#!/usr/bin/env python3
"""Numerical study of the positivity of the two-loop Symanzik remainder V (obligation O2-12).

For each order-e^5 vertex class (`QED.TwoLoop.Enumeration.Class5`) this script takes the integer
loop matrix `class5LoopMatrix` of `QED/Integration/SymanzikIntegrabilityClasses.lean` (rows are
the six internal lines in the order of that file's docstring, columns the coefficients of the two
loop momenta), checks that its columns are cycles of the graph of the class representative
(`QED/TwoLoop/EnumerationGauge5.lean`), routes the external momenta through the graph, and
evaluates the remainder of `QED/Integration/TwoLoopParametricAlgebra.lean`

    V(z) = sum_i z_i (M_i^2 + p_i.p_i) - sum_{s,t} (A(z)^{-1})_{st} B_s.B_t ,
    A(z)_{st} = sum_i z_i a_{is} a_{it},   B_s = sum_i z_i a_{is} p_i ,

(mostly-plus metric) on the simplex.  Kinematics: p.p = p'.p' = -m^2, q = p' - p, q.q = Q2 >= 0.
Writing P = (p + p')/2 and K = (p' - p)/2 one has P.K = 0, P.P = -m^2 - Q2/4, K.K = Q2/4, and
each line momentum is p_i = a_i P + b_i K with real a_i, b_i.  Then (exact algebra)

    V(z) = sum_i z_i M_i^2 + (P.P) R(a) + (K.K) R(b),
    R(c) = sum_i z_i c_i^2 - beta(c)^T A^{-1} beta(c),  beta(c)_s = sum_i z_i a_{is} c_i ,

the formula proved in Lean as `symanzikV_smul_add_smul` (QED/Integration/SymanzikPositivity.lean).
The script cross-checks it against a direct four-vector evaluation in a frame.

Masses: electron lines m; closed-loop lines M_f >= m (V is increasing in every M_i^2, since
dV/dM_i^2 = z_i >= 0, so the minimum over the Pauli-Villars masses is at M_f = m); photon lines
lambda >= m_gamma (likewise minimal at lambda = m_gamma, which also covers the Pauli-Villars
mass integral over mu in [m_gamma^2, Lambda^2]).

Minimization: random points (Dirichlet with concentrations 1, 0.3, 0.1, 0.03, which pile up
near the faces), points on every face (each subset of lines set to zero), then a projected
pattern search from the best points.  V is evaluated stably
near U -> 0 (the residual of a weighted least-squares problem, by Gram-Schmidt).  Points with U = 0 are excluded: V is defined there only as a limit, which depends
on the direction (V = F/U with F, U -> 0).

Usage: python3 scripts/numerics/two_loop_positivity.py [--quick]
"""

from __future__ import annotations

import itertools
import sys

import numpy as np

# Loop matrices of `class5LoopMatrix` (QED/Integration/SymanzikIntegrabilityClasses.lean).
LOOP = {
    "L": [[0, 1], [1, 0], [1, 0], [0, 1], [0, -1], [-1, 1]],
    "X": [[1, -1], [1, 0], [1, 0], [0, 1], [-1, 1], [0, -1]],
    "Cp": [[1, 1], [1, 1], [1, 0], [0, -1], [-1, -1], [0, 1]],
    "Cm": [[1, -1], [1, 0], [0, 1], [0, 1], [-1, 1], [0, -1]],
    "Sp": [[1, 1], [1, 1], [1, 0], [1, 1], [-1, -1], [0, 1]],
    "Sm": [[1, 0], [1, -1], [1, 0], [1, 0], [-1, 0], [0, 1]],
    "VP": [[0, 1], [0, 1], [1, -1], [1, 0], [0, -1], [0, 1]],
    "Fp": [[-1, 1], [0, 1], [1, 0], [0, 1], [1, -1], [-1, 1]],
    "Fm": [[-1, 1], [1, 0], [0, 1], [1, 0], [1, -1], [-1, 1]],
}

# Graph of the representative (EnumerationGauge5.lean): lines (tail, head, kind) in the order of
# the loop matrix; kind 'e' open-line electron, 'f' closed-loop fermion, 'g' photon (oriented from
# the first to the second vertex of its pair); the open line runs from `first` to `last`; the
# external photon attaches at `ext`.
def open_line_graph(photons):
    return [(0, 1, "e"), (1, 2, "e"), (2, 3, "e"), (3, 4, "e")] + [(a, b, "g") for a, b in photons]


GRAPH = {
    "L": (open_line_graph([(0, 4), (1, 3)]), 0, 4, 2),
    "X": (open_line_graph([(0, 3), (1, 4)]), 0, 4, 2),
    "Cp": (open_line_graph([(0, 3), (2, 4)]), 0, 4, 1),
    "Cm": (open_line_graph([(0, 2), (1, 4)]), 0, 4, 3),
    "Sp": (open_line_graph([(0, 4), (2, 3)]), 0, 4, 1),
    "Sm": (open_line_graph([(0, 4), (1, 2)]), 0, 4, 3),
    "VP": ([(0, 1, "e"), (1, 2, "e"), (3, 4, "f"), (4, 3, "f"), (0, 3, "g"), (2, 4, "g")], 0, 2, 1),
    "Fp": ([(0, 1, "e"), (2, 3, "f"), (3, 4, "f"), (4, 2, "f"), (0, 3, "g"), (1, 4, "g")], 0, 1, 2),
    "Fm": ([(0, 1, "e"), (2, 4, "f"), (4, 3, "f"), (3, 2, "f"), (0, 3, "g"), (1, 4, "g")], 0, 1, 2),
}


def incidence(lines):
    n = np.zeros((5, len(lines)))
    for i, (s, t, _) in enumerate(lines):
        n[t, i] += 1.0
        n[s, i] -= 1.0
    return n


def setup(name):
    """Return (alpha, a, b, kinds), after orienting the photon lines so that the loop matrix
    columns are cycles, and routing p_i = a_i P + b_i K."""
    alpha = np.array(LOOP[name], dtype=float)
    lines, first, last, ext = GRAPH[name]
    lines = list(lines)
    # orient photons: try every flip pattern of the photon lines
    gidx = [i for i, l in enumerate(lines) if l[2] == "g"]
    for flips in itertools.product([False, True], repeat=len(gidx)):
        trial = list(lines)
        for i, f in zip(gidx, flips):
            if f:
                s, t, k = trial[i]
                trial[i] = (t, s, k)
        if np.allclose(incidence(trial) @ alpha, 0):
            lines = trial
            break
    else:
        raise RuntimeError(f"{name}: loop matrix columns are not cycles")
    n = incidence(lines)
    assert np.linalg.matrix_rank(alpha) == 2
    assert np.linalg.matrix_rank(n) == 4  # connected graph on 5 vertices; cycle space dim 2
    # external inflow: p = P - K at `first`, -p' = -(P + K) at `last`, q = 2K at `ext`
    inj_a = np.zeros(5)
    inj_b = np.zeros(5)
    inj_a[first] += 1
    inj_b[first] -= 1
    inj_a[last] -= 1
    inj_b[last] -= 1
    inj_b[ext] += 2
    a = np.linalg.lstsq(n, -inj_a, rcond=None)[0]
    b = np.linalg.lstsq(n, -inj_b, rcond=None)[0]
    assert np.allclose(n @ a, -inj_a) and np.allclose(n @ b, -inj_b)
    kinds = [l[2] for l in lines]
    return alpha, a, b, kinds


def masses_sq(kinds, m, mg):
    return np.array([mg**2 if k == "g" else m**2 for k in kinds])


def symanzik(alpha, z):
    """A(z), U(z), adj A(z) for a batch z of shape (n, 6)."""
    a00 = z @ (alpha[:, 0] ** 2)
    a11 = z @ (alpha[:, 1] ** 2)
    a01 = z @ (alpha[:, 0] * alpha[:, 1])
    u = a00 * a11 - a01**2
    return a00, a11, a01, u


def remainder_gs(alpha, z, c):
    """R(c) = min_y sum_i z_i (alpha_i.y + c_i)^2, the weighted least-squares residual, by
    modified Gram-Schmidt with reorthogonalization on the columns sqrt(z) alpha_s.  This is
    numerically stable near U -> 0, unlike U R = U sum z c^2 - beta^T adj(A) beta, whose
    cancellation error O(eps) is divided by U."""
    w = np.sqrt(np.maximum(z, 0))
    u1 = w * alpha[:, 0]
    u2 = w * alpha[:, 1]
    t = w * c
    n1 = np.linalg.norm(u1, axis=1, keepdims=True)
    swap = (n1[:, 0] == 0)
    u1[swap], u2[swap] = u2[swap].copy(), u1[swap].copy()
    n1 = np.linalg.norm(u1, axis=1, keepdims=True)
    q1 = u1 / np.where(n1 > 0, n1, 1)
    for _ in range(2):
        u2 = u2 - np.sum(q1 * u2, axis=1, keepdims=True) * q1
    n2 = np.linalg.norm(u2, axis=1, keepdims=True)
    q2 = u2 / np.where(n2 > 0, n2, 1)
    for _ in range(2):
        t = t - np.sum(q1 * t, axis=1, keepdims=True) * q1
        t = t - np.sum(q2 * t, axis=1, keepdims=True) * q2
    return np.sum(t * t, axis=1)


def v_parts(alpha, a, b, msq, z):
    """Return U, sum z M^2, R(a), R(b)."""
    _, _, _, u = symanzik(alpha, z)
    return u, z @ msq, remainder_gs(alpha, z, a), remainder_gs(alpha, z, b)


def v_value(alpha, a, b, msq, z, m, q2):
    """V = sum z M^2 + (P.P) R(a) + (K.K) R(b); returns (V, U, F = U V)."""
    u, zm, ra, rb = v_parts(alpha, a, b, msq, z)
    v = zm + (-m**2 - q2 / 4) * ra + (q2 / 4) * rb
    return v, u, u * v


def direct_check(alpha, a, b, kinds, m, mg, q2, rng):
    """Direct four-vector evaluation of V in the Breit frame, compared with the formula."""
    # Breit frame: P = (E, 0, 0, 0), K = (0, 0, 0, k), k^2 = q2/4, E^2 = m^2 + q2/4
    kk = np.sqrt(q2) / 2
    E = np.sqrt(m**2 + q2 / 4)
    P = np.array([E, 0, 0, 0.0])
    K = np.array([0, 0, 0, kk])
    eta = np.diag([-1.0, 1, 1, 1])
    p = np.outer(a, P) + np.outer(b, K)
    # sanity: on shell
    pin, pout = P - K, P + K
    assert abs(pin @ eta @ pin + m**2) < 1e-9 and abs(pout @ eta @ pout + m**2) < 1e-9
    msq = masses_sq(kinds, m, mg)
    for _ in range(20):
        z = rng.dirichlet(np.ones(6))
        A = np.einsum("i,is,it->st", z, alpha, alpha)
        B = np.einsum("i,is,im->sm", z, alpha, p)
        V = np.sum(z * (msq + np.einsum("im,mn,in->i", p, eta, p))) - np.einsum(
            "st,sm,mn,tn->", np.linalg.inv(A), B, eta, B)
        Vf = v_value(alpha, a, b, msq, z[None, :], m, q2)[0][0]
        assert abs(V - Vf) < 1e-9 * max(1, abs(V)), (V, Vf)


def sample_points(rng, n):
    pts = [rng.dirichlet(np.full(6, c), size=n) for c in (1.0, 0.3, 0.1, 0.03)]
    # faces: for each nonempty proper support, random points supported there
    for k in range(1, 6):
        for supp in itertools.combinations(range(6), k):
            w = np.zeros((max(n // 50, 20), 6))
            w[:, supp] = rng.dirichlet(np.ones(k), size=w.shape[0])
            pts.append(w)
    return np.vstack(pts)


def project_simplex(v):
    """Euclidean projection of rows of v onto the probability simplex."""
    n, d = v.shape
    u = -np.sort(-v, axis=1)
    css = np.cumsum(u, axis=1) - 1
    ind = np.arange(1, d + 1)
    cond = u - css / ind > 0
    rho = d - 1 - np.argmax(cond[:, ::-1], axis=1)
    theta = css[np.arange(n), rho] / (rho + 1)
    return np.maximum(v - theta[:, None], 0)


def local_min(fun, z0, rng, iters=400):
    """Projected random pattern search on the simplex from the rows of z0."""
    z = z0.copy()
    fz = fun(z)
    step = np.full(z.shape[0], 0.05)
    for _ in range(iters):
        cand = project_simplex(z + step[:, None] * rng.standard_normal(z.shape))
        fc = fun(cand)
        better = fc < fz
        z[better] = cand[better]
        fz[better] = fc[better]
        step = np.where(better, step * 1.3, step * 0.85)
        step = np.clip(step, 1e-7, 0.3)
    return z, fz


def study(name, m, mg, q2_list, rng, n):
    alpha, a, b, kinds = setup(name)
    for q2 in (0.0, 0.5):
        direct_check(alpha, a, b, kinds, m, mg, q2 if q2 > 0 else 1e-12, rng)
    msq = masses_sq(kinds, m, mg)
    pts = sample_points(rng, n)
    _, u, _ = v_value(alpha, a, b, msq, pts, m, 0.0)
    pts = pts[u > 1e-14]
    out = []
    for q2 in q2_list:
        def fun(z, q2=q2):
            v, u, _ = v_value(alpha, a, b, msq, z, m, q2)
            return np.where(u > 1e-14, v, np.inf)
        vals = fun(pts)
        order = np.argsort(vals)[:40]
        zbest, fbest = local_min(fun, pts[order], rng)
        k = int(np.argmin(fbest))
        out.append((q2, float(min(fbest[k], vals[order[0]])), zbest[k]))
    # the q^2-slope R(b) - R(a): V = V0 + (q^2/4) (R(b) - R(a))
    def slope(z):
        u, _, ra, rb = v_parts(alpha, a, b, msq, z)
        return np.where(u > 1e-14, rb - ra, np.inf)
    sv = slope(pts)
    order = np.argsort(sv)[:40]
    zs, fs = local_min(slope, pts[order], rng)
    ks = int(np.argmin(fs))
    return alpha, a, b, kinds, out, (float(fs[ks]), zs[ks])


def face_study(name, m, mg, rng):
    """Behaviour of V near faces where U -> 0: approach each U = 0 face point along random
    directions into the interior and record V and U at distance t."""
    alpha, a, b, kinds = setup(name)
    msq = masses_sq(kinds, m, mg)
    rows = []
    for k in range(1, 6):
        for supp in itertools.combinations(range(6), k):
            w = np.zeros((200, 6))
            w[:, supp] = rng.dirichlet(np.ones(k), size=200)
            _, u, _ = v_value(alpha, a, b, msq, w, m, 0.0)
            w = w[u < 1e-15]
            if len(w) == 0:
                continue
            vmin = np.inf
            for t in (1e-2, 1e-4, 1e-6):
                d = rng.dirichlet(np.ones(6), size=len(w))
                zz = (1 - t) * w + t * d
                v, uu, f = v_value(alpha, a, b, msq, zz, m, 0.0)
                vmin = min(vmin, float(np.min(v)))
            rows.append((supp, vmin))
    return rows


def lower_bound(name, z, m, mg, q2):
    """The analytic lower bounds proved in Lean (`le_symanzikV_classL`, `le_symanzikV_classX`,
    QED/Integration/SymanzikPositivity.lean) at the point z; they hold for every q2 >= 0."""
    E = z[:4].sum()
    if name == "L":
        return m**2 * E**2 + mg**2 * (1 - E)
    if name == "X":
        return m**2 * E**2 / 4 + mg**2 * (1 - E)
    return None


def main():
    quick = "--quick" in sys.argv
    rng = np.random.default_rng(20261117)
    n = 4000 if quick else 40000
    q2_list = [0.0, 0.01, 0.1, 0.5, 1.0, 4.0, 25.0, 400.0]
    m = 1.0
    for mg in (1e-3, 0.1, 1.0, 3.0):
        print(f"=== m = {m}, m_gamma = {mg} (closed-loop masses M_f = m, photons lambda = m_gamma)")
        print("class  " + "  ".join(f"q2={q2:<7g}" for q2 in q2_list) + "   min dV/dq2*4   at z")
        for name in LOOP:
            alpha, a, b, kinds, out, (smin, zs) = study(name, m, mg, q2_list, rng, n)
            row = "  ".join(f"{v:<10.5g}" for _, v, _ in out)
            print(f"{name:<6} {row}   {smin:< .4g}  {np.round(zs, 3)}")
            if mg in (0.1,) and name in ("L", "X"):
                for q2, v, z in out:
                    lb = lower_bound(name, z, m, mg, q2)
                    print(f"       q2={q2:g}: min V = {v:.6g} at z = {np.round(z, 4)}; "
                          f"Lean lower bound there = {lb:.6g}")
        print()
    # the routing used in Lean, p_i = (p, p, p', p', 0, 0), i.e. a = (1,1,1,1,0,0),
    # b = (-1,-1,1,1,0,0), gives the same V as the routing of `setup` (V is routing invariant)
    for name in ("L", "X"):
        alpha, a, b, kinds = setup(name)
        al = np.array([1, 1, 1, 1, 0, 0.0])
        bl = np.array([-1, -1, 1, 1, 0, 0.0])
        msq = masses_sq(kinds, m, 0.1)
        pts = rng.dirichlet(np.ones(6), size=1000)
        d = np.max(np.abs(v_value(alpha, a, b, msq, pts, m, 0.7)[0]
                          - v_value(alpha, al, bl, msq, pts, m, 0.7)[0]))
        print(f"routing invariance {name}: max |V(setup) - V(Lean routing)| = {d:.2g}")
    # the analytic bound must hold everywhere: check on random points
    for name in ("L", "X"):
        alpha, a, b, kinds = setup(name)
        for mg in (1e-3, 0.1, 1.0, 3.0):
            msq = masses_sq(kinds, m, mg)
            pts = sample_points(rng, n)
            for q2 in (0.0, 0.1, 1.0, 25.0):
                v, u, _ = v_value(alpha, a, b, msq, pts, m, q2)
                ok = u > 1e-12
                lb = np.array([lower_bound(name, z, m, mg, q2) for z in pts[ok]])
                gap = float(np.min(v[ok] - lb))
                print(f"bound check {name} m_gamma={mg} q2={q2}: min(V - bound) = {gap:.3g}")
    print()
    print("Faces with U = 0 (approached from the interior), q2 = 0, m_gamma = 0.1:")
    for name in LOOP:
        rows = face_study(name, m, 0.1, rng)
        worst = min(rows, key=lambda r: r[1])
        print(f"{name:<4} {len(rows)} faces with U = 0; smallest V seen nearby = {worst[1]:.4g} "
              f"(face support {worst[0]})")
    print()
    print("Routings p_i = a_i P + b_i K (photon lines oriented so that the loop matrix is a cycle basis):")
    for name in LOOP:
        alpha, a, b, kinds = setup(name)
        print(f"{name:<4} a = {np.round(a, 3)}  b = {np.round(b, 3)}  kinds = {''.join(kinds)}")


if __name__ == "__main__":
    main()
