#!/usr/bin/env python3
"""Numerical cross-checks of the two-loop integration and Furry modules.

NUMERICAL SANITY CHECKS, NOT PROOFS. Every statement checked here is proved in Lean, except
the necessity of the integrability criterion (see `criterion`); the scripts only replay the floating-point cross-checks that were run when the Lean modules were
written, so that they can be reproduced. Agreement to quadrature accuracy is evidence against
a transcription slip (a wrong constant, sign or power), nothing more.

Subcommands (each runs in under 5 minutes on one core, niced; none starts subprocesses):

  energy2d   The signed two-loop energy integral (QED/Integration/TwoLoopEnergyIntegral.lean,
             `integral_inv_neg_quadratic_add_pow`):
             int_{R^2} (-t^T A t + w)^{-n} dt = -(pi/(n-1)) (det A)^{-1/2} w^{1-n},  Im w < 0,
             for a non-diagonal positive definite A, n = 2, 3 and two values of w, by polar
             quadrature (mpmath, 20 digits), and once by a direct 2D quadrature. ~30 s.

  feynman    The general Feynman formula (QED/Integration/FeynmanParameterGeneral.lean,
             `prod_inv_eq_factorial_mul_integral_simplex`) for n = 3, 4 factors in the lower
             half plane, its one-variable lemma `integral_one_sub_pow_mul_inv_pow`, and the 6D
             spatial formula (QED/Integration/SpatialIntegralSix.lean,
             `integral_inv_quadForm_add_pow`): int_{R^6} (|v|^2 + w)^{-k} = pi^3/((k-1)(k-2)(k-3))
             w^{3-k} via its radial integral, plus a 2D analogue with a matrix. ~3 min.

  param      The scalar two-loop parametric representation (QED/Integration/TwoLoopParametric.lean,
             `jointEnergyFirstIntegral_prod_inv_lineDenom`) for a sunset-type graph with N = 5
             lines, loop coefficients (1,0),(1,0),(0,1),(0,1),(1,1), unit masses, eps = 0.5:
             sub-step (a) (the energy integral at fixed spatial momenta against its simplex
             form), a Wick-rotation check of the direct energy quadrature, and the full formula
             -pi^4 (N-5)! int_simplex U^{-2} (V - i eps)^{4-N} against a 5D quadrature
             (spatial radii and angle, then the Wick-rotated energies) for external momenta
             with zero spatial parts. At the first point of sub-step (a) the default grids
             differ by 1.7e-2; `--refine` repeats that point with finer grids and a Wick-rotated
             energy quadrature, which agree with the simplex form to about 1e-6 (the error is in
             the direct energy quadrature at n = 600). ~1 min, ~0.6 GB (~2 min, ~1 GB with
             --refine).

  criterion  The U^{-2} integrability criterion (QED/Integration/SymanzikIntegrability.lean,
             `integrableOn_inv_sq_symanzikU_of_criterion`; per-class statements in
             SymanzikIntegrabilityClasses.lean): the Cauchy-Binet form of U, the classical
             Newton-polytope face test, and a Monte Carlo growth test of E[min(U^-2, T)] for
             z uniform on the simplex (bounded in T iff integrable), on test examples and on the
             nine order-e^5 topologies with single photon lines, doubled photon lines, and the
             VP bubble doubled. The loop matrices here come from a BFS spanning tree, not from
             `class5LoopMatrix`; the criterion depends only on which lines are parallel. The
             Monte Carlo is the only evidence for NECESSITY of the criterion, which is not
             proved in Lean. ~15 s (`--samples` to change the Monte Carlo size).

  furry      Charge conjugation (QED/Algebra/ChargeConjugation.lean, QED/TwoLoop/FurryPair.lean):
             for the Weyl gamma matrices of QED/Algebra/Dirac.lean and C = gamma^0 gamma^2,
             C^-1 gamma^mu C = -(gamma^mu)^T, the monomial entry identity used in Lean, the
             propagator identity C S(k) C^-1 = S(-k)^T (with i eps), and the cancellation of the
             two orientations of a three-propagator trace. < 1 s.

  all        Run all of the above with default settings (~5 min in total).

Usage:
  nice -n 10 python3 scripts/numerics/two_loop_crosschecks.py <subcommand> [options]

Requires numpy and mpmath. Sources: the scratch checks run by the workers that wrote the
modules (2026-11-17), copied with the logic unchanged; only the packaging, the memory-bounded
chunking of the simplex grid in `param`, and the printed summaries are new.
"""

from __future__ import annotations

import argparse
import itertools
import math
import os
import sys
import time

# Shared machine: keep numpy's BLAS on one thread (set before numpy is imported).
for _var in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ.setdefault(_var, '1')


# ---------------------------------------------------------------------------------------------
# energy2d
# ---------------------------------------------------------------------------------------------

def run_energy2d(_args) -> bool:
    import mpmath as mp

    ok = True
    mp.mp.dps = 20
    A = [[2.0, 0.7], [0.7, 1.3]]
    det = A[0][0] * A[1][1] - A[0][1] ** 2
    print("polar quadrature, A = [[2, 0.7], [0.7, 1.3]]  (n, w, lhs, rhs, |lhs - rhs|)")
    for w in [mp.mpc(3, -0.7), mp.mpc(-2, -0.3)]:
        for n in [2, 3]:
            # polar in t-space directly: t = r(cos th, sin th); q = r^2 * Q(th)
            def inner(th, n=n, w=w):
                Q = (A[0][0] * mp.cos(th) ** 2 + 2 * A[0][1] * mp.cos(th) * mp.sin(th)
                     + A[1][1] * mp.sin(th) ** 2)
                return mp.quad(lambda r: r / (-Q * r ** 2 + w) ** n, [0, 1, 10, mp.inf])
            lhs = mp.quad(inner, [0, mp.pi / 2, mp.pi, 3 * mp.pi / 2, 2 * mp.pi])
            rhs = -(mp.pi / (n - 1)) / mp.sqrt(det) * w ** (1 - n)
            err = abs(lhs - rhs)
            print(" ", n, w, mp.nstr(lhs, 15), mp.nstr(rhs, 15), mp.nstr(err, 3))
            ok &= err < 1e-10 * abs(rhs)
    # direct 2D quadrature (check2.py)
    mp.mp.dps = 15
    w = mp.mpc(3, -0.7)
    n = 3
    f = lambda x, y: 1 / (-(A[0][0] * x * x + 2 * A[0][1] * x * y + A[1][1] * y * y) + w) ** n
    pts = [-mp.inf, -3, -1, 0, 1, 3, mp.inf]
    lhs = mp.quad(f, pts, pts)
    rhs = -(mp.pi / (n - 1)) / mp.sqrt(det) * w ** (1 - n)
    print("direct 2D quadrature, n = 3, w = 3 - 0.7i:", mp.nstr(lhs, 12), "formula", mp.nstr(rhs, 12))
    ok &= abs(lhs - rhs) < 1e-6 * abs(rhs)
    return ok


# ---------------------------------------------------------------------------------------------
# feynman
# ---------------------------------------------------------------------------------------------

def run_feynman(_args) -> bool:
    import mpmath as mp

    ok = True

    def agree(name, lhs, rhs, rel=1e-10):
        nonlocal ok
        err = abs(lhs - rhs)
        good = err <= rel * abs(rhs)
        ok &= good
        print(f"  {name}: lhs {mp.nstr(lhs, 15)}  rhs {mp.nstr(rhs, 15)}  |diff| {mp.nstr(err, 3)}"
              f"  {'ok' if good else 'MISMATCH'}")

    mp.mp.dps = 20
    print("Feynman formula prod a_i^-1 = m! int_simplex (sum x_i a_i)^-(m+1):")
    # n = 3 factors on the simplex {x0, x1 >= 0, x0 + x1 <= 1}, x2 = 1 - x0 - x1
    a = [mp.mpc(1.3, -0.4), mp.mpc(-0.7, -1.1), mp.mpc(2.0, -0.2)]
    comb = lambda x0, x1: x0 * a[0] + x1 * a[1] + (1 - x0 - x1) * a[2]
    I3 = mp.quad(lambda x0: mp.quad(lambda x1: comb(x0, x1) ** -3, [0, 1 - x0]), [0, 1])
    agree("n=3", 1 / (a[0] * a[1] * a[2]), 2 * I3)
    b = a + [mp.mpc(0.5, -0.9)]
    comb4 = lambda x0, x1, x2: x0 * b[0] + x1 * b[1] + x2 * b[2] + (1 - x0 - x1 - x2) * b[3]
    I4 = mp.quad(lambda x0: mp.quad(lambda x1: mp.quad(lambda x2: comb4(x0, x1, x2) ** -4,
                                                       [0, 1 - x0 - x1]), [0, 1 - x0]), [0, 1])
    agree("n=4", 1 / (b[0] * b[1] * b[2] * b[3]), 6 * I4)
    print("one-variable lemma int_0^1 (1-t)^m (t c + (1-t) L)^-(m+2) dt = 1/((m+1) c L^(m+1)):")
    L, c, m = mp.mpc(0.3, -1.2), mp.mpc(-2, -0.1), 3
    agree("m=3", mp.quad(lambda t: (1 - t) ** m * (t * c + (1 - t) * L) ** -(m + 2), [0, 1]),
          1 / ((m + 1) * c * L ** (m + 1)))
    print("6D radial: pi^3 int_0^inf r^5 (r^2+w)^-k dr = pi^3/((k-1)(k-2)(k-3)) w^(3-k)"
          " = pi^3 Gamma(k-3)/Gamma(k) w^(3-k):")
    for w in [mp.mpc(0.7, -0.3), mp.mpc(-1.5, -0.2), mp.mpf(2.0)]:
        for k in [4, 5, 7]:
            rad = mp.pi ** 3 * mp.quad(lambda r: r ** 5 * (r ** 2 + w) ** -k, [0, 1, mp.inf])
            f1 = mp.pi ** 3 / ((k - 1) * (k - 2) * (k - 3)) * w ** (3 - k)
            f2 = mp.pi ** 3 * mp.gamma(k - 3) / mp.gamma(k) * w ** (3 - k)
            agree(f"w={mp.nstr(w, 3)}, k={k}", rad, f1)
            ok &= abs(f1 - f2) <= 1e-15 * abs(f1)
    print("  surface factor 6 vol(B^6) = 6 pi^3/Gamma(4) vs pi^3:",
          mp.nstr(6 * mp.pi ** 3 / mp.gamma(4), 15), mp.nstr(mp.pi ** 3, 15))
    print("2D analogue with a matrix: int_R2 (x^T A x + w)^-k = pi/(k-1) det^-1/2 w^(1-k):")
    A = mp.matrix([[2, 0.5], [0.5, 1]])
    w = mp.mpc(0.4, -0.6)
    k = 5
    f = lambda x, y: (A[0, 0] * x * x + 2 * A[0, 1] * x * y + A[1, 1] * y * y + w) ** -k
    I2 = mp.quad(f, [-mp.inf, 0, mp.inf], [-mp.inf, 0, mp.inf])
    agree("k=5", I2, mp.pi / (k - 1) / mp.sqrt(mp.det(A)) * w ** (1 - k), rel=1e-6)
    return ok


# ---------------------------------------------------------------------------------------------
# param
# ---------------------------------------------------------------------------------------------

def run_param(args) -> bool:
    import numpy as np
    from numpy.polynomial.legendre import leggauss

    eps = 0.5
    alpha = np.array([[1, 0], [1, 0], [0, 1], [0, 1], [1, 1]], float)
    N = len(alpha)
    Mass = np.ones(N)
    G = np.diag([-1., 1, 1, 1])

    def mdot(a, b):
        return np.einsum('...m,mn,...n->...', a, G, b)

    def simplex_nodes(n1, n2, chunk=2000):
        """Nodes/weights on the 4-simplex via class sums (Za, Zb, Zc) and splits u, w.

        z = (Za u, Za(1-u), Zb w, Zb(1-w), Zc); dx1..dx4 = Za Zb dZa dZb du dw. The triangle
        (Za, Zb, Zc) is split at its centroid, with a Duffy map at each original vertex.
        Yields (z, wt) in chunks of `chunk` triangle points (to bound memory).
        """
        g1, w1 = leggauss(n1)
        g1 = (g1 + 1) / 2
        w1 = w1 / 2
        g2, w2 = leggauss(n2)
        g2 = (g2 + 1) / 2
        w2 = w2 / 2
        V = np.eye(3)
        C = np.ones(3) / 3
        pts = []
        wts = []
        for k in range(3):
            # two subtriangles with vertex V[k]: (V[k], C, V[k+1]) and (V[k], C, V[k+2])
            for j in [(k + 1) % 3, (k + 2) % 3]:
                P0, P1, P2 = V[k], C, V[j]
                d1 = (P1 - P0)[:2]
                d2 = (P2 - P0)[:2]
                area2 = abs(d1[0] * d2[1] - d1[1] * d2[0])  # in (Za, Zb) coordinates
                for s, ws in zip(g1, w1):
                    for tau, wt in zip(g1, w1):
                        P = P0 + s * ((1 - tau) * (P1 - P0) + tau * (P2 - P0))
                        pts.append(P)
                        wts.append(ws * wt * s * area2 / 2)  # each subtriangle is visited twice
        pts = np.array(pts)
        wts = np.array(wts)
        U_, W_ = np.meshgrid(g2, g2, indexing='ij')
        WW = np.outer(w2, w2)
        for i0 in range(0, len(pts), chunk):
            P = pts[i0:i0 + chunk]
            Za = P[:, 0][:, None, None]
            Zb = P[:, 1][:, None, None]
            Zc = P[:, 2][:, None, None]
            z = np.stack([Za * U_, Za * (1 - U_), Zb * W_, Zb * (1 - W_), Zc * np.ones_like(U_)],
                         -1).reshape(-1, 5)
            wt = (wts[i0:i0 + chunk][:, None, None] * WW * Za * Zb).reshape(-1)
            yield z, wt

    def param_data(z, p):
        A = np.einsum('ki,is,it->kst', z, alpha, alpha)
        U = A[:, 0, 0] * A[:, 1, 1] - A[:, 0, 1] ** 2
        Ainv = np.stack([np.stack([A[:, 1, 1], -A[:, 0, 1]], -1),
                         np.stack([-A[:, 1, 0], A[:, 0, 0]], -1)], -2) / U[:, None, None]
        B = np.einsum('ki,is,im->ksm', z, alpha, p)  # 4-vectors B_s
        V = z @ (Mass ** 2 + mdot(p, p)) - np.einsum('kst,ksm,mn,ktn->k', Ainv, B, G, B)
        sig = np.einsum('kst,ktm->ksm', Ainv, B[:, :, 1:])  # spatial shift sigma_s
        return A, U, V, sig

    def F_direct(v, p, n=600):
        g, w = leggauss(n)
        s = 3.0
        t = s * g / (1 - g ** 2)
        jt = s * (1 + g ** 2) / (1 - g ** 2) ** 2
        T1, T2 = np.meshgrid(t, t, indexing='ij')
        W = np.outer(w * jt, w * jt)
        prod = np.ones_like(T1, dtype=complex)
        for i in range(N):
            k0 = alpha[i, 0] * T1 + alpha[i, 1] * T2 + p[i, 0]
            kv = alpha[i, 0] * v[0] + alpha[i, 1] * v[1] + p[i, 1:]
            D = -k0 ** 2 + kv @ kv + Mass[i] ** 2 - 1j * eps
            prod /= D
        return (prod * W).sum()

    def F_wick(v, p, n=120):
        # Wick rotation t = i tau (no pole crossing: |p0| < masses); dt = -dtau
        g, w = leggauss(n)
        s = 1.0 + np.abs(v).sum()
        t = s * g / (1 - g ** 2)
        jt = s * (1 + g ** 2) / (1 - g ** 2) ** 2
        T1, T2 = np.meshgrid(t, t, indexing='ij')
        W = np.outer(w * jt, w * jt)
        prod = np.ones_like(T1, dtype=complex)
        for i in range(N):
            k0 = 1j * (alpha[i, 0] * T1 + alpha[i, 1] * T2) + p[i, 0]
            kv = alpha[i, 0] * v[0] + alpha[i, 1] * v[1] + p[i, 1:]
            prod /= (-k0 ** 2 + kv @ kv + Mass[i] ** 2 - 1j * eps)
        return -(prod * W).sum()

    def F_param(v, p, n1, n2):
        tot = 0
        for z, wt in simplex_nodes(n1, n2):
            A, U, V, sig = param_data(z, p)
            y = v[None, :, :] + sig
            q = np.einsum('kst,ksc,ktc->k', A, y, y)
            wv = q + V - 1j * eps
            tot += np.sum(wt * U ** -0.5 * wv ** (1 - N))
        return math.factorial(N - 1) * (-math.pi / (N - 1)) * tot

    ok = True
    rng = np.random.default_rng(1)
    p = rng.normal(size=(N, 4)) * 0.6
    vol = sum(wt.sum() for _, wt in simplex_nodes(40, 24))
    print("simplex volume check", vol, 1 / 24)
    print("sub-step (a): energy integral at fixed v, direct quadrature vs simplex form")
    for trial in range(3):
        v = rng.normal(size=(2, 3))
        d, q = F_direct(v, p), F_param(v, p, 40, 24)
        print("  direct", d, " param", q, f" rel diff {abs(d - q) / abs(d):.1e}")
        ok &= abs(d - q) < 2e-2 * abs(d)
    print("Wick rotation vs direct energy quadrature")
    for trial in range(2):
        v = rng.normal(size=(2, 3)) * 0.7
        pp = np.c_[p[:, 0] * 0.5, p[:, 1:]]
        a, d = F_wick(v, pp, 200), F_direct(v, pp)
        print("  wick", a, " direct", d, f" rel diff {abs(a - d) / abs(d):.1e}")
        ok &= abs(a - d) < 1e-6 * abs(d)
    # full formula, external data with zero spatial parts, so the 6D integral reduces to 3D
    pt = np.zeros((N, 4))
    pt[:, 0] = [0.3, -0.2, 0.5, 0.1, -0.4]
    rhs = 0
    for z, wt in simplex_nodes(40, 24):
        A, U, V, sig = param_data(z, pt)
        rhs += np.sum(wt * U ** -2 * (V - 1j * eps) ** (4 - N))
    rhs *= -math.pi ** 4 * math.factorial(N - 5)
    print("full formula: RHS = -pi^4 (N-5)! int U^-2 (V - i eps)^(4-N) =", rhs)

    # LHS = 8 pi^2 int r1^2 r2^2 dr1 dr2 dc F(v)
    def lhs(nr=24, nc=12, nt=300):
        g, w = leggauss(nr)
        s = 1.5
        r = s * (1 + g) / (1 - g)
        jr = 2 * s / (1 - g) ** 2
        gc, wc = leggauss(nc)
        tot = 0
        for r1, w1 in zip(r, w * jr):
            for r2, w2 in zip(r, w * jr):
                for c, w3 in zip(gc, wc):
                    v = np.array([[r1, 0, 0], [r2 * c, r2 * math.sqrt(1 - c * c), 0]])
                    tot += w1 * w2 * w3 * r1 ** 2 * r2 ** 2 * F_wick(v, pt, nt)
        return 8 * math.pi ** 2 * tot

    grids = [(12, 6, 80), (16, 8, 100), (24, 10, 120)]
    last = None
    for nr, nc, nt in grids:
        last = lhs(nr, nc, nt)
        print(f"  LHS (5D quadrature, grid {nr},{nc},{nt}) =", last,
              f" rel diff {abs(last - rhs) / abs(rhs):.1e}")
    ok &= abs(last - rhs) < 2e-3 * abs(rhs)

    if args.refine:
        print("refinement of sub-step (a) at the first point (check_a)")
        rng = np.random.default_rng(1)
        p = rng.normal(size=(N, 4)) * 0.6
        v = rng.normal(size=(2, 3))
        for n1, n2 in [(40, 24), (60, 32)]:
            print("  param", n1, n2, F_param(v, p, n1, n2), flush=True)
        for n in [600, 1200]:
            print("  direct", n, F_direct(v, p, n), flush=True)
        print("  max |p0|", np.abs(p[:, 0]).max(), " wick", F_wick(v, p, 300))
    return ok


# ---------------------------------------------------------------------------------------------
# criterion
# ---------------------------------------------------------------------------------------------

def run_criterion(args) -> bool:
    """Numerical check of the U^{-2} integrability criterion on the simplex.

    U(z) = det(sum_i z_i a_i a_i^T) = sum_{i<j} z_i z_j det(a_i, a_j)^2 (Cauchy-Binet, 2x2).
    Criterion: for every i, #{j : det(a_i, a_j) != 0} >= 3 (the complement of each direction
    class has >= 3 lines). Independent checks:
      (1) Cauchy-Binet at random points;
      (2) Newton-polytope face test: for every proper subset S, |S| > 2 ord_S(U), where
          ord_S(U) is the minimal S-degree of a monomial of U (the classical convergence test);
      (3) Monte Carlo growth of the truncated mean E[min(U^-2, T)] (z uniform on the simplex):
          bounded in T iff integrable (log growth for the failing cases).
    """
    import numpy as np

    rng = np.random.default_rng(12345)
    samples = args.samples

    def dets(a):
        a = np.asarray(a, float)
        return np.outer(a[:, 0], a[:, 1]) - np.outer(a[:, 1], a[:, 0])

    def criterion(a):
        d = dets(a)
        return all(np.count_nonzero(np.abs(d[i]) > 1e-12) >= 3 for i in range(len(a)))

    def classes(a):
        d = dets(a)
        n = len(a)
        seen, out = set(), []
        for i in range(n):
            if i in seen:
                continue
            c = [j for j in range(n) if abs(d[i, j]) < 1e-12]
            seen |= set(c)
            out.append(c)
        return out

    def newton_test(a):
        d = dets(a)
        n = len(a)
        mons = [(i, j) for i in range(n) for j in range(i + 1, n) if abs(d[i, j]) > 1e-12]
        for r in range(1, n):
            for S in itertools.combinations(range(n), r):
                S = set(S)
                ordS = min((i in S) + (j in S) for i, j in mons)
                if not len(S) > 2 * ordS:
                    return False, sorted(S), ordS
        return True, None, None

    def cauchy_binet_check(a, trials=5):
        a = np.asarray(a, float)
        d = dets(a)
        err = 0
        for _ in range(trials):
            z = rng.random(len(a))
            A = (a.T * z) @ a
            lhs = np.linalg.det(A)
            rhs = sum(z[i] * z[j] * d[i, j] ** 2 for i in range(len(a))
                      for j in range(i + 1, len(a)))
            err = max(err, abs(lhs - rhs))
        return err

    def mc_truncated(a, Ts=(1e2, 1e4, 1e6, 1e8), chunk=500_000):
        a = np.asarray(a, float)
        d2 = dets(a) ** 2
        sums = np.zeros(len(Ts))
        done = 0
        while done < samples:
            k = min(chunk, samples - done)
            z = rng.dirichlet(np.ones(len(a)), size=k)
            U = np.einsum('ki,ij,kj->k', z, d2, z) / 2
            inv2 = 1.0 / np.maximum(U, 1e-300) ** 2
            sums += [float(np.sum(np.minimum(inv2, T))) for T in Ts]
            done += k
        return list(sums / samples)

    def alpha_from_graph(edges):
        """Loop matrix of a connected graph with cyclomatic number 2 (BFS spanning tree)."""
        verts = sorted({v for e in edges for v in e})
        parent = {verts[0]: None}
        order = [verts[0]]
        tree = set()
        for u in order:
            for k, (x, y) in enumerate(edges):
                for p, q in ((x, y), (y, x)):
                    if p == u and q not in parent:
                        parent[q] = (u, k)
                        tree.add(k)
                        order.append(q)
        chords = [k for k in range(len(edges)) if k not in tree]
        assert len(chords) == 2, chords

        def path_to_root(v):
            out = []
            while parent[v] is not None:
                u, k = parent[v]
                out.append((k, u, v))  # tree edge k traversed u -> v (root to v)
                v = u
            return out

        alpha = np.zeros((len(edges), 2), int)
        for s, c in enumerate(chords):
            x, y = edges[c]
            alpha[c, s] = 1  # traverse chord x -> y, then tree path y -> root -> x
            for k, u, v in path_to_root(y):  # root->y edges traversed backwards (v -> u)
                alpha[k, s] += 1 if edges[k] == (v, u) else -1
            for k, u, v in path_to_root(x):  # root->x edges traversed forwards (u -> v)
                alpha[k, s] += 1 if edges[k] == (u, v) else -1
        return alpha, chords

    def open_line(vs):
        return [(vs[i], vs[i + 1]) for i in range(len(vs) - 1)]

    def loop(vs):
        return [(vs[i], vs[(i + 1) % len(vs)]) for i in range(len(vs))]

    # order-e^5 classes: internal lines (directed u -> v for fermions, photons as listed)
    CLASSES = {
        'L': (open_line([0, 1, 2, 3, 4]), [(0, 4), (1, 3)]),
        'X': (open_line([0, 1, 2, 3, 4]), [(0, 3), (1, 4)]),
        'Cp': (open_line([0, 1, 2, 3, 4]), [(0, 3), (2, 4)]),
        'Cm': (open_line([0, 1, 2, 3, 4]), [(0, 2), (1, 4)]),
        'Sp': (open_line([0, 1, 2, 3, 4]), [(0, 4), (2, 3)]),
        'Sm': (open_line([0, 1, 2, 3, 4]), [(0, 4), (1, 2)]),
        'VP': (open_line([0, 1, 2]) + loop([3, 4]), [(0, 3), (2, 4)]),
        'Fp': (open_line([0, 1]) + loop([2, 3, 4]), [(0, 3), (1, 4)]),
        'Fm': (open_line([0, 1]) + loop([2, 4, 3]), [(0, 3), (1, 4)]),
    }

    ok = True

    def report(name, a, mc=True):
        nonlocal ok
        a = np.asarray(a)
        cb = cauchy_binet_check(a)
        crit = criterion(a)
        nt, S, o = newton_test(a)
        cl = classes(a)
        line = (f"{name:14s} N={len(a)} classes={cl} complements={[len(a) - len(c) for c in cl]} "
                f"criterion={crit} newton={nt}" + ("" if nt else f" (S={S}, ord={o})") +
                f" CB-err={cb:.1e}")
        print(line, flush=True)
        if mc:
            vals = mc_truncated(a)
            print("   E[min(U^-2,T)], T=1e2,1e4,1e6,1e8:", " ".join(f"{v:.4g}" for v in vals),
                  flush=True)
        ok &= (crit == nt) and cb < 1e-10
        return crit

    print(f"Monte Carlo samples per case: {samples}")
    print("== test examples ==")
    report('sunset 2+2+1', [[1, 0], [1, 0], [0, 1], [0, 1], [1, 1]])
    report('sunset 2+1+1', [[1, 0], [1, 0], [0, 1], [1, 1]])
    report('sunset 3+1+1', [[1, 0], [1, 0], [1, 0], [0, 1], [1, 1]])
    report('vertex 2+2+2', [[1, 0], [1, 0], [0, 1], [0, 1], [1, 1], [1, 1]])
    report('vertex 3+2+1', [[1, 0], [1, 0], [1, 0], [0, 1], [0, 1], [1, 1]])
    report('4+1+1 (bubble)', [[1, 0], [1, 0], [1, 0], [1, 0], [0, 1], [1, 1]])
    report('random dirs N=5', rng.integers(-3, 4, size=(5, 2)), mc=False)
    expected_single = {'L': True, 'X': True, 'Cp': True, 'Cm': True, 'Sp': False, 'Sm': False,
                       'VP': False, 'Fp': True, 'Fm': True}
    print("== order-e^5 classes, photons single (6 lines) ==")
    for name, (ferm, phot) in CLASSES.items():
        a, _ = alpha_from_graph(ferm + phot)
        ok &= report(name, a) == expected_single[name]
    print("== photons doubled (PV pair as a product of two denominators) ==")
    for name, (ferm, phot) in CLASSES.items():
        a, _ = alpha_from_graph(ferm + phot)
        a = np.vstack([a, a[len(ferm):]])  # each photon line twice (same momentum)
        ok &= report(name + '+PV', a, mc=(name in ('Sp', 'VP'))) == (name != 'VP')
    print("== VP with the bubble lines doubled (divided-difference form) ==")
    ferm, phot = CLASSES['VP']
    a, _ = alpha_from_graph(ferm + phot)
    a = np.vstack([a, a[3:5]])  # bubble lines 3->4, 4->3 each twice
    ok &= report('VP bubble^2', a, mc=True)
    print("== alpha matrices (BFS tree) ==")
    for name, (ferm, phot) in CLASSES.items():
        a, _ = alpha_from_graph(ferm + phot)
        print(name, [tuple(e) for e in ferm + phot], a.tolist())
    return ok


# ---------------------------------------------------------------------------------------------
# furry
# ---------------------------------------------------------------------------------------------

def run_furry(_args) -> bool:
    import numpy as np

    I = 1j
    # Weyl gamma matrices of QED/Algebra/Dirac.lean (mostly-plus metric, {g^m, g^n} = -2 eta^mn)
    g = [np.array([[0, 0, 1, 0], [0, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, 0]]),
         np.array([[0, 0, 0, 1], [0, 0, 1, 0], [0, -1, 0, 0], [-1, 0, 0, 0]]),
         np.array([[0, 0, 0, -I], [0, 0, I, 0], [0, I, 0, 0], [-I, 0, 0, 0]]),
         np.array([[0, 0, 1, 0], [0, 0, 0, -1], [-1, 0, 0, 0], [0, 1, 0, 0]])]
    g = [x.astype(complex) for x in g]
    eta = np.diag([-1, 1, 1, 1])
    ok = True
    for m in range(4):
        for n in range(4):
            ok &= np.allclose(g[m] @ g[n] + g[n] @ g[m], -2 * eta[m, n] * np.eye(4))
    print("Clifford relation:", ok)
    C = g[0] @ g[2]
    Ci = np.linalg.inv(C)
    for m in range(4):
        a1 = np.allclose(Ci @ g[m] @ C, -g[m].T)
        a2 = np.allclose(C @ g[m] @ Ci, -g[m].T)
        print(f"mu={m}: C^-1 g C = -g^T {a1};  C g C^-1 = -g^T {a2}")
        ok &= a1 and a2
    print("C = gamma^0 gamma^2 =\n", C)
    # monomial form: C[a, p(a)] = c_a
    p = [int(np.nonzero(C[a])[0][0]) for a in range(4)]
    c = [C[a, p[a]] for a in range(4)]
    print("permutation p =", p, " entries c =", c)
    for m in range(4):
        for a in range(4):
            for b in range(4):
                ok &= abs(g[m][a, b] + c[a] / c[b] * g[m][p[b], p[a]]) < 1e-12
    print("entry identity g[a,b] = -(c_a/c_b) g[p b, p a]:", ok)
    rng = np.random.default_rng(0)

    def slash(k):
        kl = eta @ k
        return sum(kl[mu] * g[mu] for mu in range(4))

    def S(m, eps, k):
        D = k @ eta @ k + m * m - 1j * eps
        return (m * np.eye(4) - slash(k)) / D

    print("propagator S(k)[a,b] = (c_a/c_b) S(-k)[p b, p a] and S(k)^T = C^-1 S(-k) C"
          " (max errors):")
    for _ in range(5):
        k = rng.normal(size=4)
        m = rng.random()
        eps = rng.random()
        A = S(m, eps, k)
        B = S(m, eps, -k)
        err = max(abs(A[a, b] - c[a] / c[b] * B[p[b], p[a]]) for a in range(4) for b in range(4))
        e1 = np.abs(A.T - Ci @ B @ C).max()
        e2 = np.abs(A.T - C @ B @ Ci).max()
        print(f"  {err:.1e} {e1:.1e} {e2:.1e}")
        ok &= max(err, e1, e2) < 1e-12
    print("three-propagator trace: orientation + reversed orientation (should cancel):")
    for _ in range(3):
        ks = [rng.normal(size=4) for _ in range(3)]
        m = rng.random() + .5
        eps = .3
        mus = rng.integers(0, 4, size=3)
        T1 = np.trace(g[mus[0]] @ S(m, eps, ks[0]) @ g[mus[1]] @ S(m, eps, ks[1]) @ g[mus[2]]
                      @ S(m, eps, ks[2]))
        T2 = np.trace(g[mus[0]] @ S(m, eps, -ks[2]) @ g[mus[2]] @ S(m, eps, -ks[1]) @ g[mus[1]]
                      @ S(m, eps, -ks[0]))
        print(f"  T1 = {T1:.6g}, T2 = {T2:.6g}, |T1 + T2| = {abs(T1 + T2):.1e}")
        ok &= abs(T1 + T2) < 1e-12 * max(1.0, abs(T1))
    return ok


# ---------------------------------------------------------------------------------------------

COMMANDS = {
    'energy2d': run_energy2d,
    'feynman': run_feynman,
    'param': run_param,
    'criterion': run_criterion,
    'furry': run_furry,
}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument('command', choices=list(COMMANDS) + ['all'])
    ap.add_argument('--refine', action='store_true', help='param: finer grids for sub-step (a)')
    ap.add_argument('--samples', type=int, default=4_000_000,
                    help='criterion: Monte Carlo samples per case (default 4e6)')
    args = ap.parse_args()
    names = list(COMMANDS) if args.command == 'all' else [args.command]
    results = {}
    for name in names:
        print(f"=== {name} ===", flush=True)
        t0 = time.time()
        results[name] = COMMANDS[name](args)
        print(f"--- {name}: {'PASS' if results[name] else 'FAIL'} ({time.time() - t0:.0f} s)",
              flush=True)
    return 0 if all(results.values()) else 1


if __name__ == '__main__':
    sys.exit(main())
