#!/usr/bin/env python3
"""Numerical sanity checks of the route-A two-loop subtraction units. NOT a proof.

Companion of docs/TWO-LOOP-DERIVATION.md, section 11. It evaluates, at finite regulators
(photon mass m_gamma, Pauli-Villars photon mass Lambda, Pauli-Villars regulator fermions
M_1, M_2 for the vacuum polarization), the contribution of each subtraction unit of
section 5.2 to the coefficient of r^2 = (alpha/pi)^2 in F_2 at q -> 0, and compares the
limits with Barbieri-Mignaco-Remiddi I, p. 852. These are floating-point checks; every
statement they support remains a proof obligation.

Units (section 5.2; order-e^2 counterterms fixed by the on-shell conditions):
  VP = VP graph (flavour sum f = 0, 1, 2) + delta_3 insertion, with Pi(0) = 0
  S  = S+ + S- + their (delta_2, delta_m) insertions
  C  = C+ + C- + delta_1 at their internal vertices          = C+ + C- + 2 delta_1 F2^(2)
  L  = ladder + delta_1 at the external vertex               = L + delta_1 F2^(2)
  X  = crossed ladder
delta_1 is fixed by the charge condition F_1(0) = 1 of the one-loop 1PI vertex; the
script checks the Ward identity delta_1 = delta_2 numerically.

Method (conventions: metric (+,-,-,-), m = 1, Feynman gauge, vertex -i e gamma^mu,
electron i(k+m)/(k^2-m^2), photon -i g/(k^2-lambda^2); every Pauli-Villars photon is the
difference lambda = m_gamma minus lambda = Lambda):
  * Covariant Feynman-parametric representation of each graph (U, its inverse, the shift
    coefficients A_i of section 4.4, the contraction rule l l -> -g (U^-1) Delta/(2(n-5))).
    This checks the parametric (covariant) values, not the energy-first prescription.
  * F_2 at q -> 0 from the exact two-structure projector applied to the vertex expanded to
    first order in q (the O(q^2) part of the vertex is annihilated exactly at q = 0). The
    Dirac traces of every numerator pattern are computed numerically once, with exact
    polynomial fits in q^2.
  * Lines with equal loop routing and equal mass are merged; the integrand is affine in the
    split, so the split integral is the value at the centroid times the group volume.
  * Quadrature: primary sector decomposition with sigmoidal Gauss-Legendre maps; for L and C
    the simplex is nested around the UV-divergent subgraph, with a log grid in its scale.
  * S in insertion form: the on-shell renormalized PV self-energy Sigma_R is written as a
    superposition over (x, mu) of terms (alpha k + beta)(k-m)^2/(M^2-k^2); with the two
    adjacent propagators it becomes a heavy line of mass M, so the S unit is an outer
    one-loop vertex integrated over (x, mu). The script checks that this equals the bare
    two-loop S+ graph plus its counterterm graphs at moderate regulators.
  * VP: Pi_R k^2 D^2 with the spectral form of Pi_R (section 5.3, O2-18), exact partial
    fractions in k^2 and the one-loop F_2 of a massive photon and its derivative (mpmath).

Run (from any directory; at most --procs worker processes, default and maximum 4):
  OMP_NUM_THREADS=1 nice -n 10 python3 scripts/numerics/two_loop_units.py checks  # ~3 min, 1 core
  OMP_NUM_THREADS=1 nice -n 10 python3 scripts/numerics/two_loop_units.py uv      # ~20 min, 4 cores
  OMP_NUM_THREADS=1 nice -n 10 python3 scripts/numerics/two_loop_units.py ir      # ~25 min, 4 cores
  OMP_NUM_THREADS=1 nice -n 10 python3 scripts/numerics/two_loop_units.py vp      # ~3 min, 1 core
  python3 scripts/numerics/two_loop_units.py fit two_loop_units_ir.jsonl          # table + IR fits
uv: m_gamma = 1e-2, Lambda = 10..1000 (other points with --points "mg,Lam;mg,Lam").
ir: Lambda = 1000, m_gamma = 1e-2..1e-5. Both write JSON lines to --out (default
two_loop_units_<mode>.jsonl in the current directory), two quadrature levels per graph; the
quoted error of a unit is |fine - coarse|. Memory stays below about 0.3 GB per worker.
Requires numpy and mpmath (run 2026-11-17 with numpy 2.5.3, mpmath 1.3.0).

Results of the 2026-11-17 run are recorded in docs/TWO-LOOP-DERIVATION.md, section 11.
"""
import argparse, itertools, json, math, sys, time
import numpy as np
import mpmath as mp

# =============================================================== Dirac algebra, projector
I2 = np.eye(2); Z2 = np.zeros((2, 2))
_sig = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]]),
        np.array([[1, 0], [0, -1]], complex)]
GAM = [np.block([[I2, Z2], [Z2, -I2]]).astype(complex)] + \
      [np.block([[Z2, s], [-s, Z2]]) for s in _sig]
ETA = np.array([1., -1, -1, -1])
ID4 = np.eye(4, dtype=complex)


def slash(v):
    return sum(GAM[m] * ETA[m] * v[m] for m in range(4))


def kin(t):
    """on-shell p, q (m = 1) with q^2 = -t."""
    p = np.array([1., 0, 0, 0])
    q = np.array([t / 2, math.sqrt(t + t * t / 4), 0, 0])
    return p, q


def matchings(items):
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for m in matchings(rest):
        yield m
    for i, x in enumerate(rest):
        for m in matchings(rest[:i] + rest[i + 1:]):
            yield [(first, x)] + m


def trace_pattern(slots, choice, pairs, t, Rb):
    """Tr[(p'+m) String (p+m) R_b], R_1 = gamma_mu, R_2 = (p+p')_mu."""
    p, q = kin(t)
    pp = p + q
    ps, qs = slash(p), slash(q)
    labels = sorted({s[1] for s in slots if s[0] == 'g' and s[1] != 'mu'})
    pairlab = {}
    for n, (i, j) in enumerate(pairs):
        pairlab[i] = ('L', n); pairlab[j] = ('L', n)
    alllab = labels + [('L', n) for n in range(len(pairs))] + ['mu']
    total = 0j
    for vals in itertools.product(range(4), repeat=len(alllab)):
        asg = dict(zip(alllab, vals))
        w = 1.0
        for lab in alllab[:-1]:
            w *= ETA[asg[lab]]
        mu = asg['mu']
        M = slash(pp) + ID4
        for k, s in enumerate(slots):
            if s[0] == 'g':
                M = M @ GAM[asg[s[1]]]
            elif k in pairlab:
                M = M @ GAM[asg[pairlab[k]]]
            else:
                c = choice[k]
                M = M @ (ps if c == 'P' else qs if c == 'Q' else ID4)
        M = M @ (slash(p) + ID4)
        if Rb == 1:
            total += w * np.trace(M @ GAM[mu]) * ETA[mu]
        else:
            total += w * np.trace(M) * ETA[mu] * (p + pp)[mu]
    return total


TNODES = [1 / 12, 1 / 6, 1 / 2, 4 / 3, 9 / 4, 16 / 5]   # rational on-shell kinematics


def pattern_value(slots, choice, pairs, kind):
    """F2(0) (kind 'F2') or F1(0) (kind 'F1') of one numerator pattern.
    With t1 = a0 + a1 s, t2 = b0 + b1 s (s = q^2): F2(0) = (a1 - b1/2 - 3 b0/8)/4."""
    s = -np.array(TNODES)
    V = np.vander(s, len(s), increasing=True)
    t1 = np.array([trace_pattern(slots, choice, pairs, t, 1) for t in TNODES])
    a = np.linalg.solve(V, t1)
    if kind == 'F1':
        return a[0] / 8
    t2 = np.array([trace_pattern(slots, choice, pairs, t, 2) for t in TNODES])
    b = np.linalg.solve(V, t2)
    assert abs(a[0] - b[0] / 2) < 1e-9 and max(abs(a[4:]).max(), abs(b[4:]).max()) < 1e-9
    return (a[1] - b[1] / 2 - 3 * b[0] / 8) / 4


def build_patterns(slots, kind):
    msl = [k for k, s in enumerate(slots) if s[0] == 'm']
    out = []
    for pairs in matchings(msl):
        paired = {i for pr in pairs for i in pr}
        free = [k for k in msl if k not in paired]
        for ch in itertools.product('PQC', repeat=len(free)):
            if ch.count('Q') > (1 if kind == 'F2' else 0):
                continue
            choice = dict(zip(free, ch))
            if any(choice[k] == 'C' and slots[k][2] == 0 for k in free):
                continue
            val = pattern_value(slots, choice, pairs, kind)
            if abs(val) < 1e-12:
                continue
            assert abs(val.imag) < 1e-10
            out.append((pairs, choice, val.real))
    return out


# =============================================================== graphs and integrand
class Graph:
    """lines: dicts k ('e'|'g'), xi (loop incidence), a (p coefficient), b (q coefficient).
    slots: string from the outgoing end: ('g', label) or ('m', line, c) for kslash + c.
    groups: merged lines. Result unit: coefficient of r^L in F2 (or F1)."""

    def __init__(self, name, L, lines, slots, groups, extra=1.0, kind='F2'):
        self.name, self.L, self.lines, self.slots = name, L, lines, slots
        self.groups, self.kind, self.N = groups, kind, len(lines)
        ne = sum(1 for l in lines if l['k'] == 'e')
        ng = sum(1 for l in lines if l['k'] == 'g')
        nv = sum(1 for s in slots if s[0] == 'g')
        f = (-1j) ** (nv - 1) * (1j) ** ne * (-1j) ** ng
        f *= (1j) ** L * (-1) ** self.N * math.pi ** (2 * L) / (2 * math.pi) ** (4 * L)
        self.pref = f * (4 * math.pi ** 2) ** L * extra
        pats = []
        for pairs, choice, val in build_patterns(slots, kind):
            k = len(pairs)
            if self.N - 2 * L - k < 0 or (self.N - 2 * L - k == 0 and kind == 'F2'):
                # overall divergence: proportional to gamma^mu, no F2 part
                assert abs(val) < 1e-9, (name, pairs, val)
                continue
            pats.append((pairs, choice, val))
        self.pats = pats
        self.xi = np.array([l['xi'] for l in lines], float)
        self.al = np.array([l['a'] for l in lines], float)
        self.be = np.array([l['b'] for l in lines], float)

    def integrand(self, Z, msq_list, over=None):
        L, N, P = self.L, self.N, Z.shape[0]
        z = np.empty((P, N)); w = np.ones(P)
        for gi, g in enumerate(self.groups):
            for l in g:
                z[:, l] = Z[:, gi] / len(g)
            w *= Z[:, gi] ** (len(g) - 1) / math.factorial(len(g) - 1)
        xi = self.xi
        U = np.einsum('pi,is,it->pst', z, xi, xi)
        if L == 1:
            det = U[:, 0, 0]; Ui = (1 / det)[:, None, None]
        else:
            det = U[:, 0, 0] * U[:, 1, 1] - U[:, 0, 1] * U[:, 1, 0]
            Ui = np.empty_like(U)
            Ui[:, 0, 0] = U[:, 1, 1] / det; Ui[:, 1, 1] = U[:, 0, 0] / det
            Ui[:, 0, 1] = -U[:, 0, 1] / det; Ui[:, 1, 0] = -U[:, 1, 0] / det
        jp = np.einsum('pi,is,i->ps', z, xi, self.al)
        jq = np.einsum('pi,is,i->ps', z, xi, self.be)
        Uijp = np.einsum('pst,pt->ps', Ui, jp)
        Uijq = np.einsum('pst,pt->ps', Ui, jq)
        a = self.al[None, :] - np.einsum('is,ps->pi', xi, Uijp)
        b = self.be[None, :] - np.einsum('is,ps->pi', xi, Uijq)
        C = np.einsum('is,pst,jt->pij', xi, Ui, xi)
        D0 = np.einsum('ps,ps->p', jp, Uijp) - z @ (self.al ** 2)
        line = {k: s[1] for k, s in enumerate(self.slots) if s[0] == 'm'}
        cst = {k: s[2] for k, s in enumerate(self.slots) if s[0] == 'm'}
        over = over or {}
        Pk = {}
        for pairs, choice, val in self.pats:
            term = np.full(P, val)
            for k, c in choice.items():
                l = line[k]
                sc, cc = over.get(k, (1.0, cst[k]))
                term = term * (sc * a[:, l] if c == 'P' else sc * b[:, l] if c == 'Q' else cc)
            for (i, j) in pairs:
                term = term * (-C[:, line[i], line[j]])
                for kk in (i, j):
                    if kk in over:
                        term = term * over[kk][0]
            Pk[len(pairs)] = Pk.get(len(pairs), 0) + term
        out = np.zeros(P, complex)
        for wt, msq in msq_list:
            D = D0 + ((z * msq).sum(-1) if np.ndim(msq) == 2 else z @ msq)
            for kk, val in Pk.items():
                if N - 2 * L - kk == 0:            # PV-summed log term (sum of weights 0)
                    out += wt * (-np.log(D)) / 2 ** kk * val
                else:
                    out += wt * math.gamma(N - 2 * L - kk) / 2 ** kk * val * D ** (2 * L - N + kk)
        return self.pref * out * w / det ** 2


def mass_combos(graph, mg2, Lam2=None):
    """Pauli-Villars combinations: each photon line -> (mg2, +1), (Lam2, -1)."""
    ph = [i for i, l in enumerate(graph.lines) if l['k'] == 'g']
    base = np.array([1.0 if l['k'] == 'e' else 0.0 for l in graph.lines])
    opts = [(mg2, 1.0)] + ([(Lam2, -1.0)] if Lam2 is not None else [])
    out = []
    for combo in itertools.product(opts, repeat=len(ph)):
        msq = base.copy(); wt = 1.0
        for i, (m2, s) in zip(ph, combo):
            msq[i] = m2; wt *= s
        out.append((wt, msq))
    return out


def two_loop(name, j, pairing):
    """open line v1..v5, external photon at v_j, photon pairing ((i1,k1),(i2,k2))."""
    lines = []
    for k in range(1, 5):
        xi = [-(1 if i <= k < kk else 0) for (i, kk) in pairing]
        lines.append(dict(k='e', xi=xi, a=1.0, b=1.0 if k >= j else 0.0))
    for n in range(2):
        xi = [0, 0]; xi[n] = 1
        lines.append(dict(k='g', xi=xi, a=0.0, b=0.0))
    lab = {}
    for n, (i, kk) in enumerate(pairing):
        lab[i] = 'ab'[n]; lab[kk] = 'ab'[n]
    lab[j] = 'mu'
    slots = []
    for v in range(5, 0, -1):
        slots.append(('g', lab[v]))
        if v > 1:
            slots.append(('m', v - 2, 1.0))
    groups, seen = [], {}
    for i, l in enumerate(lines):
        key = (l['k'], tuple(l['xi']))
        if l['k'] == 'e' and key in seen:
            groups[seen[key]].append(i)
        else:
            seen[key] = len(groups); groups.append([i])
    return Graph(name, 2, lines, slots, groups)


# graph name -> (j, pairing, groups of the UV subgraph for the nested quadrature)
TWO_LOOP = {'L': (3, ((1, 5), (2, 4)), [1, 3]), 'X': (3, ((1, 4), (2, 5)), None),
            'C+': (2, ((1, 4), (3, 5)), [1, 2, 4]), 'C-': (4, ((1, 3), (2, 5)), [0, 1, 3]),
            'S+': (2, ((1, 5), (3, 4)), None), 'S-': (4, ((1, 5), (2, 3)), None)}


def one_loop_vertex(kind='F2'):
    lines = [dict(k='g', xi=[1], a=0., b=0.), dict(k='e', xi=[-1], a=1., b=0.),
             dict(k='e', xi=[-1], a=1., b=1. if kind == 'F2' else 0.)]
    slots = [('g', 'a'), ('m', 2, 1.0), ('g', 'mu'), ('m', 1, 1.0), ('g', 'a')]
    return Graph('V1' + kind, 1, lines, slots, [[0], [1, 2]], kind=kind)


# =============================================================== quadrature
def rule(n, k=5):
    """Gauss-Legendre in u on [0,1], sigmoidal map t = u^k/(u^k+(1-u)^k)."""
    x, w = np.polynomial.legendre.leggauss(n)
    u = (x + 1) / 2; w = w / 2
    a, b = u ** k, (1 - u) ** k
    return a / (a + b), w * k * (u ** (k - 1) * b + a * (1 - u) ** (k - 1)) / (a + b) ** 2


def simplex_points(m, t, w):
    if m == 1:
        return np.ones((1, 1)), np.ones(1)
    idx = np.array(list(itertools.product(range(len(t)), repeat=m - 1)), dtype=np.int32)
    T = t[idx]; W = np.prod(w[idx], axis=1)
    P, Wt = [], []
    for s in range(m):
        Zs = 1 / (1 + T.sum(1))
        Z = np.empty((len(idx), m))
        oth = [g for g in range(m) if g != s]
        Z[:, oth] = T * Zs[:, None]; Z[:, s] = Zs
        P.append(Z); Wt.append(W * Zs ** m)
    return np.concatenate(P), np.concatenate(Wt)


def _acc(v):
    fin = np.isfinite(v)
    return v[fin].sum(), int((~fin).sum())


def sector_integrate(f, m, n, k=5, chunk=300000):
    P, W = simplex_points(m, *rule(n, k))
    tot, bad = 0j, 0
    for c0 in range(0, len(P), chunk):
        s, b = _acc(f(P[c0:c0 + chunk]) * W[c0:c0 + chunk]); tot += s; bad += b
    return tot, bad


def log_rule(lo, npp, plen=3.0):
    x, w = np.polynomial.legendre.leggauss(npp)
    K = int(math.ceil(-lo / plen)); e = np.linspace(lo, 0, K + 1)
    s = np.concatenate([a + (b - a) * (x + 1) / 2 for a, b in zip(e[:-1], e[1:])])
    W = np.concatenate([w * (b - a) / 2 for a, b in zip(e[:-1], e[1:])])
    return np.exp(s), W * np.exp(s)


def nested_integrate(f, m, inner, n, k=5, lo=-40.0, npp=6, chunk=300000):
    """simplex of m group totals with Z_inner = rho w, Z_outer = (1-rho) y; rho on a log grid
    in (0, 1/2] and a sigmoidal grid on (1/2, 1)."""
    outer = [g for g in range(m) if g not in inner]
    t, w = rule(n, k)
    Pi, Wi = simplex_points(len(inner), t, w)
    Po, Wo = simplex_points(len(outer), t, w)
    r1, w1 = log_rule(lo, npp)
    rho = np.concatenate([0.5 * r1, 0.5 + 0.5 * t]); wr = np.concatenate([0.5 * w1, 0.5 * w])
    A = np.repeat(Pi, len(Po), 0); WA = np.repeat(Wi, len(Po))
    B = np.tile(Po, (len(Pi), 1)); WB = np.tile(Wo, len(Pi))
    tot, bad = 0j, 0
    for r, wrr in zip(rho, wr):
        jac = r ** (len(inner) - 1) * (1 - r) ** (len(outer) - 1) * wrr
        for c0 in range(0, len(A), chunk):
            Z = np.empty((len(A[c0:c0 + chunk]), m))
            Z[:, inner] = r * A[c0:c0 + chunk]; Z[:, outer] = (1 - r) * B[c0:c0 + chunk]
            s, b = _acc(f(Z) * WA[c0:c0 + chunk] * WB[c0:c0 + chunk] * jac)
            tot += s; bad += b
    return tot, bad


# =============================================================== exact one-loop pieces
mp.mp.dps = 30


def _pts(lam):
    return [0] + sorted({p for p in (lam / 4, lam, 4 * lam, mp.mpf(1) / 2) if 0 < p < 1}) + [1]


def f2(c):
    """one-loop F2 / r with a photon of squared mass c."""
    c = mp.mpf(c)
    if c == 0:
        return mp.mpf(1) / 2
    return mp.quad(lambda x: x**2 * (1 - x) / (x**2 + (1 - x) * c), _pts(mp.sqrt(c)))


def df2(c):
    c = mp.mpf(c)
    return -mp.quad(lambda x: x**2 * (1 - x)**2 / (x**2 + (1 - x) * c)**2, _pts(mp.sqrt(c)))


def F2_one_loop(mg, Lam):
    return f2(mp.mpf(mg)**2) - f2(mp.mpf(Lam)**2)


def sigma_onshell(mg, Lam):
    """(delta_2, Sigma(m)) / r with Sigma = (r/4) int dx [-2(1-x) pslash + 4] log(D_Lam/D_mg),
    D_mu = -x(1-x) p^2 + x + (1-x) mu (x on the electron line); delta_2 = dSigma/dpslash."""
    mg2, L2 = mp.mpf(mg)**2, mp.mpf(Lam)**2
    D = lambda x, mu: x**2 + (1 - x) * mu
    ell = lambda x: mp.log(D(x, L2) / D(x, mg2))
    pts = _pts(mp.mpf(mg))
    d2 = mp.quad(lambda x: -(1 - x) * ell(x) / 2
                 - (1 + x) * x * (1 - x) * (1 / D(x, L2) - 1 / D(x, mg2)), pts)
    sig = mp.quad(lambda x: (1 - (1 - x) / 2) * ell(x), pts)
    return d2, sig


def delta1_engine(mg, Lam, n=400):
    """delta_1 = -F1^loop(0) from the parametric engine (charge condition)."""
    g = one_loop_vertex('F1')
    t, w = rule(n, 5)
    Z = np.stack([1 - t, t], 1)
    return -(g.integrand(Z, mass_combos(g, mg**2, Lam**2)) * w).sum().real


# =============================================================== VP unit
def vp_insert(c, a, b):
    """F2/r of R(x) = x^2/(x+c) (1/(x+a) - 1/(x+b))^2, x = k^2 (Euclidean); b may be inf."""
    c, a = mp.mpf(c), mp.mpf(a)
    if b == mp.inf:
        h = lambda x: x**2 / (x + c)
        return c**2 / (a - c)**2 * f2(c) + mp.diff(h, -a) * f2(a) - (h(-a) * df2(a) if a > 0 else 0)
    b = mp.mpf(b)
    ha = lambda x: x**2 / (x + c) * ((b - a) / (x + b))**2
    hb = lambda x: x**2 / (x + c) * ((a - b) / (x + a))**2
    out = c**2 * (1 / (a - c) - 1 / (b - c))**2 * f2(c)
    for e, h in ((a, ha), (b, hb)):
        out += mp.diff(h, -e) * f2(e) - h(-e) * df2(e)
    return out


def vp_flavour(M, mg, Lam):
    """one flavour of mass M: int dv rho(v) F2[x^2/(x+mu_v^2) D^2], mu_v^2 = 4M^2/(1-v^2)."""
    rho = lambda v: v**2 * (1 - v**2 / 3) / (1 - v**2)
    L2 = mp.inf if Lam == mp.inf else mp.mpf(Lam)**2
    return mp.quad(lambda v: rho(v) * vp_insert(4 * mp.mpf(M)**2 / (1 - v**2), mp.mpf(mg)**2, L2),
                   [0, 0.5, 0.9, 0.99, 1])


def vp_unit(mg, Lam, M1=None, M2=None):
    v = vp_flavour(1, mg, Lam)
    if M1 is None:
        return v
    M1, M2 = mp.mpf(M1), mp.mpf(M2)
    c1 = (M2**2 - 1) / (M1**2 - M2**2); c2 = (M1**2 - 1) / (M2**2 - M1**2)
    return v + c1 * vp_flavour(M1, mg, Lam) + c2 * vp_flavour(M2, mg, Lam)


# =============================================================== S unit, insertion form
def _heavy_graph(side):
    lines = [dict(k='g', xi=[1], a=0., b=0.), dict(k='e', xi=[-1], a=1., b=0.),
             dict(k='e', xi=[-1], a=1., b=1.)]
    slots = [('g', 'a'), ('m', 2, 1.0), ('g', 'mu'), ('m', 1, 1.0), ('g', 'a')]
    g = Graph('S' + side + 'R', 1, lines, slots, [[0], [1], [2]])
    g.heavy_line, g.heavy_slot = (2, 1) if side == '+' else (1, 3)
    return g


def _sigma_R_coeffs(x, mu):
    """g(z) = (a z + b)/(M^2 - z^2); g - g(1) - (z-1) g'(1) = (z-1)^2 (al z + be)/(M^2 - z^2)."""
    a, b = -2 * (1 - x), 4.0
    M2 = 1 / (1 - x) + mu / x
    d = M2 - 1
    g1 = (a + b) / d
    gp1 = a / d + 2 * (a + b) / d ** 2
    return M2, gp1, b - (g1 - gp1) * M2


def S_side(side, mg, Lam, nx=48, ns=72, n=28, k=5):
    """one side of the S unit: outer one-loop vertex with i S (-i Sigma_R) i S inserted."""
    g = _heavy_graph(side)
    tx, wx = rule(nx, k)
    u, ws = np.polynomial.legendre.leggauss(ns)
    s0, s1 = math.log(mg ** 2), math.log(Lam ** 2)
    s = s0 + (u + 1) / 2 * (s1 - s0); ws = ws / 2 * (s1 - s0)
    P, W = simplex_points(3, *rule(n, k))
    total = 0.0
    for x, wxx in zip(tx, wx):
        x = min(max(x, 1e-15), 1 - 1e-15)
        for sj, wsj in zip(s, ws):
            mu = math.exp(sj)
            M2, al, be = _sigma_R_coeffs(x, mu)
            ml = []
            for pw, m2 in [(1.0, mg ** 2), (-1.0, Lam ** 2)]:
                msq = np.array([m2, 1.0, 1.0]); msq[g.heavy_line] = M2; ml.append((pw, msq))
            v = g.integrand(P, ml, over={g.heavy_slot: (al, be)})
            total += wxx * wsj * mu * (-0.25 / x) * _acc(v * W)[0]
    return total.real


def S_side_bare_plus_ct(side, mg, Lam, n=40):
    """the same side as bare two-loop graph + counterterm graphs i(kslash delta2 - delta_m)."""
    j, pairing, _ = TWO_LOOP['S' + side]
    g = two_loop('S' + side, j, pairing)
    mc = mass_combos(g, mg ** 2, Lam ** 2)
    bare = sector_integrate(lambda Z: g.integrand(Z, mc), len(g.groups), n)[0].real
    d2, sig = [float(mp.re(v)) for v in sigma_onshell(mg, Lam)]
    dm = d2 - sig
    bq = 1. if side == '+' else 0.
    lines = [dict(k='g', xi=[1], a=0., b=0.), dict(k='e', xi=[-1], a=1., b=0.),
             dict(k='e', xi=[-1], a=1., b=1.), dict(k='e', xi=[-1], a=1., b=1.)]
    if side == '-':
        lines[2]['b'] = 0.; lines[3]['b'] = 0.; lines[1]['b'] = 1.
        s2 = [('g', 'a'), ('m', 1, 1.0), ('g', 'mu'), ('m', 3, 1.0), ('m', 2, 0.0), ('m', 2, 1.0), ('g', 'a')]
        sm = [('g', 'a'), ('m', 1, 1.0), ('g', 'mu'), ('m', 3, 1.0), ('m', 2, 1.0), ('g', 'a')]
    else:
        s2 = [('g', 'a'), ('m', 3, 1.0), ('m', 2, 0.0), ('m', 2, 1.0), ('g', 'mu'), ('m', 1, 1.0), ('g', 'a')]
        sm = [('g', 'a'), ('m', 3, 1.0), ('m', 2, 1.0), ('g', 'mu'), ('m', 1, 1.0), ('g', 'a')]
    ct = 0
    for sl, ex in ((s2, 1j * d2), (sm, -1j * dm)):
        gg = Graph('ct', 1, lines, sl, [[0], [1, 2, 3]], extra=ex)
        t, w = rule(400, 5)
        ct += (gg.integrand(np.stack([1 - t, t], 1), mass_combos(gg, mg ** 2, Lam ** 2)) * w).sum()
    return bare, ct.real


# =============================================================== units
_G = {}


def graph(name):
    if name not in _G:
        j, pairing, _ = TWO_LOOP[name]
        _G[name] = two_loop(name, j, pairing)
    return _G[name]


def bare(name, mg, Lam, n):
    g = graph(name)
    mc = mass_combos(g, mg ** 2, None if Lam is None else Lam ** 2)
    inner = TWO_LOOP[name][2]
    f = lambda Z: g.integrand(Z, mc)
    if inner is None or Lam is None:
        v, bad = sector_integrate(f, len(g.groups), n)
    else:
        npp = 6 if n <= 32 else 8
        v, bad = nested_integrate(f, len(g.groups), inner, n, lo=-2 * math.log(Lam) - 25, npp=npp)
    return v.real, bad


GRIDS = {  # (coarse, fine) node numbers per coordinate
    'L': (64, 96), 'X': (32, 40), 'C+': (28, 36), 'C-': (28, 36), 'S': ((48, 72, 28), (64, 112, 36))}


def task(args):
    """one evaluation; returns a dict (run in a worker process)."""
    name, mg, Lam, level = args
    t0 = time.time()
    out = dict(name=name, mg=mg, Lam=Lam, level=level)
    if name in ('S+', 'S-'):
        nx, ns, n = GRIDS['S'][level]
        out['value'] = S_side(name[1], mg, Lam, nx, ns, n)
    elif name == 'VP':
        out['value'] = float(vp_unit(mg, Lam))
    elif name == 'ONE':
        d2, sig = sigma_onshell(mg, Lam)
        out.update(delta2=float(mp.re(d2)), sigma=float(mp.re(sig)),
                   delta1=delta1_engine(mg, Lam), F2=float(F2_one_loop(mg, Lam)))
    else:
        v, bad = bare(name, mg, Lam, GRIDS[name][level])
        out['value'] = v; out['bad'] = bad
    out['sec'] = round(time.time() - t0, 1)
    return out


def run_tasks(tasks, procs, outfile):
    import multiprocessing as mpc
    with mpc.get_context('fork').Pool(procs) as pool, open(outfile, 'a') as fh:
        for res in pool.imap_unordered(task, tasks):
            fh.write(json.dumps(res) + '\n'); fh.flush()
            print(json.dumps(res), flush=True)


def scan_tasks(points, names=('L', 'X', 'C+', 'C-', 'S+', 'S-', 'VP', 'ONE'), levels=(0, 1)):
    tasks = []
    for mg, Lam in points:
        for nm in names:
            for lv in (levels if nm not in ('VP', 'ONE') else (0,)):
                tasks.append((nm, mg, Lam, lv))
    # longest first
    order = {'C+': 0, 'C-': 0, 'X': 1, 'S+': 2, 'S-': 2, 'L': 3, 'VP': 4, 'ONE': 5}
    return sorted(tasks, key=lambda t: (order[t[0]], -t[3]))


# =============================================================== assembling units
BMR = {  # BMR-I p. 852, Feynman gauge, photon mass lambda; value = a ln(lambda/m) + b
    'VP': (0, mp.mpf(119) / 36 - mp.pi**2 / 3),
    'S': (1, mp.mpf(11) / 24 - mp.zeta(2) / 3),
    'C': (-1, -mp.mpf(67) / 24 + 2 * mp.zeta(2) * mp.log(2) + mp.zeta(2) / 3 - mp.zeta(3) / 2),
    'L': (0, mp.mpf(11) / 48 + mp.zeta(2) / 3),
    'X': (0, mp.mpf(1) / 6 - 5 * mp.zeta(2) * mp.log(2) + mp.mpf(13) / 6 * mp.zeta(2)
          + mp.mpf(5) / 4 * mp.zeta(3))}
A14 = mp.mpf(197) / 144 + mp.pi**2 / 12 - mp.pi**2 / 2 * mp.log(2) + mp.mpf(3) / 4 * mp.zeta(3)


def assemble(rows):
    """rows -> {(mg, Lam): {unit: (value, quad_err)}} from the fine level, error = |fine-coarse|."""
    by = {}
    for r in rows:
        by.setdefault((r['mg'], r['Lam']), {}).setdefault(r['name'], {})[r.get('level', 0)] = r
    res = {}
    for key, d in sorted(by.items()):
        one = d['ONE'][0]
        d1, F2 = one['delta1'], one['F2']
        val = lambda nm, lv: d[nm][lv]['value']
        def both(f):
            try:
                a, b = f(1), f(0)
                return (a, abs(a - b))
            except KeyError:
                return None
        u = {}
        u['L_bare'] = both(lambda lv: val('L', lv))
        u['L'] = both(lambda lv: val('L', lv) + d1 * F2)
        u['C_bare'] = both(lambda lv: val('C+', lv) + val('C-', lv))
        u['C'] = both(lambda lv: val('C+', lv) + val('C-', lv) + 2 * d1 * F2)
        u['S'] = both(lambda lv: val('S+', lv) + val('S-', lv))
        u['X'] = both(lambda lv: val('X', lv))
        u['VP'] = (d['VP'][0]['value'], 0.0) if 'VP' in d else None
        u['delta1'], u['delta2'], u['F2_1loop'] = (d1, 0), (one['delta2'], 0), (F2, 0)
        res[key] = u
    return res


def report(path):
    rows = [json.loads(l) for l in open(path)]
    res = assemble(rows)
    names = ['VP', 'S', 'C', 'L', 'X', 'L_bare', 'C_bare', 'delta1', 'delta2']
    print('m_gamma  Lambda  ' + '  '.join(f'{n:>20s}' for n in names) + '   S+C   total')
    for (mg, Lam), u in res.items():
        cells = []
        for n in names:
            v = u.get(n)
            cells.append(f'{v[0]:+.6f}({v[1]:.0e})' if v else ' ' * 20)
        tot = sum(u[n][0] for n in ('VP', 'S', 'C', 'L', 'X') if u.get(n))
        sc = u['S'][0] + u['C'][0] if u.get('S') and u.get('C') else float('nan')
        print(f'{mg:7.0e} {Lam:7.0f}  ' + '  '.join(f'{c:>20s}' for c in cells)
              + f'  {sc:+.6f}  {tot:+.6f}')
    return res


def ir_fit(res, Lam):
    """Per unit at fixed Lambda: U(mg) = a ln mg + b + mg (c1 ln mg + c0) [+ c2 mg ln^2 mg],
    fitted on the points with mg <= 1e-3, 3e-3, 1e-2 (six fits). Returns, per unit, the mean
    fitted a with its spread, and b (median, spread) with a fixed to the nearest integer."""
    out = {}
    for unit in ('VP', 'S', 'C', 'L', 'X', 'S+C'):
        a_free, b_fix = [], []
        for mmax in (1.01e-3, 3.1e-3, 1.1e-2):
            ks = sorted(k for k in res if k[1] == Lam and k[0] <= mmax)
            lam = np.array([k[0] for k in ks]); lg = np.log(lam)
            y = np.array([res[k]['S'][0] + res[k]['C'][0] if unit == 'S+C' else res[k][unit][0]
                          for k in ks])
            for extra in ([], [lam * lg ** 2]):
                cols = [np.ones_like(lg), lam * lg, lam] + extra
                if len(cols) + 1 <= len(y):
                    a_free.append(np.linalg.lstsq(np.stack([lg] + cols, 1), y, rcond=None)[0][0])
        a = round(float(np.mean(a_free)))
        for mmax in (1.01e-3, 3.1e-3, 1.1e-2):
            ks = sorted(k for k in res if k[1] == Lam and k[0] <= mmax)
            lam = np.array([k[0] for k in ks]); lg = np.log(lam)
            y = np.array([res[k]['S'][0] + res[k]['C'][0] if unit == 'S+C' else res[k][unit][0]
                          for k in ks]) - a * lg
            for extra in ([], [lam * lg ** 2]):
                cols = [np.ones_like(lg), lam * lg, lam] + extra
                if len(cols) <= len(y):
                    b_fix.append(np.linalg.lstsq(np.stack(cols, 1), y, rcond=None)[0][0])
        out[unit] = dict(a=float(np.mean(a_free)), a_spread=float(np.ptp(a_free)), a_int=a,
                         b=float(np.median(b_fix)), b_spread=float(np.ptp(b_fix)))
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('mode', choices=['checks', 'uv', 'ir', 'vp', 'fit'])
    ap.add_argument('file', nargs='?')
    ap.add_argument('--procs', type=int, default=4)
    ap.add_argument('--out')
    ap.add_argument('--points', help='override the scan: "mg,Lam;mg,Lam;..."')
    args = ap.parse_args()
    procs = max(1, min(args.procs, 4))
    if args.mode == 'checks':
        checks()
    elif args.mode in ('uv', 'ir'):
        pts = ([(0.01, L) for L in (10., 30., 100., 300., 1000.)] if args.mode == 'uv' else
               [(m, 1000.) for m in (0.01, 3e-3, 1e-3, 3e-4, 1e-4, 3e-5, 1e-5)])
        if args.points:
            pts = [tuple(float(v) for v in s.split(',')) for s in args.points.split(';')]
        out = args.out or f'two_loop_units_{args.mode}.jsonl'
        run_tasks(scan_tasks(pts), procs, out)
        report(out)
    elif args.mode == 'vp':
        vp_scan()
    else:
        res = report(args.file)
        for Lam in sorted({k[1] for k in res}):
            if sum(1 for k in res if k[1] == Lam) >= 5:
                print('IR fits at Lambda =', Lam, '(b with a fixed to the nearest integer)')
                bmr = dict(BMR); bmr['S+C'] = (0, BMR['S'][1] + BMR['C'][1])
                for unit, f in ir_fit(res, Lam).items():
                    print(f"  {unit:4s} a = {f['a']:+.5f} (spread {f['a_spread']:.0e})"
                          f"  b = {f['b']:+.6f} (spread {f['b_spread']:.0e})"
                          f"  BMR: a = {bmr[unit][0]:+d}, b = {float(bmr[unit][1]):+.6f}"
                          f"  b - BMR = {f['b'] - float(bmr[unit][1]):+.1e}")


def checks():
    t0 = time.time()
    # 1. projector
    print('projector: F2[gamma^mu] =', pattern_value([('g', 'mu')], {}, [], 'F2').real)
    # 2. one-loop F2 with a massive photon
    g = one_loop_vertex()
    t, w = rule(300, 5)
    Z = np.stack([1 - t, t], 1)
    for lam in (1e-4, 0.3, 1.0):
        v = (g.integrand(Z, mass_combos(g, lam**2)) * w).sum().real
        print(f'one loop F2/r, lambda={lam}: engine {v:.12f}  exact {float(f2(lam**2)):.12f}')
    # 3. Ward identity at fixed regulators
    for mg, Lam in ((0.1, 10.), (0.03, 100.), (0.5, 3.)):
        d2, _ = sigma_onshell(mg, Lam)
        print(f'Ward: m_gamma={mg} Lambda={Lam}: delta1 = {delta1_engine(mg, Lam):.12f}'
              f'  delta2 = {float(mp.re(d2)):.12f}')
    # 4. S insertion form = bare graph + counterterm graphs
    for side in '+-':
        for mg, Lam in ((0.5, 3.), (0.2, 10.)):
            b, c = S_side_bare_plus_ct(side, mg, Lam)
            print(f'S{side} at ({mg},{Lam}): bare {b:+.6f} + ct {c:+.6f} = {b + c:+.6f};'
                  f' insertion form {S_side(side, mg, Lam):+.6f}')
    # 5. mirror pairs
    for a, b in (('C+', 'C-'),):
        va, vb = bare(a, 0.1, 10., 28)[0], bare(b, 0.1, 10., 28)[0]
        print(f'mirror {a} {va:+.8f}  {b} {vb:+.8f}')
    # 6. crossed graph at m_gamma = 0 (no Pauli-Villars photon needed) against BMR
    v = bare('X', 0.0, None, 40)[0]
    print(f'X at m_gamma = 0, Lambda = inf: {v:+.6f}  BMR {float(BMR["X"][1]):+.6f}')
    # 7. counterterm insertions on one internal line of the one-loop vertex (single photon
    #    mass, Lambda = inf): the mass insertion has no power-like infrared growth in F2
    lines = [dict(k='g', xi=[1], a=0., b=0.), dict(k='e', xi=[-1], a=1., b=0.),
             dict(k='e', xi=[-1], a=1., b=1.), dict(k='e', xi=[-1], a=1., b=1.)]
    gm = Graph('mass', 1, lines, [('g', 'a'), ('m', 3, 1.0), ('m', 2, 1.0), ('g', 'mu'),
                                  ('m', 1, 1.0), ('g', 'a')], [[0], [1, 2, 3]], extra=1j)
    gk = Graph('kslash', 1, lines, [('g', 'a'), ('m', 3, 1.0), ('m', 2, 0.0), ('m', 2, 1.0),
                                    ('g', 'mu'), ('m', 1, 1.0), ('g', 'a')], [[0], [1, 2, 3]], extra=1j)
    t, w = rule(2000, 5)
    Z = np.stack([1 - t, t], 1)
    for lam in (0.1, 1e-2, 1e-3, 1e-4):
        vm = (gm.integrand(Z, mass_combos(gm, lam**2)) * w).sum().real
        vk = (gk.integrand(Z, mass_combos(gk, lam**2)) * w).sum().real
        print(f'insertion i*m on one line, lambda={lam}: {vm:+.6f};  i*kslash: {vk:+.6f}')
    # 8. VP at m_gamma = 0, Lambda = inf
    print('VP(0, inf) - (119/36 - pi^2/3) =', mp.nstr(vp_flavour(1, 0, mp.inf) - BMR['VP'][1], 3))
    print(f'checks done in {time.time() - t0:.0f} s')


def vp_scan():
    for mg, Lam in ((0.1, 10), (0.1, 100), (0.01, 100), (1e-3, 1e3), (1e-4, 1e4)):
        print(f'VP electron loop m_gamma={mg} Lambda={Lam}: '
              f'{mp.nstr(vp_unit(mg, Lam), 12)}  minus limit {mp.nstr(vp_unit(mg, Lam) - BMR["VP"][1], 3)}')
    for M1, M2 in ((3, 5), (10, 20), (30, 60), (100, 300), (1000, 1001)):
        v = vp_unit(0, mp.inf, M1, M2)
        print(f'VP with regulator fermions M1={M1} M2={M2} (m_gamma=0, Lambda=inf): '
              f'{mp.nstr(v, 12)}  minus limit {mp.nstr(v - BMR["VP"][1], 3)}')
    # size of the would-be Pi(0) term without (Z8): -(1/3) sum c_f ln M_f^2 times F2^(gamma)
    for M1, M2 in ((10, 20), (100, 300), (1000, 3000)):
        M1, M2 = mp.mpf(M1), mp.mpf(M2)
        c1 = (M2**2 - 1) / (M1**2 - M2**2); c2 = (M1**2 - 1) / (M2**2 - M1**2)
        pi0 = (c1 * mp.log(M1**2) + c2 * mp.log(M2**2)) / 3
        print(f'|Pi_reg(0)/r| = {mp.nstr(abs(pi0), 6)} at M1={M1}, M2={M2}'
              f' (times F2^(gamma) ~ 1/2 if (Z8) were dropped)')


if __name__ == '__main__':
    main()
