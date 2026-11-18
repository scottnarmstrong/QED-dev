#!/usr/bin/env python3
"""Numerical model of the Lean objects `openNum .L`, `openV .L`, `openZero .L` (Lean conventions),
and comparison with the engine integrand of scripts/numerics/two_loop_unit_integrals.py.

Lean conventions: metric diag(-1,1,1,1); slash a = sum_mu lower(a)_mu gamma^mu; E = m - slash k;
paramNum = U^-2 [6 F(-S) + V <H(-S),G> + V^2/4 <R, Pi(G)>] with G = g (x) A^-1 (8 lines, m = 7).
Here <H,G> and <R,Pi(G)> are computed from F by finite differences along eigenvectors of G
(independent of the Wick formula to be proved).
"""
import itertools, math, sys
import numpy as np

I = 1j
GAM = [np.array([[0, 0, 1, 0], [0, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, 0]], complex),
       np.array([[0, 0, 0, 1], [0, 0, 1, 0], [0, -1, 0, 0], [-1, 0, 0, 0]], complex),
       np.array([[0, 0, 0, -I], [0, 0, I, 0], [0, I, 0, 0], [-I, 0, 0, 0]], complex),
       np.array([[0, 0, 1, 0], [0, 0, 0, -1], [-1, 0, 0, 0], [0, 1, 0, 0]], complex)]
G4 = np.diag([-1.0, 1, 1, 1])
ID = np.eye(4, dtype=complex)
GAML = [G4[m, m] * GAM[m] for m in range(4)]


def dot(a, b):
    return a @ G4 @ b


def slash(a):
    la = G4 @ a
    return sum(la[m] * GAM[m] for m in range(4))


def enum(m, p):
    return m * ID - slash(p)


# ladder data (class5LoopMatrix .L, pvLines, classLXMomenta)
ALPHA6 = np.array([[0, 1], [1, 0], [1, 0], [0, 1], [0, -1], [-1, 1]], float)
PVL = [0, 1, 2, 3, 4, 5, 4, 5]
ALPHA = ALPHA6[PVL]


def ext6(p, pp):
    z = np.zeros(4)
    return [p, p, pp, pp, z, z]


def curve(m, u):
    return np.array([m * (1 + u * u) / (1 - u * u), 2 * m * u / (1 - u * u), 0, 0])


def rest(m):
    return np.array([m, 0, 0, 0.0])


def symanzik(z, mom, masses):
    A = np.einsum('i,is,it->st', z, ALPHA, ALPHA)
    Ai = np.linalg.inv(A)
    B = np.einsum('i,is,iu->su', z, ALPHA, mom)          # B_s^mu
    S = Ai @ B                                             # loopShift
    V = sum(z[i] * (masses[i] ** 2 + dot(mom[i], mom[i])) for i in range(8)) - \
        sum(Ai[s, t] * dot(B[s], B[t]) for s in range(2) for t in range(2))
    U = np.linalg.det(A)
    return A, Ai, S, V, U


def chain_vertex(m, ks, lam, Lam, e=1.0):
    """classNumM .L at loop-dependent momenta ks[i] (i = 0..3 lines of the chain), times
    twoLoopNorm: returns list over mu of 4x4 matrices."""
    E = [enum(m, k) for k in ks]
    pre = (I * e) ** 5 * (1 / I) ** 4 * ((1 / I) * (Lam ** 2 - lam ** 2)) ** 2
    norm = 1.0 / (2 * math.pi) ** 8
    out = []
    for mu in range(4):
        tot = np.zeros((4, 4), complex)
        for nu in range(4):
            for rho in range(4):
                # gamma^{l4} E3 gamma^{l3} E2 gamma^{l2} E1 gamma^{l1} E0 gamma^{l0}
                # pairs (0,4) and (1,3) via pvEta = (1/i) g (Lam^2-lam^2): g_{nu nu} g_{rho rho}
                w = G4[nu, nu] * G4[rho, rho]
                tot += w * (GAM[nu] @ E[3] @ GAM[rho] @ E[2] @ GAM[mu] @ E[1] @ GAM[rho] @ E[0] @ GAM[nu])
        out.append(norm * pre * tot)
    return out


def pauli_wt(m, pp, p):
    q = pp - p
    q2 = dot(q, q)
    lowpp = G4 @ (pp + p)
    W = np.zeros((4, 4, 4), complex)
    Np, Npp = enum(m, p), enum(m, pp)
    for mu in range(4):
        M1 = Np @ GAML[mu] @ Npp
        M2 = Np @ Npp
        W[mu] = (m * (4 * m * m + q2) * M1 + (q2 - 2 * m * m) * lowpp[mu] * M2).T   # (j,i) -> [i,j]
    return W


def pauli_num(m, pp, p, Vmu):
    W = pauli_wt(m, pp, p)
    return sum(np.sum(W[mu] * Vmu[mu]) for mu in range(4))


def param_num_lean(Ffun, z, mom, masses):
    """paramNum for a scalar polynomial F (degree <= 4) of l in R^{2x4}, by finite differences."""
    A, Ai, S, V, U = symanzik(z, mom, masses)
    G = np.kron(Ai, G4)          # index (s, mu) -> s*4+mu ; G_{(s,mu),(r,nu)} = g_{mu nu} Ai_{s r}
    X = -S.reshape(8)
    lam_, vec = np.linalg.eigh(G)
    F0 = Ffun(X.reshape(2, 4))
    ts = np.array([-2, -1, 0, 1, 2], float)
    Vd = np.vander(ts, 5, increasing=True)

    def coeffs(v, base=X):
        vals = np.array([Ffun((base + t * v).reshape(2, 4)) for t in ts])
        return np.linalg.solve(Vd, vals)
    c2 = []; c4 = []
    for k in range(8):
        c = coeffs(vec[:, k]); c2.append(c[2]); c4.append(c[4])
    two = sum(lam_[k] * c2[k] for k in range(8))
    four = sum(3 * lam_[k] ** 2 * c4[k] for k in range(8))
    for k in range(8):
        for l in range(k + 1, 8):
            qp = coeffs(vec[:, k] + vec[:, l])[4]
            qm = coeffs(vec[:, k] - vec[:, l])[4]
            e22 = (qp + qm) / 2 - c4[k] - c4[l]
            four += lam_[k] * lam_[l] * e22
    return (6 * F0 + V * two + V ** 2 / 4 * four) / U ** 2, V, U


def lean_integrand_u(z, m, lam, Lam, u):
    """openNum .L (x, u) / openV(x)^4 is NOT what we want; return openNum(x,u) and V(x, q=0)."""
    p, pp = rest(m), curve(m, u)
    mom = np.array(ext6(p, pp))[PVL]
    masses = np.array([m, m, m, m, lam, lam, Lam, Lam])
    W = pauli_wt(m, pp, p)

    def F(l):
        ks = [ALPHA6[i, 0] * l[0] + ALPHA6[i, 1] * l[1] + ext6(p, pp)[i] for i in range(4)]
        Vmu = chain_vertex(m, ks, lam, Lam)
        return sum(np.sum(W[mu] * Vmu[mu]) for mu in range(4))
    val, V, U = param_num_lean(F, z, mom, masses)
    return -(math.pi ** 4) * val


def lean_V0(z, m, lam, Lam):
    p = rest(m)
    mom = np.array(ext6(p, p))[PVL]
    masses = np.array([m, m, m, m, lam, lam, Lam, Lam])
    return symanzik(z, mom, masses)[3]


def lean_integrand(z, m, lam, Lam, h=2e-3):
    """secondCoeff(openNum .L (x, .)) / openV(x)^4 at the point z (8 homogeneous coords)."""
    def c2(hh):
        gp = lean_integrand_u(z, m, lam, Lam, hh)
        gm = lean_integrand_u(z, m, lam, Lam, -hh)
        g0 = lean_integrand_u(z, m, lam, Lam, 0.0)
        return (gp + gm - 2 * g0) / (2 * hh * hh)
    a, b = c2(h), c2(h / 2)
    val = (4 * b - a) / 3
    return val / lean_V0(z, m, lam, Lam) ** 4


if __name__ == '__main__':
    rng = np.random.default_rng(1)
    z = rng.random(8); z /= z.sum()
    print('g(z) =', lean_integrand(z, 1.0, 0.3, 2.0))
    # homogeneity check: degree -8
    print('g(2z)*2^8 =', lean_integrand(2 * z, 1.0, 0.3, 2.0) * 2 ** 8)


# ---------------------------------------------------------------- split-resolved coefficients
def param_parts(Ffun, z, mom):
    """(T1, T2, T3) with paramNum = T1 + T2 V + T3 V^2 (mass independent)."""
    masses = np.zeros(8)
    A, Ai, S, V, U = symanzik(z, mom, masses)
    G = np.kron(Ai, G4)
    X = -S.reshape(8)
    lam_, vec = np.linalg.eigh(G)
    F0 = Ffun(X.reshape(2, 4))
    ts = np.array([-2, -1, 0, 1, 2], float)
    Vd = np.vander(ts, 5, increasing=True)

    def coeffs(v):
        vals = np.array([Ffun((X + t * v).reshape(2, 4)) for t in ts])
        return np.linalg.solve(Vd, vals)
    c2 = []; c4 = []
    for k in range(8):
        c = coeffs(vec[:, k]); c2.append(c[2]); c4.append(c[4])
    two = sum(lam_[k] * c2[k] for k in range(8))
    four = sum(3 * lam_[k] ** 2 * c4[k] for k in range(8))
    for k in range(8):
        for l in range(k + 1, 8):
            qp = coeffs(vec[:, k] + vec[:, l])[4]
            qm = coeffs(vec[:, k] - vec[:, l])[4]
            four += lam_[k] * lam_[l] * ((qp + qm) / 2 - c4[k] - c4[l])
    return np.array([6 * F0, two, four / 4]) / U ** 2


def parts_u(z, m, u, pv=1.0):
    p, pp = rest(m), curve(m, u)
    mom = np.array(ext6(p, pp))[PVL]
    W = pauli_wt(m, pp, p)

    def F(l):
        ks = [ALPHA6[i, 0] * l[0] + ALPHA6[i, 1] * l[1] + ext6(p, pp)[i] for i in range(4)]
        Vmu = chain_vertex(m, ks, 0.0, math.sqrt(pv))
        return sum(np.sum(W[mu] * Vmu[mu]) for mu in range(4))
    return -(math.pi ** 4) * param_parts(F, z, mom)


def parts_c2(z, m, h=2e-3):
    def c2(hh):
        return (parts_u(z, m, hh) + parts_u(z, m, -hh) - 2 * parts_u(z, m, 0.0)) / (2 * hh * hh)
    return (4 * c2(h / 2) - c2(h)) / 3


def V0_nomass(z, m):
    p = rest(m)
    mom = np.array(ext6(p, p))[PVL]
    return symanzik(z, mom, np.array([m, m, m, m, 0, 0, 0, 0.]))[3]
