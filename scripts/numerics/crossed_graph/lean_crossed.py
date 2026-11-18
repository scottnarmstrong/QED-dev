#!/usr/bin/env python3
"""Numerical model of the Lean objects `openNum .X`, `openV .X` (Lean conventions), adapted from
../ladder_graph/lean_ladder.py to the crossed ladder.

Lean data of X: class5LoopMatrix .X rows (1,-1), (1,0), (1,0), (0,1), (-1,1), (0,-1); external
momenta (p, p, p', p', 0, 0); Pauli-Villars form: lines 4, 6 (photon 0-3, the outer photon `a`)
and 5, 7 (photon 1-4, the inner photon `b`), lines 4, 5 at m_gamma and 6, 7 at Lambda.
Photon pairing of the chain: permX = (2, 0, 3, 1, 4), i.e. vertices (0,3) and (1,4), the
external photon at vertex 2.
paramNum by finite differences along the eigenvectors of G (independent of the Wick formula).
"""
import itertools, math
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


ALPHA6 = np.array([[1, -1], [1, 0], [1, 0], [0, 1], [-1, 1], [0, -1]], float)
PVL = [0, 1, 2, 3, 4, 5, 4, 5]
ALPHA = ALPHA6[PVL]
LINES = [3, 2, 1, 0]          # chain slot k <-> line LINES[k]
PERM = [2, 0, 3, 1, 4]


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
    B = np.einsum('i,is,iu->su', z, ALPHA, mom)
    S = Ai @ B
    V = sum(z[i] * (masses[i] ** 2 + dot(mom[i], mom[i])) for i in range(8)) - \
        sum(Ai[s, t] * dot(B[s], B[t]) for s in range(2) for t in range(2))
    U = np.linalg.det(A)
    return A, Ai, S, V, U


def pauli_mat(m, pp, p, mu):
    q = pp - p; q2 = dot(q, q); low = G4 @ (pp + p)
    return (m * (4 * m * m + q2)) * (enum(m, p) @ GAML[mu] @ enum(m, pp)) + \
        ((q2 - 2 * m * m) * low[mu]) * (enum(m, p) @ enum(m, pp))


def chain_vertex(m, ks, lam, Lam, e=1.0):
    """classNumM .X at loop-dependent momenta ks[i] (lines 0..3), times twoLoopNorm."""
    E = [enum(m, k) for k in ks]
    pre = (I * e) ** 5 * (1 / I) ** 4 * ((1 / I) * (Lam ** 2 - lam ** 2)) ** 2
    norm = 1.0 / (2 * math.pi) ** 8
    out = []
    for mu in range(4):
        tot = np.zeros((4, 4), complex)
        for nu in range(4):
            for sg in range(4):
                # openChain = G4 E3 G3 E2 G2 E1 G1 E0 G0 with l0 = l3 = nu, l1 = l4 = sg, l2 = mu
                w = G4[nu, nu] * G4[sg, sg]
                tot += w * (GAM[sg] @ E[3] @ GAM[nu] @ E[2] @ GAM[mu] @ E[1] @ GAM[sg] @ E[0] @ GAM[nu])
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
        W[mu] = (m * (4 * m * m + q2) * M1 + (q2 - 2 * m * m) * lowpp[mu] * M2).T
    return W


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
