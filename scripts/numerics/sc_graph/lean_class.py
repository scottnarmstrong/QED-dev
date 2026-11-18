#!/usr/bin/env python3
"""Numerical model of the Lean objects `openNum c`, `openV c` for the open-line classes
c in {L, Sp, Sm, Cp, Cm} (Lean conventions), generalizing ../ladder_graph/lean_ladder.py.
NOT a proof.

Lean conventions: metric diag(-1,1,1,1); slash a = sum_mu lower(a)_mu gamma^mu; E = m - slash k;
paramNum = U^-2 [6 F(-S) + V <H(-S),G> + V^2/4 <R, Pi(G)>] with G = g (x) A^-1 (8 lines).
<H,G> and <R,Pi(G)> are computed from F by finite differences along eigenvectors of G
(independent of the Wick formula).

Class data (QED/Integration/SymanzikIntegrabilityClasses.lean `class5LoopMatrix`,
QED/TwoLoop/ParametricBridgeC.lean `extMomenta`, QED/TwoLoop/LimitCovarianceOpen.lean `perm*`):
the open line is G4 E3 G3 E2 G2 E1 G1 E0 G0 (vertex t carries G_t = gamma^{l_t}, line i runs from
vertex i to vertex i + 1); the photon pairing pi has the external photon at vertex pi(0) and the
internal photons (pi(1) pi(2)), (pi(3) pi(4)).
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

LOOP = {'L': [[0, 1], [1, 0], [1, 0], [0, 1], [0, -1], [-1, 1]],
        'X': [[1, -1], [1, 0], [1, 0], [0, 1], [-1, 1], [0, -1]],
        'Cp': [[1, 1], [1, 1], [1, 0], [0, -1], [-1, -1], [0, 1]],
        'Cm': [[1, -1], [1, 0], [0, 1], [0, 1], [-1, 1], [0, -1]],
        'Sp': [[1, 1], [1, 1], [1, 0], [1, 1], [-1, -1], [0, 1]],
        'Sm': [[1, 0], [1, -1], [1, 0], [1, 0], [-1, 0], [0, 1]]}
# which external momentum (0: p, 1: p') each electron line carries
EXT = {'L': [0, 0, 1, 1], 'X': [0, 0, 1, 1], 'Cp': [0, 1, 1, 1], 'Sp': [0, 1, 1, 1],
       'Cm': [0, 0, 0, 1], 'Sm': [0, 0, 0, 1]}
PERM = {'L': [2, 0, 4, 1, 3], 'X': [2, 0, 3, 1, 4], 'Cp': [1, 0, 3, 2, 4],
        'Cm': [3, 0, 2, 1, 4], 'Sp': [1, 0, 4, 2, 3], 'Sm': [3, 0, 4, 1, 2]}
PVL = [0, 1, 2, 3, 4, 5, 4, 5]


def dot(a, b):
    return a @ G4 @ b


def slash(a):
    la = G4 @ a
    return sum(la[m] * GAM[m] for m in range(4))


def enum(m, p):
    return m * ID - slash(p)


def curve(m, u):
    return np.array([m * (1 + u * u) / (1 - u * u), 2 * m * u / (1 - u * u), 0, 0])


def rest(m):
    return np.array([m, 0, 0, 0.0])


class Cls:
    def __init__(self, name):
        self.name = name
        self.A6 = np.array(LOOP[name], float)
        self.A = self.A6[PVL]
        self.ext = EXT[name]
        self.perm = PERM[name]

    def ext6(self, p, pp):
        z = np.zeros(4)
        return [p if e == 0 else pp for e in self.ext] + [z, z]

    def symanzik(self, z, mom, masses):
        A = np.einsum('i,is,it->st', z, self.A, self.A)
        Ai = np.linalg.inv(A)
        B = np.einsum('i,is,iu->su', z, self.A, mom)
        S = Ai @ B
        V = sum(z[i] * (masses[i] ** 2 + dot(mom[i], mom[i])) for i in range(8)) - \
            sum(Ai[s, t] * dot(B[s], B[t]) for s in range(2) for t in range(2))
        return A, Ai, S, V, np.linalg.det(A)

    def chain_vertex(self, m, ks, pv, e=1.0):
        """twoLoopNorm * classNumM c at line momenta ks (lines 0..3); photon factor
        pvEta = (1/i) g (Lam^2 - lam^2) with (Lam^2 - lam^2) = pv."""
        E = [enum(m, k) for k in ks]
        pre = (I * e) ** 5 * (1 / I) ** 4 * ((1 / I) * pv) ** 2
        norm = 1.0 / (2 * math.pi) ** 8
        pi = self.perm
        out = []
        for mu in range(4):
            tot = np.zeros((4, 4), complex)
            for a in range(4):
                for b in range(4):
                    l = [0] * 5
                    l[pi[0]] = mu; l[pi[1]] = a; l[pi[2]] = a; l[pi[3]] = b; l[pi[4]] = b
                    w = G4[a, a] * G4[b, b]
                    G = [GAM[l[t]] for t in range(5)]
                    tot += w * (G[4] @ E[3] @ G[3] @ E[2] @ G[2] @ E[1] @ G[1] @ E[0] @ G[0])
            out.append(norm * pre * tot)
        return out


def pauli_wt(m, pp, p):
    q = pp - p
    q2 = dot(q, q)
    lowpp = G4 @ (pp + p)
    W = np.zeros((4, 4, 4), complex)
    Np, Npp = enum(m, p), enum(m, pp)
    for mu in range(4):
        W[mu] = (m * (4 * m * m + q2) * (Np @ GAML[mu] @ Npp) +
                 (q2 - 2 * m * m) * lowpp[mu] * (Np @ Npp)).T
    return W


def param_parts(cls, Ffun, z, mom):
    """(T1, T2, T3) with paramNum = T1 + T2 V + T3 V^2."""
    A, Ai, S, V, U = cls.symanzik(z, mom, np.zeros(8))
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


def parts_u(cls, z, m, u, pv=1.0):
    p, pp = rest(m), curve(m, u)
    e6 = cls.ext6(p, pp)
    mom = np.array(e6)[PVL]
    W = pauli_wt(m, pp, p)

    def F(l):
        ks = [cls.A6[i, 0] * l[0] + cls.A6[i, 1] * l[1] + e6[i] for i in range(4)]
        Vmu = cls.chain_vertex(m, ks, pv)
        return sum(np.sum(W[mu] * Vmu[mu]) for mu in range(4))
    return -(math.pi ** 4) * param_parts(cls, F, z, mom)


def parts_c2(cls, z, m=1.0, h=2e-3):
    def c2(hh):
        return (parts_u(cls, z, m, hh) + parts_u(cls, z, m, -hh) - 2 * parts_u(cls, z, m, 0.0)) \
            / (2 * hh * hh)
    return (4 * c2(h / 2) - c2(h)) / 3


def V0_nomass(cls, z, m=1.0):
    p = rest(m)
    mom = np.array(cls.ext6(p, p))[PVL]
    return cls.symanzik(z, mom, np.array([m, m, m, m, 0, 0, 0, 0.]))[3]


K = 16 * math.pi ** 4 / (64j)
