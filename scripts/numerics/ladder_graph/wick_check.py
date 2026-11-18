"""Check of QED.TwoLoop.UnitLGraph.openNum_L_explicit (Wick form) against the finite-difference
model of openNum .L in lean_ladder.py."""
import math, itertools
import numpy as np
from lean_ladder import *

PERM = [2, 0, 4, 1, 3]
LINES = [3, 2, 1, 0]


def pauli_mat(m, pp, p, mu):
    q = pp - p; q2 = dot(q, q); low = G4 @ (pp + p)
    return (m * (4 * m * m + q2)) * (enum(m, p) @ GAML[mu] @ enum(m, pp)) + \
        ((q2 - 2 * m * m) * low[mu]) * (enum(m, p) @ enum(m, pp))


def ch(B, Y):
    return np.trace(B[0] @ Y[0] @ B[1] @ Y[1] @ B[2] @ Y[2] @ B[3] @ Y[3])


def openNum_wick(z, m, lam, Lam, u, e=1.0):
    p, pp = rest(m), curve(m, u)
    mom = np.array(ext6(p, pp))[PVL]
    masses = np.array([m, m, m, m, lam, lam, Lam, Lam])
    A, Ai, S, V, U = symanzik(z, mom, masses)
    Ebar = []
    for k in range(4):
        i = LINES[k]
        kk = ALPHA[i, 0] * (-S[0]) + ALPHA[i, 1] * (-S[1]) + mom[i]
        Ebar.append(enum(m, kk))
    C = lambda k, l: sum(ALPHA[LINES[k], s] * Ai[s, r] * ALPHA[LINES[l], r] for s in range(2) for r in range(2))
    pveta = lambda x, y: (1 / I) * G4[x, y] * (Lam ** 2 - lam ** 2)
    kappa = (1 / (2 * math.pi) ** 8) * (I * e) ** 5 * (1 / I) ** 4
    tot = 0
    for mu in range(4):
        Pm = pauli_mat(m, pp, p, mu)
        for l in itertools.product(range(4), repeat=5):
            w = (1.0 if l[PERM[0]] == mu else 0.0) * pveta(l[PERM[1]], l[PERM[2]]) * pveta(l[PERM[3]], l[PERM[4]])
            if w == 0:
                continue
            B = [GAM[l[0]] @ Pm @ GAM[l[4]], GAM[l[3]], GAM[l[2]], GAM[l[1]]]
            t0 = ch(B, Ebar)
            two = 0
            for (k, ll) in itertools.combinations(range(4), 2):
                s = 0
                for nu in range(4):
                    Y = list(Ebar); Y[k] = GAML[nu]; Y[ll] = GAM[nu]
                    s += ch(B, Y)
                two += C(k, ll) * s
            four = 0
            for (a, b, c, d) in ((0, 1, 2, 3), (0, 2, 1, 3), (0, 3, 1, 2)):
                s = 0
                for nu in range(4):
                    for rho in range(4):
                        Y = [None] * 4
                        Y[a] = GAML[nu]; Y[b] = GAM[nu]; Y[c] = GAML[rho]; Y[d] = GAM[rho]
                        # chainFour slot pattern: (01)(23): gl nu, g nu, gl rho, g rho
                        # (02)(13): gl nu, gl rho, g nu, g rho ; (03)(12): gl nu, gl rho, g rho, g nu
                        s += ch(B, Y)
                four += C(a, b) * C(c, d) * s
            tot += w * (6 * t0 + two * V + 0.25 * four * V ** 2) / U ** 2
    return -(math.pi ** 4) * kappa * tot


if __name__ == '__main__':
    rng = np.random.default_rng(3)
    for t in range(2):
        z = rng.random(8); z /= z.sum()
        u = 0.13
        a = openNum_wick(z, 1.0, 0.3, 2.0, u)
        b = lean_integrand_u(z, 1.0, 0.3, 2.0, u)
        print(a, b, abs(a - b) / abs(b))
