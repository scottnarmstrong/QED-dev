#!/usr/bin/env python3
"""Exact second-order coefficients c2[T1], c2[T2], c2[T3] of the projected parametric numerator
of the classes S+, S-, C+, C- (and L for regression), in the Lean conventions. NOT a proof.

paramNum = T1 + T2 V + T3 V^2 (Wick's rule, QED.TwoLoop.ParamNumEval.paramNumOf_elecChain):
  T1 = k U^-2 * 6 * sum_w ch(B; E),  T2 = k U^-2 * sum_{k<l} C_kl sum_w sum_s ch(B; E | slot k ->
  gamma_s, slot l -> gamma^s),  T3 = k U^-2 / 4 * sum_{pairings} C C sum_w ...,
with k = -pi^4 kappa, and the photon weights w of the class pairing. Here the trace sums are done
with explicit 4x4 matrices in exact arithmetic (sympy), the slot momenta q_k = a_k p + b_k p'(u)
with p'(u) = (1 + 2u^2, 2u, 0, 0) + O(u^3) at m = 1, and the second-order coefficient in u is
taken exactly. The slot coefficients a_k, b_k and C_kl are then evaluated from the Symanzik data
of the class at a symbolic point z (all eight parameters symbolic).

Output: the coefficients normalized as c2[T_i] = (Lambda^2 - m_gamma^2)^2 / K * R_i(z) with
K = 16 pi^4 / (64 i); R_i is printed in the group variables of the class.
Run: nice -n 10 python3 symbolic_c2.py Sp   (a few minutes per class)
"""
import itertools, sys
import sympy as sp

I = sp.I
GAM = [sp.Matrix([[0, 0, 1, 0], [0, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, 0]]),
       sp.Matrix([[0, 0, 0, 1], [0, 0, 1, 0], [0, -1, 0, 0], [-1, 0, 0, 0]]),
       sp.Matrix([[0, 0, 0, -I], [0, 0, I, 0], [0, I, 0, 0], [-I, 0, 0, 0]]),
       sp.Matrix([[0, 0, 1, 0], [0, 0, 0, -1], [-1, 0, 0, 0], [0, 1, 0, 0]])]
MET = [-1, 1, 1, 1]
GAML = [MET[m] * GAM[m] for m in range(4)]
ID = sp.eye(4)

LOOP = {'L': [[0, 1], [1, 0], [1, 0], [0, 1], [0, -1], [-1, 1]],
        'Cp': [[1, 1], [1, 1], [1, 0], [0, -1], [-1, -1], [0, 1]],
        'Cm': [[1, -1], [1, 0], [0, 1], [0, 1], [-1, 1], [0, -1]],
        'Sp': [[1, 1], [1, 1], [1, 0], [1, 1], [-1, -1], [0, 1]],
        'Sm': [[1, 0], [1, -1], [1, 0], [1, 0], [-1, 0], [0, 1]]}
EXT = {'L': [0, 0, 1, 1], 'Cp': [0, 1, 1, 1], 'Sp': [0, 1, 1, 1], 'Cm': [0, 0, 0, 1],
       'Sm': [0, 0, 0, 1]}
PERM = {'L': [2, 0, 4, 1, 3], 'Cp': [1, 0, 3, 2, 4], 'Cm': [3, 0, 2, 1, 4],
        'Sp': [1, 0, 4, 2, 3], 'Sm': [3, 0, 4, 1, 2]}
PVL = [0, 1, 2, 3, 4, 5, 4, 5]
LINES = [3, 2, 1, 0]          # chain slot k <-> line 3 - k

u = sp.Symbol('u')


def slash(v):
    return sum((MET[m] * v[m] * GAM[m] for m in range(4)), sp.zeros(4))


def enum(v):
    return ID - slash(v)


def trunc(M):
    """truncate a matrix of polynomials in u at order u^2."""
    return M.applyfunc(lambda e: sp.expand(sp.series(sp.expand(e), u, 0, 3).removeO())
                       if e.has(u) else e)


def c2(e):
    return sp.expand(e).coeff(u, 2)


def pauli_mats():
    p = [1, 0, 0, 0]
    pp = [1 + 2 * u ** 2, 2 * u, 0, 0]
    q = [pp[i] - p[i] for i in range(4)]
    q2 = sp.expand(-q[0] ** 2 + q[1] ** 2)
    q2 = sp.series(q2, u, 0, 3).removeO()
    low = [MET[m] * (pp[m] + p[m]) for m in range(4)]
    Np, Npp = enum(p), enum(pp)
    return [trunc((4 + q2) * (Np * GAML[mu] * Npp) + ((q2 - 2) * low[mu]) * (Np * Npp))
            for mu in range(4)]


def weights(name):
    pi = PERM[name]
    out = []
    for mu in range(4):
        for a in range(4):
            for b in range(4):
                l = [0] * 5
                l[pi[0]] = mu; l[pi[1]] = a; l[pi[2]] = a; l[pi[3]] = b; l[pi[4]] = b
                out.append((MET[a] * MET[b], mu, l))
    return out


def chain_sum(name, P, Y):
    """sum over the photon weights of ch(B; Y) (eta^2 factored out)."""
    tot = 0
    for w, mu, l in weights(name):
        M = GAM[l[0]] * P[mu] * GAM[l[4]] * Y[0] * GAM[l[3]] * Y[1] * GAM[l[2]] * Y[2] * \
            GAM[l[1]] * Y[3]
        tot += w * M.trace()
    return sp.expand(tot)


def slot_E(al, be):
    """E = 1 - slash(a p + b p'), al = a + b, be = b (to order u^2)."""
    q = [al + 2 * be * u ** 2, 2 * be * u, 0, 0]
    return enum(q)


def coefficients(name):
    al = sp.symbols('al0:4'); be = sp.symbols('be0:4')
    Cs = {(k, l): sp.Symbol(f'C{k}{l}') for k in range(4) for l in range(k + 1, 4)}
    P = pauli_mats()
    E = [slot_E(al[k], be[k]) for k in range(4)]
    # T1
    t1 = 6 * c2(chain_sum(name, P, E))
    # T2
    t2 = 0
    for (k, l) in itertools.combinations(range(4), 2):
        s = 0
        for nu in range(4):
            Y = list(E); Y[k] = GAML[nu]; Y[l] = GAM[nu]
            s += chain_sum(name, P, Y)
        t2 += Cs[(k, l)] * c2(s)
    # T3
    t3 = 0
    for (a, b, c, d) in ((0, 1, 2, 3), (0, 2, 1, 3), (0, 3, 1, 2)):
        s = 0
        for nu in range(4):
            for rho in range(4):
                Y = [None] * 4
                Y[a] = GAML[nu]; Y[b] = GAM[nu]; Y[c] = GAML[rho]; Y[d] = GAM[rho]
                s += chain_sum(name, P, Y)
        t3 += Cs[(a, b)] * Cs[(c, d)] * c2(s) / 4
    return al, be, Cs, sp.expand(t1), sp.expand(t2), sp.expand(t3)


def symanzik_data(name):
    z = sp.symbols('z0:8')
    A6 = LOOP[name]
    A = [A6[PVL[i]] for i in range(8)]
    M = sp.Matrix(2, 2, lambda s, t: sum(z[i] * A[i][s] * A[i][t] for i in range(8)))
    U = sp.expand(M.det())
    Mi = M.adjugate() / U
    ext = EXT[name] + [None, None]
    # B_s = sum_i z_i alpha_is mom_i = Bp_s p + Bq_s p'
    Bp = [sum(z[i] * A[i][s] for i in range(8) if ext[PVL[i]] == 0) for s in range(2)]
    Bq = [sum(z[i] * A[i][s] for i in range(8) if ext[PVL[i]] == 1) for s in range(2)]
    sig = [sum(Mi[s, t] * Bp[t] for t in range(2)) for s in range(2)]
    tau = [sum(Mi[s, t] * Bq[t] for t in range(2)) for s in range(2)]
    a = []; b = []
    for k in range(4):
        i = LINES[k]
        e = EXT[name][i]
        a.append(sp.together(-(A[i][0] * sig[0] + A[i][1] * sig[1]) + (1 if e == 0 else 0)))
        b.append(sp.together(-(A[i][0] * tau[0] + A[i][1] * tau[1]) + (1 if e == 1 else 0)))
    C = {(k, l): sp.together(sum(A[LINES[k]][s] * Mi[s, t] * A[LINES[l]][t]
                                 for s in range(2) for t in range(2)))
         for k in range(4) for l in range(k + 1, 4)}
    return z, U, a, b, C


def main(name):
    al, be, Cs, t1, t2, t3 = coefficients(name)
    print(name, 'T1 =', sp.factor(t1))
    print(name, 'T2 =', t2)
    print(name, 'T3 =', sp.factor(t3))
    z, U, a, b, C = symanzik_data(name)
    sub = {al[k]: a[k] + b[k] for k in range(4)}
    sub.update({be[k]: b[k] for k in range(4)})
    sub.update({Cs[kl]: C[kl] for kl in Cs})
    # T_i = k U^-2 * t_i with k = i eta^2 ... ; c2[T_i] = (L^2-m^2)^2 / K * R_i where
    # k = I (L^2 - m^2)^2 / (256 pi^4) and 1/K = 64 I / (16 pi^4): k = -(L^2-m^2)^2/(64 K) * ...
    # R_i = k / ((L^2 - m^2)^2 / K) * t_i / U^2 = (I K / (256 pi^4)) t_i / U^2 = t_i / (1024 U^2)
    R = [sp.factor(sp.together(t.subs(sub) / (1024 * U ** 2))) for t in (t1, t2, t3)]
    for i, r in enumerate(R):
        print(name, f'R{i + 1} =', r)
    return R


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'Sp')


# group variables: outer electrons zo, inner electrons (Y or y3, y4), photons za (outer), zb (inner)
GROUPS = {
    'Sp': lambda z, g: {z[0]: g['zo'] - z[1] - z[3], z[2]: g['Y'],
                        z[4]: g['za'] - z[6], z[5]: g['zb'] - z[7]},
    'Sm': lambda z, g: {z[0]: g['zo'] - z[2] - z[3], z[1]: g['Y'],
                        z[4]: g['za'] - z[6], z[5]: g['zb'] - z[7]},
    'Cp': lambda z, g: {z[0]: g['zo'] - z[1], z[2]: g['y3'], z[3]: g['y4'],
                        z[4]: g['za'] - z[6], z[5]: g['zb'] - z[7]},
    # C-: row 4 is the inner photon (0 2), row 5 the outer photon (1 4)
    'Cm': lambda z, g: {z[3]: g['zo'] - z[2], z[1]: g['y3'], z[0]: g['y4'],
                        z[5]: g['za'] - z[7], z[4]: g['zb'] - z[6]},
}


def grouped(name, R):
    g = {k: sp.Symbol(k) for k in ('zo', 'Y', 'y3', 'y4', 'za', 'zb')}
    z = sp.symbols('z0:8')
    sub = GROUPS[name](z, g)
    out = [sp.factor(sp.together(r.subs(sub))) for r in R]
    for i, r in enumerate(out):
        print(name, f'grouped R{i + 1} =', r, ' free:', sorted(map(str, r.free_symbols)))
    return out
