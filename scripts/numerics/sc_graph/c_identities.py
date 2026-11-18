#!/usr/bin/env python3
"""The rational identities behind QED/TwoLoop/UnitSCGraphCpMain.lean and UnitSCGraphCmMain.lean, in
exact arithmetic. NOT a proof.

From the planar pieces (cp_planar.py, cm_planar.py) the second-order coefficients are polynomials in
the slot data alpha_k = a_k + b_k, beta_k = b_k, which are affine in S_s = sigma_s + tau_s, T_s = tau_s
(rational in the line parameters with denominator U). The script computes
  Phi1 = (T1 piece)(S, T),  Phi2 = sum_kl C_kl (piece_kl)(S, T),
checks U^4 Phi1 = 512 W M1 and U^3 Phi2 = -1024 M2 (the polynomials cpM1/cmM1, cpM2/cmM2 of the Lean
files are M1, M2 here), and compares R1 = 6 U^4 Phi1/(1024 U^6), R2 = U^3 Phi2/(1024 U^5) with the
direct 4x4 traces of symbolic_c2.py (a few minutes per class).
Run: nice -n 10 python3 c_identities.py Cp   (or Cm)
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sympy as sp
from planar_patterns import Fam, c, ONE, G0L, G1, P0, pw, al, be, E, I1
import cp_planar as CP
import symbolic_c2 as S

name = sys.argv[1] if len(sys.argv) > 1 else 'Cp'
pp, Hf, GL = CP.pp, CP.Hf, Fam(c(G0L), c(G1), c(ONE))
z0, z1, z2, z3, za, zb = sp.symbols('z0 z1 z2 z3 za zb')
S0, S1, T0, T1 = sp.symbols('S0 S1 T0 T1')
if name == 'Cp':
    P, PS = P0, P0.contract()
    v = {'T1': pp(P, Hf(E[0], E[1]), E[2], E[3]), '01': pp(P, GL, E[2], E[3]),
         '02a': pp(P, GL.mulRight(E[1]).contract().contract(), I1, E[3]), '02b': pp(P, GL.mulRight(E[1]), I1, E[3]),
         '03a': pp(PS, Hf(I1, E[1]), E[2], I1), '03b': pw(P, E[1].gam() * E[2], I1),
         '03c': pw(PS, E[1] * E[2].gam(), I1), '03d': pw(PS, E[1], E[2]), '12': pp(P, Hf(E[0], I1), I1, E[3]),
         '13a': pp(P, Hf(E[0], I1), E[2].gam(), I1), '13b': pp(P, Hf(E[0], I1), I1, E[2]),
         '13c': pp(P, Hf(E[0], E[2]), I1, I1), '13d': pw(P, I1, E[0] * E[2].gam()), '23': pp(P, Hf(E[0], E[1]), I1, I1)}
    t1 = v['T1']
    piece = {(0, 1): 4 * v['01'], (0, 2): -v['02a'] + 8 * v['02b'],
             (0, 3): v['03a'] + 4 * v['03b'] + 2 * v['03c'] + 4 * v['03d'], (1, 2): 2 * v['12'],
             (1, 3): v['13a'] + 2 * v['13b'] + 2 * v['13c'] + 4 * v['13d'], (2, 3): 2 * v['23']}
    # z0 outer (split z1), y3 = z2, y4 = z3, za = z4 + z6, zb = z5 + z7
    A00, A01, A11 = z0 + z1 + z2 + za, z0 + z1 + za, z0 + z1 + z3 + za + zb
    adj = sp.Matrix([[A11, -A01], [-A01, A00]])
    U = sp.expand(A00 * A11 - A01 ** 2)
    sig = [(adj[s, 0] + adj[s, 1]) * z0 / U for s in range(2)]
    tau = [(adj[s, 0] * (z1 + z2) + adj[s, 1] * (z1 - z3)) / U for s in range(2)]
    albe = {al[0]: 1 + S1, be[0]: 1 + T1, al[1]: 1 - S0, be[1]: 1 - T0, al[2]: 1 - S0 - S1,
            be[2]: 1 - T0 - T1, al[3]: 1 - S0 - S1, be[3]: -T0 - T1}
    avec = {0: [0, -1], 1: [1, 0], 2: [1, 1], 3: [1, 1]}
    W = (z2 + z3 + zb) * (z0 + z1) + z2 * zb
    rep = {'zo': z0 + z1, 'z1': z1, 'y3': z2, 'y4': z3, 'za': za, 'zb': zb}
else:
    import cm_planar as CM
    P, PS, ER = CM.PR, CM.PR.contract(), CM.ER
    Ek = {k: ER[3 - k] for k in range(4)}
    v = {'T1': pp(P, Hf(Ek[3], Ek[2]), Ek[1], Ek[0]), '01': pp(P, Hf(Ek[3], Ek[2]), I1, I1),
         '02a': pp(P, Hf(Ek[3], I1), Ek[1].gam(), I1), '02b': pp(P, Hf(Ek[3], I1), I1, Ek[1]),
         '02c': pp(P, Hf(Ek[3], Ek[1]), I1, I1), '02d': pw(P, I1, Ek[3] * Ek[1].gam()),
         '03a': pp(PS, Hf(I1, Ek[2]), Ek[1], I1), '03b': pw(P, Ek[2].gam() * Ek[1], I1),
         '03c': pw(PS, Ek[2] * Ek[1].gam(), I1), '03d': pw(PS, Ek[2], Ek[1]), '12': pp(P, Hf(Ek[3], I1), I1, Ek[0]),
         '13a': pp(P, GL.mulRight(Ek[2]).contract().contract(), I1, Ek[0]), '13b': pp(P, GL.mulRight(Ek[2]), I1, Ek[0]),
         '23': pp(P, GL, Ek[1], Ek[0])}
    t1 = -v['T1']
    piece = {(0, 1): -2 * v['01'], (0, 2): -(v['02a'] + 2 * v['02b'] + 2 * v['02c'] + 4 * v['02d']),
             (0, 3): -(v['03a'] + 4 * v['03b'] + 2 * v['03c'] + 4 * v['03d']), (1, 2): -2 * v['12'],
             (1, 3): -(-v['13a'] + 8 * v['13b']), (2, 3): -4 * v['23']}
    # y4 = z0, y3 = z1, outer z2 + z3 (split z2), za = z5 + z7, zb = z4 + z6
    A00, A01, A11 = z0 + z1 + zb, -(z0 + zb), z0 + z2 + z3 + zb + za
    adj = sp.Matrix([[A11, -A01], [-A01, A00]])
    U = sp.expand(A00 * A11 - A01 ** 2)
    sig = [(adj[s, 0] * (z0 + z1) + adj[s, 1] * (z2 - z0)) / U for s in range(2)]
    tau = [adj[s, 1] * z3 / U for s in range(2)]
    albe = {al[0]: 1 - S1, be[0]: 1 - T1, al[1]: 1 - S1, be[1]: -T1, al[2]: 1 - S0, be[2]: -T0,
            al[3]: 1 - S0 + S1, be[3]: -T0 + T1}
    avec = {0: [0, 1], 1: [0, 1], 2: [1, 0], 3: [1, -1]}
    W = z1 * zb + (z1 + z0 + zb) * (z2 + z3)
    rep = {'zo': z2 + z3, 'z2': z2, 'y3': z1, 'y4': z0, 'za': za, 'zb': zb}
Sv = {S0: sig[0] + tau[0], S1: sig[1] + tau[1], T0: tau[0], T1: tau[1]}
Ainv = adj / U
C = {(k, l): sp.cancel(sum(avec[k][s] * Ainv[s, t] * avec[l][t] for s in range(2) for t in range(2)))
     for k in range(4) for l in range(k + 1, 4)}
Phi1 = sp.expand(t1.subs(albe))
Phi2 = sp.expand(sum(C[kl] * p.subs(albe) for kl, p in piece.items()))
N1 = sp.factor(sp.cancel(Phi1.subs(Sv) * U ** 4))
N2 = sp.factor(sp.cancel(Phi2.subs(Sv) * U ** 3))
M1 = sp.cancel(N1 / (512 * W)); M2 = sp.cancel(N2 / (-1024))
print(name, 'M1 polynomial:', sp.denom(sp.together(M1)) == 1, ' M2 polynomial:', sp.denom(sp.together(M2)) == 1)
R = S.grouped(name, S.main(name))
g = {k: sp.Symbol(k) for k in rep}
sub = {g[k]: val for k, val in rep.items()}
print(name, 'R1 - 6 N1/(1024 U^6) =', sp.simplify(R[0].subs(sub) - 6 * N1 / (1024 * U ** 6)))
print(name, 'R2 - N2/(1024 U^5) =', sp.simplify(R[1].subs(sub) - N2 / (1024 * U ** 5)))
