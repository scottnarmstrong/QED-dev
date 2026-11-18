#!/usr/bin/env python3
"""The C- coefficients through the reversal cmw(P; Y) = -cpw(P^R; Y3^R, Y2^R, Y1^R, Y0^R) of
QED/TwoLoop/UnitSCGraphCmTrace.lean, evaluated on the planar jets, against the exact 4x4 traces of
symbolic_c2.py. NOT a proof. Run: nice -n 10 python3 cm_planar.py (~10 s).
"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sympy as sp
from planar_patterns import Pl, PJ, c, ONE, G0, G1, G0L, Fam, P0, pw, al, be, E, I1
import cp_planar as CP
import symbolic_c2 as S
def revPl(x): return Pl(x.v[0], -x.v[1], -x.v[2], -x.v[3])
def rev(x): return PJ(*[revPl(t) for t in x.j])
def revR(x):  # -bar(rev R)
    return PJ(*[Pl(-t.v[0], -t.v[1], -t.v[2], t.v[3]) for t in x.j])
PR = Fam(rev(P0.q0), rev(P0.q1), revR(P0.r))
ER = [rev(E[3]), rev(E[2]), rev(E[1]), rev(E[0])]
def pieces(k=2):
    P = PR; PS = PR.contract(); e = ER
    pp, Hf, Kf, GL = CP.pp, CP.Hf, CP.Kf, CP.GL
    cp = {
      (0,1): 4 * pp(P, GL, e[2], e[3], k),
      (0,2): pp(P, Kf(e[1]), I1, e[3], k),
      (0,3): 4 * pw(P, e[1].gam() * e[2], I1, k) + pp(PS, Hf(I1, e[1]), e[2], I1, k) - 2 * pw(PS.mulRight(e[1]).contract(), e[2], I1, k),
      (1,2): 2 * pp(P, Hf(e[0], I1), I1, e[3], k),
      (1,3): pp(P, Hf(e[0], I1), e[2].gam(), I1, k) + 2 * pp(P, Hf(e[0], I1), I1, e[2], k) + 2 * pp(P, Hf(e[0], e[2]), I1, I1, k) + 4 * pw(P, I1, e[0] * e[2].gam(), k),
      (2,3): 2 * pp(P, Hf(e[0], e[1]), I1, I1, k)}
    t1 = -6 * pp(P, Hf(e[0], e[1]), e[2], e[3], k)
    two = {(k_, l_): -cp[(3 - l_, 3 - k_)] for (k_, l_) in cp}
    four = {(0,1,2,3): -8 * pp(P, GL, I1, I1, k), (0,2,1,3): -(8 * pp(P, GL, I1, I1, k) - 48 * pw(P, I1, I1, k)),
            (0,3,1,2): -(-8 * pp(P, GL, I1, I1, k) - 16 * pw(P, I1, I1, k))}
    return t1, two, four
a2, b2, Cs, t1, t2, t3 = S.coefficients('Cm')
p1, p2, p4 = pieces()
rep = {a2[k]: al[k] for k in range(4)}; rep.update({b2[k]: be[k] for k in range(4)})
T2 = sum(sp.Symbol(f'C{k}{l}') * v for (k, l), v in p2.items())
T3 = sum(sp.Symbol(f'C{a}{b}') * sp.Symbol(f'C{cc}{d}') * v / 4 for (a, b, cc, d), v in p4.items())
print('T1 match', sp.expand(t1.subs(rep) - p1) == 0, 'T2 match', sp.expand(t2.subs(rep) - T2) == 0, 'T3', sp.expand(t3.subs(rep) - T3) == 0)
for kk in (0, 1):
    q1, q2, q4 = pieces(kk)
    print('order', kk, q1 == 0, all(v == 0 for v in q2.values()), all(v == 0 for v in q4.values()))
print('T1 piece', sp.factor(p1))
for kl, v in p2.items(): print('piece', kl, sp.factor(v))
