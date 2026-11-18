#!/usr/bin/env python3
"""The planar evaluation of the C+ reductions of QED/TwoLoop/UnitSCGraphCpTrace.lean (pattern pp of
QED/TwoLoop/UnitSCGraphCross.lean, families H, K) on the second-order jets of the planar data, against
the exact 4x4 traces of symbolic_c2.py. NOT a proof. Run: nice -n 10 python3 cp_planar.py (~10 s).
"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sympy as sp
from planar_patterns import Pl, PJ, c, ONE, ZERO, G0, G1, G0L, qJ0, qJ1, rJ, eJ, Fam, P0, pw, al, be, E, I1
import symbolic_c2 as S
GL = Fam(c(G0L), c(G1), c(ONE))   # gamma_nu lower family
def addF(F, G, k=1): return Fam(F.q0 + G.q0.sc(k), F.q1 + G.q1.sc(k), F.r + G.r.sc(k))
def scF(F, k): return Fam(F.q0.sc(k), F.q1.sc(k), F.r.sc(k))
def Hf(y0, y1): return GL.mulLeft(y0).mulRight(y1).contract()
def Kf(y1):
    F = GL.mulRight(y1)
    return addF(scF(F.contract().contract(), -1), F, 8)
def pp(P, H, w, z, k=2):
    gs = [c(G0), c(G1)]
    A = [H.q0, H.q1]; Q = [P.q0, P.q1]
    t = 0
    for m in range(2):
        for n in range(2):
            t += 4 * (A[n] * w * gs[m] * z * gs[n] * Q[m]).j[k].s
    for m in range(2):
        t -= 8 * (H.r * (w * gs[m] * z).bar() * Q[m]).j[k].s
    for n in range(2):
        t -= 8 * (A[n] * w * (z * gs[n] * P.r).bar()).j[k].s
    return sp.expand(t)
def Cp_pieces(k=2):
    P = P0; PS = P0.contract()
    t1 = 6 * pp(P, Hf(E[0], E[1]), E[2], E[3], k)
    two = {
      (0,1): 4 * pp(P, GL, E[2], E[3], k),
      (0,2): pp(P, Kf(E[1]), I1, E[3], k),
      (0,3): 4 * pw(P, E[1].gam() * E[2], I1, k) + pp(PS, Hf(I1, E[1]), E[2], I1, k) - 2 * pw(PS.mulRight(E[1]).contract(), E[2], I1, k),
      (1,2): 2 * pp(P, Hf(E[0], I1), I1, E[3], k),
      (1,3): pp(P, Hf(E[0], I1), E[2].gam(), I1, k) + 2 * pp(P, Hf(E[0], I1), I1, E[2], k) + 2 * pp(P, Hf(E[0], E[2]), I1, I1, k) + 4 * pw(P, I1, E[0] * E[2].gam(), k),
      (2,3): 2 * pp(P, Hf(E[0], E[1]), I1, I1, k),
    }
    four = {(0,1,2,3): 8 * pp(P, GL, I1, I1, k), (0,2,1,3): 8 * pp(P, GL, I1, I1, k) - 48 * pw(P, I1, I1, k),
            (0,3,1,2): -8 * pp(P, GL, I1, I1, k) - 16 * pw(P, I1, I1, k)}
    return t1, two, four
if __name__ == '__main__':
    name = sys.argv[1] if len(sys.argv) > 1 else 'Cp'
    a2, b2, Cs, t1, t2, t3 = S.coefficients(name)
    p1, p2, p4 = Cp_pieces()
    rep = {a2[k]: al[k] for k in range(4)}; rep.update({b2[k]: be[k] for k in range(4)})
    T2 = sum(sp.Symbol(f'C{k}{l}') * v for (k, l), v in p2.items())
    T3 = sum(sp.Symbol(f'C{a}{b}') * sp.Symbol(f'C{cc}{d}') * v / 4 for (a, b, cc, d), v in p4.items())
    print('T1 match', sp.expand(t1.subs(rep) - p1) == 0, 'T2 match', sp.expand(t2.subs(rep) - T2) == 0, 'T3', sp.expand(t3.subs(rep) - T3) == 0)
    for kk in (0, 1):
        q1, q2, q4 = Cp_pieces(kk)
        print('order', kk, q1 == 0, all(v == 0 for v in q2.values()), all(v == 0 for v in q4.values()))
    print('T1 piece', sp.factor(p1))
    for kl, v in p2.items(): print('piece', kl, sp.factor(v))
    for kl, v in p4.items(): print('four', kl, v)
