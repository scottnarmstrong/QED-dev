#!/usr/bin/env python3
"""The rational identities of c2[T1], c2[T2] of S+ (QED/TwoLoop/UnitSCGraphSpMain.lean), from the
planar pieces of planar_patterns.py, in exact arithmetic. NOT a proof. Run: nice -n 10 python3 sp_identities.py.
"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sympy as sp
import planar_patterns as PP
z = sp.symbols('z0:8')
zo = z[0]+z[1]+z[3]; Y = z[2]; za = z[4]+z[6]; zb = z[5]+z[7]
A00 = zo+za+Y; A01 = zo+za; A11 = zo+za+zb
U = sp.expand(A00*A11 - A01**2)
Ui = sp.Matrix([[A11, -A01],[-A01, A00]])/U
sig = [z[0]*(Ui[s,0]+Ui[s,1]) for s in range(2)]
tau = [Ui[s,0]*(z[1]+z[2]+z[3]) + Ui[s,1]*(z[1]+z[3]) for s in range(2)]
X = sig[0]+tau[0]; W = sig[0]+sig[1]+tau[0]+tau[1]; T = tau[0]+tau[1]; T0 = tau[0]
al = PP.al; be = PP.be
sub = {al[0]: 1-W, be[0]: 1-T, al[1]: 1-X, be[1]: 1-T0, al[2]: 1-W, be[2]: 1-T, al[3]: 1-W, be[3]: -T}
p1, p2, p4 = PP.Sp_pieces()
poly1 = sp.expand(p1/(-3072))
s_ = Y+zb; c = Y*zb; a = s_*zo + c
print('poly1 =', poly1)
d1 = sp.simplify(sp.together(poly1.subs(sub) - za*s_*a**2*(2*U+za*zb)/U**4))
print('T1 identity:', d1)
C = {(0,1): zb/U, (0,2): s_/U, (0,3): s_/U, (1,2): zb/U, (1,3): zb/U, (2,3): s_/U}
t2 = sum(C[k]*v.subs(sub) for k, v in p2.items())
d2 = sp.simplify(sp.together(t2 - 2048*za*s_*(3*Y*U + 2*s_*za*zb)/U**3))
print('T2 identity:', d2)
print('U =', sp.factor(U))
for k,v in p2.items(): print(k, sp.expand(v))
print('X,W,T,T0 =', [sp.factor(sp.together(e)) for e in (X,W,T,T0)])
Ws, Xs, Ts, T0s = sp.symbols('W X T T0')
subS = {al[0]: 1-Ws, be[0]: 1-Ts, al[1]: 1-Xs, be[1]: 1-T0s, al[2]: 1-Ws, be[2]: 1-Ts, al[3]: 1-Ws, be[3]: -Ts}
Phi1 = sp.expand(poly1.subs(subS))
print('Phi1 =', Phi1)
c01, c02 = sp.symbols('c01 c02')   # c01 = zb/U, c02 = s/U
Cs = {(0,1): c01, (0,2): c02, (0,3): c02, (1,2): c01, (1,3): c01, (2,3): c02}
Phi2 = sp.expand(sum(Cs[k]*v.subs(subS) for k, v in p2.items()))
print('Phi2 =', Phi2)
for k, v in p2.items(): print('piece', k, sp.expand(v.subs(subS)))
