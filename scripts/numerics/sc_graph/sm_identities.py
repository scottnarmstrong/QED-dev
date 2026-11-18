#!/usr/bin/env python3
"""The rational identities of c2[T1], c2[T2] of S- (QED/TwoLoop/UnitSCGraphSmMain.lean), from the
planar pieces of planar_patterns.py, in exact arithmetic. NOT a proof. Run: nice -n 10 python3 sm_identities.py.
"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sympy as sp
import planar_patterns as PP
z = sp.symbols('z0:8')
zo = z[0]+z[2]+z[3]; Y = z[1]; za = z[4]+z[6]; zb = z[5]+z[7]
A00 = zo+Y+za; A01 = -Y; A11 = Y+zb
U = sp.expand(A00*A11 - A01**2)
Ui = sp.Matrix([[A11, -A01],[-A01, A00]])/U
sig = [Ui[s,0]*(z[0]+z[1]+z[2]) + Ui[s,1]*(-z[1]) for s in range(2)]
tau = [Ui[s,0]*z[3] for s in range(2)]
X = sig[0]+tau[0]; V = sig[0]-sig[1]+tau[0]-tau[1]; T0 = tau[0]; T = tau[0]-tau[1]
al = PP.al; be = PP.be
sub = {al[0]: 1-X, be[0]: 1-T0, al[1]: 1-X, be[1]: -T0, al[2]: 1-V, be[2]: -T, al[3]: 1-X, be[3]: -T0}
p1, p2, p4 = PP.Sm_pieces()
poly1 = sp.expand(p1/(-3072))
s_ = Y+zb; c = Y*zb; a = s_*zo + c
print('T1 identity:', sp.simplify(sp.together(poly1.subs(sub) - za*s_*a**2*(2*U+za*zb)/U**4)))
C = {(0,1): s_/U, (0,2): zb/U, (0,3): s_/U, (1,2): zb/U, (1,3): s_/U, (2,3): zb/U}
t2 = sum(C[k]*v.subs(sub) for k, v in p2.items())
print('T2 identity:', sp.simplify(sp.together(t2 - 2048*za*s_*(3*Y*U + 2*s_*za*zb)/U**3)))
Xs, Vs, T0s, Ts = sp.symbols('X V T0 T')
subS = {al[0]: 1-Xs, be[0]: 1-T0s, al[1]: 1-Xs, be[1]: -T0s, al[2]: 1-Vs, be[2]: -Ts, al[3]: 1-Xs, be[3]: -T0s}
print('poly1 =', poly1)
print('Phi1 =', sp.expand(poly1.subs(subS)))
c01, c02 = sp.symbols('cs cb')
Cs = {(0,1): c01, (0,2): c02, (0,3): c01, (1,2): c02, (1,3): c01, (2,3): c02}
print('Phi2 =', sp.expand(sum(Cs[k]*v.subs(subS) for k, v in p2.items())))
for k, v in p2.items(): print('piece', k, sp.factor(v))
print('X, V, T0, T =', [sp.factor(sp.together(e*U)) for e in (X, V, T0, T)])
