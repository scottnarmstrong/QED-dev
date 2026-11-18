#!/usr/bin/env python3
"""Numerical check, on random complex 4x4 matrices, of the Clifford reductions of the corner
contraction cpw(P; Y) = sum tr(g^n P_m g^s Y0 g_n Y1 g_s Y2 g^m Y3) used in
QED/TwoLoop/UnitSCGraphCpTrace.lean (cpw = pp(P, H(Y0, Y1); Y2, Y3) and the Wick contractions of
pairs of slots). NOT a proof. Run: nice -n 10 python3 cross_identities.py (seconds); every printed
relative difference should be ~1e-15.
"""
import numpy as np
I=1j
GAM=[np.array([[0,0,1,0],[0,0,0,1],[1,0,0,0],[0,1,0,0]],complex),
     np.array([[0,0,0,1],[0,0,1,0],[0,-1,0,0],[-1,0,0,0]],complex),
     np.array([[0,0,0,-I],[0,0,I,0],[0,I,0,0],[-I,0,0,0]],complex),
     np.array([[0,0,1,0],[0,0,0,-1],[-1,0,0,0],[0,1,0,0]],complex)]
ME=[-1,1,1,1]; GL=[ME[m]*GAM[m] for m in range(4)]; ID=np.eye(4)
rng=np.random.default_rng(1)
def R(): return rng.normal(size=(4,4))+1j*rng.normal(size=(4,4))
tr=np.trace
def Sig(X): return sum(GAM[n]@X@GL[n] for n in range(4))
def cpw(P,Y0,Y1,Y2,Y3): return sum(tr(GAM[n]@P[m]@GAM[s]@Y0@GL[n]@Y1@GL[s]@Y2@GAM[m]@Y3) for m in range(4) for n in range(4) for s in range(4))
def H(Y0,Y1): return [Sig(Y0@GL[n]@Y1) for n in range(4)]
def pp(P,Hf,W,Z): return sum(tr(Hf[n]@W@GAM[m]@Z@GAM[n]@P[m]) for m in range(4) for n in range(4))
def pw(P,W,Z): return sum(tr(P[m]@W@GAM[m]@Z) for m in range(4))
def K(Y1): return [-Sig(Sig(GL[n]@Y1))+8*GL[n]@Y1 for n in range(4)]
P=[R() for _ in range(4)]; Y=[R() for _ in range(4)]
SP=[Sig(p) for p in P]
def chk(name,a,b): print(name, abs(a-b)/max(1,abs(a)))
Y0,Y1,Y2,Y3=Y
chk('cpw=pp', cpw(P,*Y), pp(P,H(Y0,Y1),Y2,Y3))
chk('01', sum(cpw(P,GL[t],GAM[t],Y2,Y3) for t in range(4)), 4*pp(P,GL,Y2,Y3))
chk('12', sum(cpw(P,Y0,GL[t],GAM[t],Y3) for t in range(4)), 2*pp(P,H(Y0,ID),ID,Y3))
chk('23', sum(cpw(P,Y0,Y1,GL[t],GAM[t]) for t in range(4)), 2*pp(P,H(Y0,Y1),ID,ID))
chk('02', sum(cpw(P,GL[t],Y1,GAM[t],Y3) for t in range(4)), pp(P,K(Y1),ID,Y3))
SPY1=[Sig(sp@Y1) for sp in SP]
chk('03', sum(cpw(P,GL[t],Y1,Y2,GAM[t]) for t in range(4)), 4*pw(P,Sig(Y1)@Y2,ID)+pp(SP,H(ID,Y1),Y2,ID)-2*pw(SPY1,Y2,ID))
chk('13', sum(cpw(P,Y0,GL[t],Y2,GAM[t]) for t in range(4)), pp(P,H(Y0,ID),Sig(Y2),ID)+2*pp(P,H(Y0,ID),ID,Y2)+2*pp(P,H(Y0,Y2),ID,ID)+4*pw(P,ID,Y0@Sig(Y2)))
chk('0123', sum(cpw(P,GL[s],GAM[s],GL[t],GAM[t]) for s in range(4) for t in range(4)), 8*pp(P,GL,ID,ID))
chk('0312', sum(cpw(P,GL[s],GL[t],GAM[t],GAM[s]) for s in range(4) for t in range(4)), -8*pp(P,GL,ID,ID)-16*pw(P,ID,ID))
chk('0213b', sum(cpw(P,GL[s],GL[t],GAM[s],GAM[t]) for s in range(4) for t in range(4)), 8*pp(P,GL,ID,ID)-48*pw(P,ID,ID))
chk('ppK1', sum(pp(P,H(GL[s],ID),ID,GAM[s]) for s in range(4)), -4*pp(P,GL,ID,ID)-8*pw(P,ID,ID))
chk('03new', sum(cpw(P,GL[t],Y1,Y2,GAM[t]) for t in range(4)), pp(SP,H(ID,Y1),Y2,ID)+4*pw(P,Sig(Y1)@Y2,ID)+2*pw(SP,Y1@Sig(Y2),ID)+4*pw(SP,Y1,Y2))
chk('ppGL', pp(P,GL,ID,ID), 2*pw(P,ID,ID))
chk('Lstar', sum(pp(P,H(GL[s],ID),ID,GAM[s]) for s in range(4)), -16*pw(P,ID,ID))
chk('0123s', sum(cpw(P,GL[s],GAM[s],GL[t],GAM[t]) for s in range(4) for t in range(4)), 16*pw(P,ID,ID))
chk('0213s', sum(cpw(P,GL[s],GL[t],GAM[s],GAM[t]) for s in range(4) for t in range(4)), -32*pw(P,ID,ID))
chk('0312s', sum(cpw(P,GL[s],GL[t],GAM[t],GAM[s]) for s in range(4) for t in range(4)), -32*pw(P,ID,ID))
