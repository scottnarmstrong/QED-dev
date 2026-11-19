from hpl import *
import itertools, sys, pickle
from sympy.polys.matrices import DomainMatrix
from sympy import QQ
S4=[u,-u,1-u,1/(1+u),u/(1+u),(1-u)/(1+u),-(1-u)/(1+u),(1+u)/2,(1-u)/2,2*u/(1+u),u**2,1-u**2,((1-u)/(1+u))**2,4*u/(1+u)**2]
S2=[u,-u,1-u,1/(1+u),u/(1+u),(1-u)/(1+u),-(1-u)/(1+u),(1+u)/2,(1-u)/2,2*u/(1+u)]
LG=['L0','L1','Lm','l2']
def build(S4=S4,S2=S2,li3free=True):
    B={}
    for f in S4:
        if li3free:
            B[f'P4[{f}]']=add(LiH(4,f),scal(-1,mul(logH(f),LiH(3,f))))
            B[f'l2*Li3[{f}]']=scal(l2,LiH(3,f))
        else:
            B[f'Li4[{f}]']=LiH(4,f)
            for g in LG: B[f'Li3[{f}]*{g}']=mul(LiH(3,f),LOG[g])
    for g in S2:
        for a,b in itertools.combinations_with_replacement(LG,2):
            B[f'Li2[{g}]*{a}*{b}']=mul(LiH(2,g),mul(LOG[a],LOG[b]))
        B[f'z2*Li2[{g}]']=scal(z2,LiH(2,g))
    for g,h in itertools.combinations_with_replacement(S2,2):
        B[f'Li2[{g}]*Li2[{h}]']=mul(LiH(2,g),LiH(2,h))
    for m in itertools.combinations_with_replacement(LG,4):
        if all(x=='l2' for x in m): continue
        F=ONE
        for x in m: F=mul(F,LOG[x])
        B['*'.join(m)]=F
    for a,b in itertools.combinations_with_replacement(LG,2):
        B[f'z2*{a}*{b}']=mul(const(z2),mul(LOG[a],LOG[b]))
    for a in LG: B[f'z3*{a}']=scal(z3,LOG[a])
    return B
def rows_of(F):
    out={}
    for w,c in F.items():
        if w==(): continue
        P=sp.Poly(c,z2,z3,l2,L4h,z5)
        for mon,cc in zip(P.monoms(),P.coeffs()):
            out[(w,mon)]=cc
    return out
def solve(B,T):
    keys=list(B)
    cols=[rows_of(B[k]) for k in keys]
    rhs=rows_of(T)
    rowkeys=sorted(set().union(*[set(c) for c in cols],set(rhs)),key=str)
    ri={r:i for i,r in enumerate(rowkeys)}
    n=len(keys)
    M=[[QQ(0)]*(n+1) for _ in rowkeys]
    for j,c in enumerate(cols):
        for r,v in c.items(): M[ri[r]][j]=QQ.from_sympy(v)
    for r,v in rhs.items(): M[ri[r]][n]=QQ.from_sympy(v)
    dm=DomainMatrix(M,(len(rowkeys),n+1),QQ)
    R,piv=dm.rref()
    if n in piv: return None
    R=R.to_Matrix()
    sol={}
    for i,p in enumerate(piv):
        v=R[i,n]
        if v!=0: sol[keys[p]]=v
    return sol
