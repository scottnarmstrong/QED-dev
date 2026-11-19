from fitH import *
L0H,L1H,LmH=LOG['L0'],LOG['L1'],LOG['Lm']
R=sp.Rational
def build3(S3,S2,Li3plain):
    B={}
    for f in S3: B[f'P3[{f}]']=add(LiH(3,f),scal(-1,mul(logH(f),LiH(2,f))))
    for f in Li3plain: B[f'Li3[{f}]']=LiH(3,f)
    LG=['L0','L1','Lm','l2']
    for g in S2:
        for a in LG: B[f'Li2[{g}]*{a}']=mul(LiH(2,g),LOG[a])
    for m in itertools.combinations_with_replacement(LG,3):
        if all(x=='l2' for x in m): continue
        F=ONE
        for x in m: F=mul(F,LOG[x])
        B['*'.join(m)]=F
    for a in LG: B[f'z2*{a}']=scal(z2,LOG[a])
    return B
P2=LiH(2,u); M2=LiH(2,-u)
form0=add(scal(R(-100,9),mul(L0H,L1H)),scal(-6,mul(L0H,LmH)),scal(R(28,3),mul(L1H,LmH)),scal(4,mul(LmH,LmH)),scal(R(176,9),add(P2,scal(R(1,2),M2))))
formm=add(scal(R(4,9),mul(L0H,L0H)),scal(R(-20,3),mul(L0H,L1H)),scal(R(-8,3),mul(L0H,LmH)),scal(R(-176,9),add(P2,scal(R(1,2),M2))))
T=add(prepend(0,form0),prepend(-1,formm))
S=[u,-u,1-u,1/(1+u),u/(1+u),(1-u)/(1+u),-(1-u)/(1+u),(1+u)/2,(1-u)/2,2*u/(1+u),u**2,1-u**2]
s=solve(build3(S,S,[u,-u]),T); print(s is not None)
def solvable(S3,S2,L3): return solve(build3(S3,S2,L3),T) is not None
S3=list(S); S2=list(S); L3=[u,-u]
for f in list(S3):
    t=[g for g in S3 if g!=f]
    if solvable(t,S2,L3): S3=t
for f in list(S2):
    t=[g for g in S2 if g!=f]
    if solvable(S3,t,L3): S2=t
print(S3,S2)
s=solve(build3(S3,S2,L3),T); print(len(s)); print(s)
import pickle; pickle.dump(s,open('g3sol.pkl','wb'))
