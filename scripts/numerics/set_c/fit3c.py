from fitH import *
import pickle
R=sp.Rational
Hd,N=pickle.load(open('red2.pkl','rb'))
names=['L0','L1','Lm']
def monH(m):
    F=ONE
    for k,nmx in zip(m[:3],names):
        for _ in range(k): F=mul(F,LOG[nmx])
    for _ in range(m[3]): F=mul(F,LiH(2,u))
    for _ in range(m[4]): F=mul(F,LiH(2,-u))
    return F
div={(0,(1,0,0,0,0)),(0,(0,0,0,0,0)),(1,(0,0,0,0,0))}
w4={(0,(1,0,0,0,1)),(0,(1,0,0,1,0)),(0,(2,0,1,0,0)),(0,(2,1,0,0,0))}
T={}
g3terms=[]
for (a,m),c in N.items():
    if (a,m) in div or (a,m) in w4: continue
    g3terms.append((a,m,c))
    M=monH(m)
    if a==0: T=add(T,scal(c,prepend(0,M)))
    elif a==-1: T=add(T,scal(c,prepend(-1,M)))
    else: T=add(T,scal(-c,prepend(1,M)))
pickle.dump(g3terms,open('g3terms.pkl','wb'))
def build(S3,S2,L3):
    B={}
    for f in S3: B[f'P3[{f}]']=add(LiH(3,f),scal(-1,mul(logH(f),LiH(2,f))))
    for f in L3: B[f'Li3[{f}]']=LiH(3,f)
    LG=['L0','L1','Lm','l2']
    for g in S2:
        for a in LG: B[f'Li2[{g}]*{a}']=mul(LiH(2,g),LOG[a])
        B[f'Li2[{g}]']=LiH(2,g)
    for k in (1,2,3):
        for m in itertools.combinations_with_replacement(LG,k):
            if all(x=='l2' for x in m): continue
            F=ONE
            for x in m: F=mul(F,LOG[x])
            B['*'.join(m)]=F
    for a in LG: B[f'z2*{a}']=scal(z2,LOG[a])
    return B
S=[u,-u,1-u,1/(1+u),u/(1+u),(1-u)/(1+u),-(1-u)/(1+u),(1+u)/2,(1-u)/2,2*u/(1+u),u**2,1-u**2]
S3=list(S); S2=[u,-u,(1-u)/2]; L3=[u,-u]
s=solve(build(S3,S2,L3),T); print('solvable',s is not None)
for f in list(S3):
    t=[g for g in S3 if g!=f]
    if solve(build(t,S2,L3),T) is not None: S3=t
for f in list(S2):
    t=[g for g in S2 if g!=f]
    if solve(build(S3,t,L3),T) is not None: S2=t
print(S3,S2)
s=solve(build(S3,S2,L3),T); print(len(s))
for k,v in s.items(): print(k,v)
pickle.dump((S3,S2,s),open('g3sol.pkl','wb'))
