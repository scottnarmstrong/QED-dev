import sympy as sp, pickle
u=sp.symbols('u',positive=True)
terms=pickle.load(open('terms.pkl','rb'))
names=['L0','L1','Lm','P2','M2']; wt=[1,1,1,2,2]
# derivative of each basic: list of (rational, monomial-exponent-vector)
def e(i,k=1):
    v=[0]*5; v[i]=k; return tuple(v)
Z=(0,0,0,0,0)
dbase={0:[(1/u,Z)],1:[(1/(u-1),Z)],2:[(1/(u+1),Z)],3:[(-1/u,e(1))],4:[(-1/u,e(2))]}
def dmon(m):
    out={}
    for i,k in enumerate(m):
        if k==0: continue
        rest=list(m); rest[i]-=1
        for r,mm in dbase[i]:
            new=tuple(a+b for a,b in zip(rest,mm))
            out[new]=sp.cancel(out.get(new,0)+k*r)
    return out
def weight(m): return sum(a*b for a,b in zip(m,wt))
target={m:sp.cancel(c) for m,c in terms.items()}
H={}; N={}
while target:
    m=max(target,key=weight)
    R=target.pop(m)
    if R==0: continue
    pf=sp.Add.make_args(sp.apart(R,u)); rest=0
    for p in pf:
        done=False
        for a in (0,-1,1):
            c=sp.cancel(p*(u-a))
            if c.is_number:
                N[(a,m)]=N.get((a,m),0)+c; done=True; break
        if not done: rest+=p
    if rest!=0:
        Q=sp.integrate(rest,u); assert not Q.has(sp.log)
        if m[1]>0:
            q1=sp.limit(Q,u,1)
            if q1.is_finite: Q=Q-q1
        Q=sp.factor(Q)
        H[m]=Q
        for mm,r in dmon(m).items():
            target[mm]=sp.cancel(target.get(mm,0)-Q*r)
for m,q in sorted(H.items(),key=lambda t:-weight(t[0])):
    print('H',[f"{n}^{k}" for n,k in zip(names,m) if k], q)
for (a,m),c in sorted(N.items(),key=lambda t:-weight(t[0][1])):
    print('N',a,[f"{n}^{k}" for n,k in zip(names,m) if k], c)
pickle.dump((H,N),open('red2.pkl','wb'))
