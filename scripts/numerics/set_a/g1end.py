import sympy as sp, pickle
u=sp.symbols('u',positive=True)
H,N=pickle.load(open('red2.pkl','rb'))
pi=sp.pi; l2=sp.log(2)
at1={'L0':0,'Lm':l2,'P2':pi**2/6,'M2':-pi**2/12}
tot=0
for m,q in H.items():
    if m[1]>0:
        assert sp.factor(q).subs(u,1)==0; continue
    v=q.subs(u,1)*0**m[0] if m[0]>0 else q.subs(u,1)
    v=v*at1['Lm']**m[2]*at1['P2']**m[3]*at1['M2']**m[4]
    tot+=v
# low prims at 1: L0->0, Lm->l2, L0^2/2->0, L0Lm+Li2(-u) -> -pi^2/12, -Li2(u) -> -pi^2/6, Lm^2/2 -> l2^2/2, -Li2(-u)->pi^2/12
prim1={(0,(0,0,0,0,0)):0, (-1,(0,0,0,0,0)):l2, (0,(1,0,0,0,0)):0, (-1,(1,0,0,0,0)):-pi**2/12,
      (0,(0,1,0,0,0)):-pi**2/6, (-1,(0,0,1,0,0)):l2**2/2, (0,(0,0,1,0,0)):pi**2/12}
for k,c in N.items():
    if k in prim1: tot+=c*prim1[k]
tot=sp.expand(tot)
print('G1(1)=',tot)
print('G1(1)-G1(0)=',sp.expand(tot+sp.Rational(4619,432)))
