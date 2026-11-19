import sympy as sp, pickle
u=sp.symbols('u')
H,N=pickle.load(open('red2.pkl','rb'))
names=['L0','L1','Lm','P2','M2']
for m,q in H.items():
    s=sp.series(q,u,0,1).removeO()
    pp=sum(s.coeff(u,-k)*u**-k for k in (1,2,3))
    print([f'{n}^{k}' for n,k in zip(names,m) if k], ' pp=',pp, ' val0=', sp.limit(q-pp,u,0))
