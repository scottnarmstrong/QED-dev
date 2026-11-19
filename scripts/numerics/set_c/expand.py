import sympy as sp, pickle
u=sp.symbols('u',positive=True)
y,a=sp.symbols('y a')
l2,pi2=sp.symbols('l2 pi2')
rA,rB,rC,rD=sp.symbols('rA rB rC rD')
rA2,rCw=sp.symbols('rA2 rCw')
R0=[rA,rB,rC,rD]; R1=[rA,rA2,rC,rCw]
def expand(F,end,hsym=None):
    """returns dict K=(j, rexps...) -> (coef_rational(y), coef_with_hsym)"""
    if end==0:
        L0=a; L1=-y-y**2/2+y**3*rA; L2=y-y**2/2+y**3*rB
        D1=y+y**2/4+y**3*rC; D2=-y+y**2/4+y**3*rD; R=R0; pt=y
    else:
        L0=-y-y**2/2+y**3*rA; L1=a; L2=l2-y/2-y**2/8+(y/2)**3*rA2
        Li2y=y+y**2/4+y**3*rC; w=y*(2-y); Li2w=w+w**2/4+w**3*rCw
        D1=pi2/6-a*L0-Li2y; D2=-pi2/12-L0*L2-Li2w/2+Li2y; R=R1; pt=1-y
    at=[L0,L1,L2,D1,D2]
    E=0; Es=0
    for m,c in F.items():
        mon=sp.prod([v**e for v,e in zip(at,m)])
        E+=c.subs(u,pt)*mon
        if hsym: Es+=hsym[m]*mon
    P=sp.Poly(sp.expand(E),a,*R)
    out={}
    Ps=sp.Poly(sp.expand(Es),a,*R).as_dict() if hsym else {}
    for K,c in P.as_dict().items():
        out[K]=(sp.factor(sp.together(c)), Ps.get(K,0))
    for K in Ps:
        if K not in out: out[K]=(0,Ps[K])
    return out
