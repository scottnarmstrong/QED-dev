import sympy as sp, pickle
u=sp.symbols('u',positive=True)
H,rho,K,pref=pickle.load(open('gen1.pkl','rb'))
a,s1,sm,sp_,sq=sp.symbols('a s1 sm sp sq')
for name,L1,Lm in [('ord1',u*s1,u*sm),('ord2',-u+u**2*s1,u+u**2*sm)]:
    P2=u*sp_; M2=-u*sq
    G=sum(h*a**m[0]*L1**m[1]*Lm**m[2]*P2**m[3]*M2**m[4] for m,h in H.items())
    P=sp.Poly(sp.expand(G),a,s1,sm,sp_,sq)
    bad=[]
    for mon,cf in P.as_dict().items():
        cf=sp.factor(sp.together(cf))
        o=sp.limit(cf*u**0,u,0)
        n,d=sp.fraction(cf)
        ordn=min(t[0][0] for t in sp.Poly(sp.expand(n),u).terms()); ordd=min(t[0][0] for t in sp.Poly(sp.expand(d),u).terms())
        if (ordn-ordd<1 and any(mon)) or ordn-ordd<0: bad.append((mon,ordn-ordd))
    print(name,bad)
