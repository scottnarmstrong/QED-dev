import sympy as sp, pickle
u=sp.symbols('u',positive=True)
H,rho,K,pref=pickle.load(open('gen1.pkl','rb'))
a,s1,sm,sp_,sq=sp.symbols('a s1 sm sp sq')
L1=-u-u**2/2+u**3*s1; Lm=u-u**2/2+u**3*sm; P2=u*sp_; M2=-u*sq
G=sum(h*a**m[0]*L1**m[1]*Lm**m[2]*P2**m[3]*M2**m[4] for m,h in H.items())
P=sp.Poly(sp.expand(G),a,s1,sm,sp_,sq)
res={}
for mon,cf in P.as_dict().items():
    cf=sp.factor(sp.together(cf))
    res[mon]=cf
    n,d=sp.fraction(cf)
    ordn=min(t[0][0] for t in sp.Poly(sp.expand(n),u).terms()); ordd=min(t[0][0] for t in sp.Poly(sp.expand(d),u).terms())
    print(mon, 'ord', ordn-ordd)
lim=sum(sp.limit(cf,u,0)*sp.Integer(1)*(sp.Rational(-1,3))**mon[1]*(sp.Rational(1,3))**mon[2] for mon,cf in res.items() if mon[0]==0)
print('lim',lim, sp.Rational(-4619,432))
print(len(res))
