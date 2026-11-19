import sympy as sp, pickle, re
exec(open('gen1lean.py').read().split("out=[]")[0])
H,rho,K,pref=pickle.load(open('gen1.pkl','rb'))
ms=sorted(H.keys(), reverse=True)
a,b,c,p,q,iu,im,ip=sp.symbols('a b c p q iu im ip')
AT=[a,b,c,p,q]
LA=['log x','log (1 - x)','log (1 + x)','Li 2 x','Li 2 (-x)']
def monexpr(m): return a**m[0]*b**m[1]*c**m[2]*p**m[3]*q**m[4]
def monlean(m,var='x'):
    fs=[]
    for e,s in zip(m,LA):
        s=s.replace('x',var) if var!='x' else s
        if e==1: fs.append(s)
        elif e>1: fs.append(f'{s} ^ {e}')
    return ' * '.join(fs)
dA={a:iu,b:-im,c:ip,p:-b*iu,q:-c*iu}
def D(e): return sum(sp.diff(e,x)*dA[x] for x in AT)
hs={m:sp.Symbol('h'+nm(m)) for m in ms}; hds={m:sp.Symbol('hd'+nm(m)) for m in ms}
rs={m:sp.Symbol('r'+nm(m)) for m in rho}; ks={m:sp.Symbol('k'+nm(m)) for m in K}; pr=sp.Symbol('pref')
LHS=sp.expand(sum(hds[m]*monexpr(m)+hs[m]*D(monexpr(m)) for m in ms))
g3=(sp.Rational(4,9)*a*a*ip-sp.Rational(100,9)*a*b*iu-sp.Rational(20,3)*a*b*ip-6*a*c*iu-sp.Rational(8,3)*a*c*ip
    +sp.Rational(28,3)*b*c*iu+4*c*c*iu+sp.Rational(176,9)*(p+q/2)*(iu-ip))
Phi=a*(2*b+c)+4*p+2*q; psd=a*ip+c*iu-2*c*ip
RHS=sp.expand(pr*sum(rs[m]*monexpr(m) for m in rho)*sum(ks[m]*monexpr(m) for m in K)-g3+sp.Rational(8,3)*Phi*psd)
PL=sp.Poly(LHS,*AT); PR=sp.Poly(RHS,*AT)
mons=sorted(set(PL.as_dict())|set(PR.as_dict()),reverse=True)
sub={iu:sp.Symbol('IU'),im:sp.Symbol('IM'),ip:sp.Symbol('IP')}
def coef_lean(e):
    s=sp.sstr(sp.expand(e))
    for m in ms: s=re.sub(r'\bh'+nm(m)+r'\b',f'h{nm(m)} u',s); s=re.sub(r'\bhd'+nm(m)+r'\b',f'hd{nm(m)} u',s)
    for m in rho: s=re.sub(r'\br'+nm(m)+r'\b',f'r{nm(m)} u',s)
    for m in K: s=re.sub(r'\bk'+nm(m)+r'\b',f'k{nm(m)} u',s)
    s=re.sub(r'\bpref\b','pref u',s)
    s=s.replace('**',' ^ ').replace('iu','u⁻¹').replace('im','(1 - u)⁻¹').replace('ip','(1 + u)⁻¹')
    s=re.sub(r'(\d+)/(\d+)',r'(\1/\2)',s)
    return s if s else '0'
checks=[]
for mo in mons:
    cl=PL.as_dict().get(mo,0); cr=PR.as_dict().get(mo,0)
    checks.append((mo,coef_lean(cl),coef_lean(cr)))
# verify numerically coefficient identities with actual rational functions
vals={iu:1/u,im:1/(1-u),ip:1/(1+u),pr:pref}
for m in ms: vals[hs[m]]=H[m]; vals[hds[m]]=sp.diff(H[m],u)
for m in rho: vals[rs[m]]=rho[m]
for m in K: vals[ks[m]]=K[m]
bad=[mo for mo in mons if sp.simplify((PL.as_dict().get(mo,0)-PR.as_dict().get(mo,0)).subs(vals))!=0]
print('bad',bad, len(mons))
pickle.dump((mons,checks),open('checks.pkl','wb'))
