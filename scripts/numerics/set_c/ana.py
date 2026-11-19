import sympy as sp, pickle, itertools
u=sp.symbols('u',positive=True)
terms=pickle.load(open('terms.pkl','rb'))
H,N=pickle.load(open('red2.pkl','rb'))
G=dict(H)
def addc(m,c): G[m]=sp.cancel(G.get(m,0)+c)
addc((2,0,0,0,0),sp.Rational(9,4)); addc((1,0,0,0,0),sp.Rational(77,216)); addc((0,1,0,0,0),-sp.Rational(133,72))
pickle.dump(G,open('G.pkl','wb'))
y,a=sp.symbols('y a')
def T_log1m(z,N): return -sum(z**n/sp.Integer(n) for n in range(1,N+1))
def T_li2(z,N): return sum(z**n/sp.Integer(n)**2 for n in range(1,N+1))
def near0(F,N):
    r=sp.symbols('r1:6')
    L1=T_log1m(y,N)+y**(N+1)*r[0]; L2=T_log1m(-y,N)+y**(N+1)*r[1]
    D1=T_li2(y,N)+y**(N+1)*r[2]; D2=T_li2(-y,N)+y**(N+1)*r[3]
    at=[a,L1,L2,D1,D2]
    E=sum(c.subs(u,y)*sp.prod([v**e for v,e in zip(at,m)]) for m,c in F.items())
    return sp.Poly(sp.expand(E),a,*r[:4])
def near1(F,N):
    s=sp.symbols('s1:6'); l2,pi2=sp.symbols('l2 pi2')
    L0=T_log1m(y,N)+y**(N+1)*s[0]
    L2=l2+T_log1m(y/2,N)+y**(N+1)*s[1]
    Li2y=T_li2(y,N)+y**(N+1)*s[2]
    w=y*(2-y)
    Li2w=T_li2(w,N)+y**(N+1)*s[3]
    L1=a
    D1=pi2/6-a*L0-Li2y
    D2=-pi2/12-L0*L2-Li2w/2+Li2y
    at=[L0,L1,L2,D1,D2]
    E=sum(c.subs(u,1-y)*sp.prod([v**e for v,e in zip(at,m)]) for m,c in F.items())
    return sp.Poly(sp.expand(E),a,*s[:4])
def order(c):
    c=sp.factor(sp.together(c))
    if c==0: return 99
    n,d=sp.fraction(c)
    return sp.Poly(n,y).as_dict() and min(k[0] for k in sp.Poly(n,y).as_dict()) - (min(k[0] for k in sp.Poly(d,y).as_dict()))
import sys
which=sys.argv[1]; N=int(sys.argv[2])
F={'G':G,'J':terms}[which[0]]
P=(near0 if which[1]=='0' else near1)(F,N)
worst={}
for mon,c in P.as_dict().items():
    o=order(c)
    worst[mon]=o
bad=[(m,o) for m,o in worst.items() if o<1 and any(m)]
print(which,N,'min order over non-const monomials',min(o for m,o in worst.items() if any(m)),'const order',worst.get((0,)*5))
print('nonconst monomials with order<1:',bad[:10])
