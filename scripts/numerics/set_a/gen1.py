import sympy as sp, pickle
u=sp.symbols('u',positive=True)
H,N=pickle.load(open('red2.pkl','rb'))
H={k:sp.factor(v) for k,v in H.items()}
def add(m,c): H[m]=sp.factor(H.get(m,0)+c)
add((2,0,0,0,0),sp.Rational(-119,27)/2)
add((1,0,1,0,0),sp.Rational(1025,108)); add((0,0,0,0,1),sp.Rational(1025,108))
add((0,0,0,1,0),-sp.Rational(29,4))
add((0,0,2,0,0),-sp.Rational(16,3)/2)
add((0,0,0,0,1),-sp.Rational(41,6))
add((1,0,0,0,0),sp.Rational(11,6))
add((0,0,1,0,0),sp.Rational(43,18))
d=(1-u)/(1+u)
A=sp.Rational(11,16)+sp.Rational(11,24)*d**2-sp.Rational(7,48)*d**4
B=sp.Rational(1,2)+d**2/3-d**4/6; C=sp.Rational(1,2)-d**2/6
rho={(1,0,0,0,0):-A+3*d*C,(1,1,0,0,0):2*B,(1,0,1,0,0):B,(0,1,0,0,0):-4*d*C,(0,0,1,0,0):-2*d*C,
     (0,0,0,0,0):d*(sp.Rational(5,8)-sp.Rational(3,8)*d**2),(0,0,0,1,0):4*B,(0,0,0,0,1):2*B}
K={(0,0,0,0,0):-sp.Rational(1,2)-(3+d**2)/(1-d**2),(1,0,0,0,0):(1-d)**2/(d*(1+d)**2),
   (0,0,1,0,0):-(1-d)**2/(d*(1+d)**2)+(1+d)**2/(d*(1-d)**2)}
pref=2/(1+u)**2*(2*d/(1-d**2))
rho={k:sp.factor(v) for k,v in rho.items()}; K={k:sp.factor(v) for k,v in K.items()}; pref=sp.factor(pref)
pickle.dump((H,rho,K,pref),open('gen1.pkl','wb'))
for k,v in rho.items(): print('rho',k,v)
for k,v in K.items(): print('K',k,v)
print('pref',pref)
# numeric check: setAJ vs G1'+g3+g4
from mpmath import mp, mpf, log, polylog, diff
mp.dps=30
def atoms(x): return dict(a=log(x),b=log(1-x),c=log(1+x),p=polylog(2,x),q=polylog(2,-x))
def mon(m,A): return A['a']**m[0]*A['b']**m[1]*A['c']**m[2]*A['p']**m[3]*A['q']**m[4]
def ev(expr,x): return mpf(sp.N(expr.subs(u,sp.Rational(x)),40))
x0=sp.Rational(37,100); X=mpf(37)/100
A0=atoms(X)
J=ev(pref,x0)*sum(ev(r,x0)*mon(m,A0) for m,r in rho.items())*sum(ev(r,x0)*mon(m,A0) for m,r in K.items())
def G1(x):
    A=atoms(x); return sum(mpf(sp.N(h.subs(u,sp.nsimplify(x)),40)) if False else sp.lambdify(u,h,'mpmath')(x)*mon(m,A) for m,h in H.items())
g1d=diff(G1,X)
a,b,c,p,q=[A0[k] for k in 'abcpq']
iu=1/X; ip=1/(1+X)
g3=(mpf(4)/9*a*a*ip-mpf(100)/9*a*b*iu-mpf(20)/3*a*b*ip-6*a*c*iu-mpf(8)/3*a*c*ip+mpf(28)/3*b*c*iu+4*c*c*iu+mpf(176)/9*(p+q/2)*(iu-ip))
Phi=a*(2*b+c)+4*p+2*q; psd=a*ip+c*iu-2*c*ip
print('check', J-(g1d+g3-mpf(8)/3*Phi*psd))
