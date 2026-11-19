import sympy as sp, pickle
from mpmath import mp, mpf, log, polylog, quad, zeta, pi, pslq, diff
mp.dps=40
u=sp.symbols('u',positive=True)
terms=pickle.load(open('terms.pkl','rb'))
H,N=pickle.load(open('red2.pkl','rb'))
def atoms(x): return [log(x),log(1-x),log(1+x),polylog(2,x),polylog(2,-x)]
def mon(k,x):
    t=1
    for e,v in zip(k,atoms(x)): t*=v**e
    return t
Hf={k:sp.lambdify(u,v,'mpmath') for k,v in H.items()}
Tf={k:sp.lambdify(u,v,'mpmath') for k,v in terms.items()}
Gq=lambda x: sum(f(x)*mon(k,x) for k,f in Hf.items())
J=lambda x: sum(f(x)*mon(k,x) for k,f in Tf.items())
Nf=lambda x: sum(c*mon(m,x)/(x-a) for (a,m),c in N.items())
x0=mpf('0.37')
print('identity check', diff(Gq,x0)+Nf(x0)-J(x0))
# value: split N into convergent ones (exact) and the divergent pieces 1/u*(9/2 L0 + 77/216) and -133/72/(u-1)
div={(0,(1,0,0,0,0)),(0,(0,0,0,0,0)),(1,(0,0,0,0,0))}
conv=[(a,m,c) for (a,m),c in N.items() if (a,m) not in div]
tot_conv=0
for a,m,c in conv:
    v=quad(lambda t: mon(m,t)/(t-a),[0,mpf(1)/2,1])
    rel=pslq([v,1,zeta(2),zeta(3),zeta(2)*log(2),zeta(4),log(2),log(2)**2,log(2)**3],maxcoeff=10**6,maxsteps=10**6)
    print(a,m,c, v, rel)
    tot_conv+=c*v
# boundary: B(eps) = Gq(1-eps)-Gq(eps) + int_eps^{1-eps} divergent pieces
def B(e):
    e=mpf(e)
    d = mpf(9)/2*(log(1-e)**2-log(e)**2)/2 + mpf(77)/216*(log(1-e)-log(e)) - mpf(133)/72*(log(e)-log(1-e))
    return Gq(1-e)-Gq(e)+d
for e in ['1e-10','1e-15','1e-20']:
    with mp.workdps(120): b=B(e)
    print('boundary',e,b)
print('total', b+tot_conv)
