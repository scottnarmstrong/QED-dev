# exact HPL algebra over letters 0,1,-1 ; functions = dict word(tuple)->sympy coeff (constants as symbols)
import sympy as sp
from functools import lru_cache
z2,z3,l2,L4h,z5=sp.symbols('z2 z3 l2 L4h z5')   # z2=pi^2/6
z4=sp.Rational(2,5)*z2**2
u=sp.symbols('u')
@lru_cache(None)
def shuffle(a,b):
    if not a: return ((b,1),)
    if not b: return ((a,1),)
    res={}
    for w,c in shuffle(a[1:],b):
        k=(a[0],)+w; res[k]=res.get(k,0)+c
    for w,c in shuffle(a,b[1:]):
        k=(b[0],)+w; res[k]=res.get(k,0)+c
    return tuple(res.items())
def clean(F): return {w:c for w,c in ((w,sp.expand(c)) for w,c in F.items()) if c!=0}
def add(*Fs):
    r={}
    for F in Fs:
        for w,c in F.items(): r[w]=r.get(w,0)+c
    return clean(r)
def scal(k,F): return clean({w:k*c for w,c in F.items()})
def mul(A,B):
    r={}
    for wa,ca in A.items():
        for wb,cb in B.items():
            for w,c in shuffle(wa,wb): r[w]=r.get(w,0)+ca*cb*c
    return clean(r)
def const(c): return {():sp.sympify(c)} if c!=0 else {}
def prepend(a,F): return clean({(a,)+w:c for w,c in F.items()})
ONE=const(1)
# logs: ln u = H(0); ln(1-u) = -H(1); ln(1+u)=H(-1)
LOG={'L0':{(0,):1},'L1':{(1,):-1},'Lm':{(-1,):1},'l2':const(l2)}
def factor_letters(e):
    """e rational in u: returns (logs dict {L0,L1,Lm,l2,sign}) """
    e=sp.factor(sp.sympify(e)); n,d=sp.fraction(e)
    out={'L0':0,'L1':0,'Lm':0,'l2':0}
    for part,s in ((n,1),(d,-1)):
        for fct in sp.Mul.make_args(part):
            b,ex=fct.as_base_exp()
            if b.is_number:
                if b==-1: continue
                fi=sp.factorint(abs(b)); assert set(fi)<={2},b
                out['l2']+=s*ex*fi.get(2,0); continue
            if b==u: out['L0']+=s*ex
            elif sp.expand(b-(1-u))==0 or sp.expand(b+(1-u))==0 or sp.expand(b-(u-1))==0: out['L1']+=s*ex
            elif sp.expand(b-(u+1))==0: out['Lm']+=s*ex
            else: raise ValueError(b)
    return out
def logH(e):
    c=factor_letters(e)
    return add(*[scal(c[k],LOG[k]) for k in c])
def dlog_letters(e):
    c=factor_letters(e)  # d ln(1-u) = -du/(1-u) -> letter 1 coefficient -c
    return {0:c['L0'],1:-c['L1'],-1:c['Lm']}
def Lin_const(n,c):
    c=sp.nsimplify(c)
    if c==0: return 0
    if c==1: return {2:z2,3:z3,4:z4,5:z5}[n]
    if c==-1: return -(1-sp.Integer(2)**(1-n))*{2:z2,3:z3,4:z4,5:z5}[n]
    if c==sp.Rational(1,2):
        return {2:z2/2-l2**2/2, 3:sp.Rational(7,8)*z3-z2*l2/2+l2**3/6, 4:L4h}[n]
    raise ValueError(c)
@lru_cache(None)
def LiH_(n,es):
    f=sp.sympify(es)
    if n==1:
        return tuple(scal(-1,logH(1-f)).items())
    low=dict(LiH_(n-1,es))
    dl=dlog_letters(f)
    F=const(Lin_const(n,f.subs(u,0)))
    for a,k in dl.items():
        if k: F=add(F,scal(k,prepend(a,low)))
    return tuple(F.items())
def LiH(n,f): return dict(LiH_(n,str(sp.sympify(f))))
def integrate_form(form):
    """form: dict letter-> HPL function (coefficient of omega_a); returns primitive vanishing (reg) at 0"""
    return add(*[prepend(a,F) for a,F in form.items()])
def numeval(F,x,dps=30):
    import mpmath as m
    m.mp.dps=dps
    # evaluate HPL by series? use iterated integration numerically: recursive quad (slow but ok for checks)
    from functools import lru_cache as lc
    sub={z2:m.pi**2/6,z3:m.zeta(3),l2:m.log(2),L4h:m.polylog(4,0.5),z5:m.zeta(5)}
    @lc(None)
    def H(w,x):
        if not w: return m.mpf(1)
        if all(a==0 for a in w): return m.log(x)**len(w)/m.factorial(len(w))
        a=w[0]; rest=w[1:]
        fa={0:lambda t:1/t,1:lambda t:1/(1-t),-1:lambda t:1/(1+t)}[a]
        if a==0:
            # H(0,w;x) for w not all zeros: integrand finite at 0
            return m.quad(lambda t: fa(t)*H(rest,t),[0,x])
        return m.quad(lambda t: fa(t)*H(rest,t),[0,x])
    return sum(m.mpf(sp.N(c.subs(sub),dps))*H(w,m.mpf(x)) for w,c in F.items())
