# exact decomposition of log-polynomial 1-forms into Li3-free primitive blocks
import sympy as sp, itertools
L0,L1,Lm,l2=sp.symbols('L0 L1 Lm l2')
X=[L0,L1,Lm,l2]
# 1-form: dict letter -> polynomial in X ; letters 'd0' du/u, 'd1' du/(1-u), 'dm' du/(1+u)
# log f as (poly linear in X), dlog f as dict
def lg(expr):
    """expr: sympy rational in u built from u,1-u,1+u,2,-1 ; returns log-linear, dlog-dict"""
    pass
u=sp.symbols('u')
def fac(e):
    e=sp.factor(e)
    n,d=sp.fraction(e)
    out={L0:0,L1:0,Lm:0,l2:0}
    def add(t,s):
        for b,ex in sp.Mul.make_args(t) and [sp.Pow(b,1).as_base_exp() for b in sp.Mul.make_args(t)]:
            pass
    for part,s in ((n,1),(d,-1)):
        for fct in sp.Mul.make_args(part):
            b,ex=fct.as_base_exp()
            if b.is_number:
                if b==-1: continue
                # integer: factor 2
                fi=sp.factorint(abs(b))
                assert set(fi)<= {2}, b
                out[l2]+=s*ex*fi.get(2,0)
                continue
            p=sp.Poly(b,u)
            if b==u: out[L0]+=s*ex
            elif sp.expand(b-(1-u))==0 or sp.expand(b+(1-u))==0: out[L1]+=s*ex
            elif sp.expand(b-(u+1))==0: out[Lm]+=s*ex
            else: raise ValueError(b)
    return out
def logpoly(e):
    c=fac(e); return c[L0]*L0+c[L1]*L1+c[Lm]*Lm+c[l2]*l2
def dlog(e):
    c=fac(e); return {'d0':c[L0],'d1':-c[L1],'dm':c[Lm]}
def form_mul(p,dl):
    return {k:sp.expand(p*v) for k,v in dl.items()}
def form_add(*fs):
    out={'d0':0,'d1':0,'dm':0}
    for f in fs:
        for k,v in f.items(): out[k]=sp.expand(out[k]+v)
    return out
def dpoly(P):
    """exact differential of a polynomial in X"""
    out={'d0':0,'d1':0,'dm':0}
    out['d0']=sp.expand(sp.diff(P,L0)); out['d1']=sp.expand(-sp.diff(P,L1)); out['dm']=sp.expand(sp.diff(P,Lm))
    return out
