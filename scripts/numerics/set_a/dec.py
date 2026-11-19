from sym import *
import sys
S=[u,-u,1-u,1/(1+u),u/(1+u),(1-u)/(1+u),-(1-u)/(1+u),(1+u)/2,(1-u)/2,2*u/(1+u),u**2,1-u**2,
   ((1-u)/(1+u))**2,4*u/(1+u)**2]
def blocks(withC=False):
    B={}
    for f in S:
        lf=logpoly(f); l1f=logpoly(1-f)
        B[('A',f)]=form_mul(lf**3,dlog(1-f))
        B[('B',f)]=form_mul(lf**2*l1f,dlog(f))
        if withC: B[('C',f)]=form_mul(lf*l1f**2,dlog(f))
    mons=[m for m in itertools.combinations_with_replacement(X,4)]
    for m in mons:
        B[('d',m)]=dpoly(sp.Mul(*m))
    return B
def decompose(target,withC=False):
    B=blocks(withC)
    keys=list(B)
    cs=sp.symbols(f'c0:{len(keys)}')
    eqs=[]
    for k in ('d0','d1','dm'):
        tot=sp.expand(sum(c*B[key][k] for c,key in zip(cs,keys))-target[k])
        P=sp.Poly(tot,*X)
        eqs+=P.coeffs()
    sol=sp.solve(eqs,cs,dict=True)
    if not sol: return None
    s=sol[0]
    out={}
    for c,key in zip(cs,keys):
        v=s.get(c,c)
        v=v.subs({cc:0 for cc in cs})
        if v!=0: out[key]=v
    return out
if __name__=='__main__':
    Phip={'d0':-(2*L1+Lm),'d1':-2*L0,'dm':L0}
    psi=L0*Lm-Lm**2
    target=form_mul(psi,Phip)
    r=decompose(target, withC=len(sys.argv)>1)
    print(r)
