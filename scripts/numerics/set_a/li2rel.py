from fitH import *
def rows_all(F):
    out={}
    for w,c in F.items():
        P=sp.Poly(c,z2,z3,l2,L4h,z5)
        for mon,cc in zip(P.monoms(),P.coeffs()): out[(w,mon)]=cc
    return out
def solve_full(B,T):
    # include constant term
    keys=list(B); cols=[rows_all(B[k]) for k in keys]; rhs=rows_all(T)
    rowkeys=sorted(set().union(*[set(c) for c in cols],set(rhs)),key=str)
    ri={r:i for i,r in enumerate(rowkeys)}; n=len(keys)
    M=[[QQ(0)]*(n+1) for _ in rowkeys]
    for j,c in enumerate(cols):
        for r,v in c.items(): M[ri[r]][j]=QQ.from_sympy(v)
    for r,v in rhs.items(): M[ri[r]][n]=QQ.from_sympy(v)
    R,piv=DomainMatrix(M,(len(rowkeys),n+1),QQ).rref()
    if n in piv: return None
    R=R.to_Matrix(); return {keys[p]:R[i,n] for i,p in enumerate(piv) if R[i,n]!=0}
LG=['L0','L1','Lm','l2']
def li2basis(basis):
    B={}
    for g in basis: B[f'Li2[{g}]']=LiH(2,g)
    for a,b in itertools.combinations_with_replacement(LG,2): B[f'{a}*{b}']=mul(LOG[a],LOG[b])
    B['z2']=const(z2); B['1']=ONE
    return B
basis=[u,-u,(1-u)/2]
for f in [1-u,1/(1+u),u/(1+u),(1-u)/(1+u),-(1-u)/(1+u),(1+u)/2,2*u/(1+u),u**2,1-u**2,((1-u)/(1+u))**2,4*u/(1+u)**2]:
    print(f, solve_full(li2basis(basis),LiH(2,f)))
