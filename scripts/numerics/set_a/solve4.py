import sys, time
from mpmath import mp, mpf, log, polylog, pi, zeta, matrix, identify, nstr
def solve(names, F, target, npts_extra=25, order=None):
    n=len(names)
    pts=[mpf(k)/(n+npts_extra+1) for k in range(1,n+npts_extra+1)]
    t=time.time()
    M=[[F[nm](p)[1] for nm in names] for p in pts]
    y=[target(p) for p in pts]
    print('eval',time.time()-t,'s', n, 'basis', file=sys.stderr)
    m=len(pts)
    Q=[]; keep=[]; R=[]
    for j in range(n):
        v=[M[i][j] for i in range(m)]
        nv0=mp.sqrt(mp.fsum(a*a for a in v))
        coef=[mpf(0)]*len(Q)
        for _ in range(2):
            for k,q in enumerate(Q):
                c=mp.fsum(v[i]*q[i] for i in range(m)); v=[v[i]-c*q[i] for i in range(m)]; coef[k]+=c
        nv=mp.sqrt(mp.fsum(a*a for a in v))
        if nv>nv0*mpf(10)**(-(mp.dps*2)//3):
            keep.append(j); Q.append([a/nv for a in v]); R.append(coef+[nv])
    r=list(y); cy=[]
    for q in Q:
        c=mp.fsum(r[i]*q[i] for i in range(m)); r=[r[i]-c*q[i] for i in range(m)]; cy.append(c)
    res=mp.sqrt(mp.fsum(a*a for a in r))
    print('rank',len(keep),'residual',nstr(res,5), file=sys.stderr)
    k=len(keep); x=[mpf(0)]*k
    for i in reversed(range(k)):
        s=cy[i]-mp.fsum(R[j][i]*x[j] for j in range(i+1,k))
        x[i]=s/R[i][i]
    out={}
    for j,v in zip(keep,x):
        if abs(v)>mpf(10)**(-mp.dps//2):
            out[names[j]]=identify(v,['pi**2','log(2)']) or nstr(v,25)
    return res,out
