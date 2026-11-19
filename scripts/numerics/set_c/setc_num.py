"""Set (c) value: A(c) = int_0^1 lambda4(x) Dalpha(t(x)) dx  (units (alpha/pi)^3).
Kernel: Balzani-Laporta-Passera arXiv:2112.05704 eqs. (21),(22),(24),(38)."""
from mpmath import mp, mpf, log, polylog, quad, zeta, pi
def F4(u):
    R1=(23*u**6-37*u**5+124*u**4-86*u**3-57*u**2+99*u+78)/(72*(u-1)**2*u*(u+1))
    R2=(12*u**8-11*u**7-78*u**6+21*u**5+4*u**4-15*u**3+13*u+6)/(12*(u-1)**3*u*(u+1)**2)
    R3=(u+1)*(-u**3+7*u**2+8*u+6)/(12*u**2)
    R4=(-7*u**4-8*u**3+8*u+7)/(12*u**2)
    R5=-(3*u**4+5*u**3+7*u**2+5*u+3)/(6*u**2)
    return (R1+R2*log(-u)+R3*log(1+u)+R4*log(1-u)
            +R5*(4*polylog(2,u)+2*polylog(2,-u)+log(-u)*log((1-u)**2*(1+u))))
def kappa4(x): return (2-x)/(x*(x-1))*2*F4(x-1)
def dax(x):  # one-loop VP Delta alpha(t(x))/(alpha/pi), t = m^2 x^2/(x-1), beta=(2-x)/x
    b=(2-x)/x
    return -mpf(8)/9 + b**2/3 - b*(3-b**2)/6*log(1-x)
def lam4(x): return kappa4(x) - 2*(1-x)*dax(x)
def f(x):
    with mp.workdps(300):
        x=mpf(x); return +(lam4(x)*dax(x))
def fchain(x):
    with mp.workdps(300):
        x=mpf(x); return +((1-x)*dax(x)**2)
if __name__=='__main__':
    import sys
    D=int(sys.argv[1]) if len(sys.argv)>1 else 30
    mp.dps=D
    z2=zeta(2)
    target = mpf(227)/72 + mpf(31)/9*z2 - 8*z2*log(2) - mpf(35)/8*zeta(3) + 2*z2**2
    Ab=mpf(8)/3*zeta(3)-mpf(4)/135*pi**2-mpf(943)/324
    pts=[0]+[mpf(10)**-k for k in range(D+10,0,-3)]+[mpf(1)/2]
    def both(h):
        def g(s):
            with mp.workdps(300):
                return +h(1-mpf(s))
        a,e1=quad(h,pts,error=True); b,e2=quad(g,pts,error=True)
        return a+b, e1+e2
    v,err=both(f)
    w,errw=both(fchain)
    print('A(c) integral =',v,' est err',err)
    print('BR74 eq.(3)   =',target)
    print('difference    =',v-target)
    print('chain int     =',w,' A(b) exact',Ab,' diff',w-Ab)
