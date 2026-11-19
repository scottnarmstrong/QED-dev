from mpmath import mp, mpf, log, polylog, quad, sqrt, zeta, pi, atanh
mp.dps = 40
def R(u):
    R1=(23*u**6-37*u**5+124*u**4-86*u**3-57*u**2+99*u+78)/(72*(u-1)**2*u*(u+1))
    R2=(12*u**8-11*u**7-78*u**6+21*u**5+4*u**4-15*u**3+13*u+6)/(12*(u-1)**3*u*(u+1)**2)
    R3=(u+1)*(-u**3+7*u**2+8*u+6)/(12*u**2)
    R4=(-7*u**4-8*u**3+8*u+7)/(12*u**2)
    R5=-(3*u**4+5*u**3+7*u**2+5*u+3)/(6*u**2)
    return R1,R2,R3,R4,R5
def F4(u):
    R1,R2,R3,R4,R5=R(u)
    return (R1+R2*log(-u)+R3*log(1+u)+R4*log(1-u)
            +R5*(4*polylog(2,u)+2*polylog(2,-u)+log(-u)*log((1-u)**2*(1+u))))
def kappa4(x): return (2-x)/(x*(x-1))*2*F4(x-1)
# one-loop VP in units alpha/pi, Delta alpha(t) = 2 int z(1-z) log(1 - z(1-z) t), m=1
def dalpha(t):
    # closed form: with beta = sqrt(1-4/t) (>1 for t<0)
    b=sqrt(1-4/t)
    return (mpf(1)/3)*(-mpf(5)/3 + b**2 + b*(3-b**2)/2*log((b+1)/(b-1)))  # to be checked
def dalpha_q(t): return 2*quad(lambda z: z*(1-z)*log(1-z*(1-z)*t),[0,mpf(1)/2,1])
t=mpf(-3)
print(dalpha(t), dalpha_q(t))
tx=lambda x: x**2/(x-1)
LO=quad(lambda x:(1-x)*dalpha_q(tx(x)),[0,0.5,1])
print('LO',LO, mpf(119)/36-pi**2/3)
