from mpmath import mp, mpf, log, polylog, quad, zeta, pi
mp.dps = 40
def F4(u):
    R1=(23*u**6-37*u**5+124*u**4-86*u**3-57*u**2+99*u+78)/(72*(u-1)**2*u*(u+1))
    R2=(12*u**8-11*u**7-78*u**6+21*u**5+4*u**4-15*u**3+13*u+6)/(12*(u-1)**3*u*(u+1)**2)
    R3=(u+1)*(-u**3+7*u**2+8*u+6)/(12*u**2)
    R4=(-7*u**4-8*u**3+8*u+7)/(12*u**2)
    R5=-(3*u**4+5*u**3+7*u**2+5*u+3)/(6*u**2)
    return (R1+R2*log(-u)+R3*log(1+u)+R4*log(1-u)
            +R5*(4*polylog(2,u)+2*polylog(2,-u)+log(-u)*log((1-u)**2*(1+u))))
def kappa4(x):
    with mp.workdps(mp.dps+60):
        x=mpf(x); return +((2-x)/(x*(x-1))*2*F4(x-1))
def dax(x):  # one-loop VP at Euclidean x^2/(1-x), units alpha/pi
    with mp.workdps(mp.dps+60):
        x=mpf(x); b=(2-x)/x
        return +(-mpf(8)/9 + b**2/3 - b*(3-b**2)/6*log(1-x))
def lam4(x): return kappa4(x)-2*(1-x)*dax(x)
PTS=[0,mpf(1)/1000,mpf(1)/10,mpf(1)/2,mpf(9)/10,1-mpf(1)/1000,1]
z2,z3=zeta(2),zeta(3)
A1four = mpf(197)/144 + z2/2 - 3*z2*log(2) + mpf(3)/4*z3   # Petermann/Sommerfield
AVP = mpf(119)/36 - pi**2/3
def Astieltjes(t, f=lam4):
    return quad(lambda x: f(x)*(x**2/(1-x))/(x**2/(1-x)+t), PTS)
if __name__=='__main__':
    I_k=quad(kappa4,PTS); I_l=quad(lam4,PTS)
    print('int kappa4 =',I_k); print('2*A1four   =',2*A1four, ' diff', I_k-2*A1four)
    print('int lam4   =',I_l); print('2(A1-AVP)  =',2*(A1four-AVP), ' diff', I_l-2*(A1four-AVP))
