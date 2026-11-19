"""Independent check of the full x-dependence of lambda4: muon (external mass M) with an
electron loop (mass m), r=M/m, vs BR74 eq. (4): 0.0487202 - 0.458889 ln r + O(ln^k r / r)."""
from setc_num import lam4
from mpmath import mp, mpf, log, sqrt, quad, zeta
mp.dps=20
def da_gen(T):  # Delta alpha/(alpha/pi) at t/m^2 = T < 0
    b=sqrt(1-4/T); L=log((b+1)/(b-1))
    return -mpf(8)/9 + b**2/3 + b*(3-b**2)/6*L
z2=zeta(2); l2=log(2); a4=mp.polylog(4,mpf(1)/2)
C4=mpf(11)/18*z2**2-mpf(4)/9*z2*l2**2-l2**4/27-mpf(8)/9*a4
c0=mpf(115)/24-mpf(79)/9*z2+10*z2*l2-mpf(7)/2*zeta(3)+3*C4
c1=-mpf(31)/12+mpf(10)/3*z2-4*z2*l2+zeta(3)
if __name__=='__main__':
  print('C4',C4,'c0,c1',c0,c1)
  for r in [mpf(10)**2,mpf(10)**3,mpf(10)**4,mpf(10)**5, mpf('206.7682830')]:
    def f(x):
        with mp.workdps(120):
            x=mpf(x); return +(lam4(x)*da_gen(r**2*x**2/(x-1)))
    def g(s):
        with mp.workdps(120):
            x=1-mpf(s); return +(lam4(x)*da_gen(r**2*x**2/(x-1)))
    pts=[0]+[mpf(10)**-k for k in range(30,0,-1)]+[mpf(1)/2]
    a,ea=quad(f,pts,error=True); b,eb=quad(g,pts,error=True)
    v=a+b; asym=c0+c1*log(r)
    print(r, v, asym, 'err', ea+eb, 'diff*r', (v-asym)*r)
