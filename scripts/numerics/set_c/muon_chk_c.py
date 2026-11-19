"""Independent check of the full x-dependence of lambda4: muon (external mass M) with an
electron loop (mass m), r=M/m, vs BR74 eq. (4) asymptotic 0.0487202 - 0.458889 ln r."""
from mpmath import mp, mpf, log, sqrt, quad, zeta
mp.dps=25
def da_gen(T):  # Delta alpha/(alpha/pi) at t/m^2 = T < 0
    b=sqrt(1-4/T); L=log((b+1)/(b-1))
    return -mpf(8)/9 + b**2/3 + b*(3-b**2)/6*L
z2=zeta(2); l2=log(2); a4=mp.polylog(4,mpf(1)/2)
C4=mpf(11)/18*z2**2-mpf(4)/9*z2*l2**2-l2**4/27-mpf(8)/9*a4
c0=mpf(115)/24-mpf(79)/9*z2+10*z2*l2-mpf(7)/2*zeta(3)+3*C4
c1=-mpf(31)/12+mpf(10)/3*z2-4*z2*l2+zeta(3)
print('c0,c1',c0,c1)
