from setc_num import lam4
from mpmath import mp, mpf, log, sqrt, quad
from muon_chk_c import c0, c1
mp.dps=20
def da_gen(T):
    b=sqrt(1-4/T); L=log((b+1)/(b-1))
    return -mpf(8)/9 + b**2/3 + b*(3-b**2)/6*L
r=mpf(1000)
for x in ['0.5','0.01','0.999']:
    x=mpf(x); T=r**2*x**2/(x-1)
    print(x, da_gen(T), log(-T)/3-mpf(5)/9)
def run(D):
    def f(x):
        with mp.workdps(120):
            x=mpf(x); return +(lam4(x)*D(r**2*x**2/(x-1)))
    def g(s):
        with mp.workdps(120):
            x=1-mpf(s); return +(lam4(x)*D(r**2*x**2/(x-1)))
    pts=[0]+[mpf(10)**-k for k in range(30,0,-1)]+[mpf(1)/2]
    a=quad(f,pts,error=True); b=quad(g,pts,error=True)
    return a,b
print(run(da_gen))
print(run(lambda T: log(-T)/3-mpf(5)/9))
print(c0+c1*log(r))
