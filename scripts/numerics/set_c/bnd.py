from chk_red import *
mp.dps=60
with mp.workdps(200): b=B('1e-45')
print(b)
print(pslq([b,1,zeta(2),zeta(3),zeta(2)*log(2),log(2)],maxcoeff=10**7,maxsteps=10**6,tol=mpf(10)**-35))
