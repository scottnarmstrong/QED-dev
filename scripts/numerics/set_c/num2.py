from num1 import *
def dax(x):
    b=(2-x)/x
    return -mpf(8)/9 + b**2/3 - b*(3-b**2)/6*log(1-x)
z2=zeta(2)
target = mpf(227)/72 + mpf(31)/9*z2 - 8*z2*log(2) - mpf(35)/8*zeta(3) + 2*z2**2
print('target', target)
f=lambda x: kappa4(x)*dax(x)
for dps in (30,45):
    mp.dps=dps
    v=quad(f,[0,mpf(1)/4,mpf(1)/2,mpf(3)/4,mpf(9)/10,mpf(99)/100,1],maxdegree=10)
    print(dps, v, v-target)
