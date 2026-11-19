from num1 import *
from num2 import dax, target
import sys
def f(x):
    with mp.workdps(260):
        x=mpf(x)
        return +(kappa4(x)*dax(x))
mp.dps=34
eps=mpf(10)**-34
for x in [mpf('1e-8'),mpf('1e-20'),1-mpf('1e-8'),1-mpf('1e-20')]:
    print(x, f(x))
pts=[eps,mpf(10)**-12,mpf(10)**-6,mpf(10)**-3,mpf(1)/10,mpf(1)/2,mpf(9)/10,1-mpf(10)**-3,1-mpf(10)**-6,1-mpf(10)**-12,1-eps]
v=quad(f,pts,method='gauss-legendre',maxdegree=8,error=True)
print(v, v[0]-target)
