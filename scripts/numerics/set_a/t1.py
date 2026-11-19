import sys
from mpmath import mp, log, polylog
argset=sys.argv[1]; which=sys.argv[2]
sys.argv=['x',argset,'40']
exec(open('fit4.py').read())
from solve4 import solve
L=lambda u:(log(u),log(1-u),log(1+u),polylog(2,u),polylog(2,-u))
T={'T1':lambda u:L(u)[0]*L(u)[1]*L(u)[2]/u,'T2':lambda u:L(u)[1]*L(u)[2]**2/u,
   'T3':lambda u:L(u)[0]**2*L(u)[2]/(1-u),'T4':lambda u:L(u)[0]*L(u)[2]**2/(1-u),
   'C':lambda u:(lambda a:(a[0]*(2*a[1]+a[2])+4*a[3]+2*a[4])*(a[0]/(1+u)+a[2]/u-2*a[2]/(1+u)))(L(u))}
res,out=solve(names,F,T[which])
print(which,'res',res)
for k,v in out.items(): print('  ',k,v)
