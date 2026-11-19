from fitH import *
L0H,L1H,LmH=LOG['L0'],LOG['L1'],LOG['Lm']
a=add(L1H,scal(-1,LmH)); b=add(const(l2),L0H,scal(-1,LmH)); c=add(const(l2),scal(-1,LmH))
F=mul(a,mul(b,c))
T=add(prepend(1,F),prepend(-1,F))
for free in (True,False):
    s=solve(build(li3free=free),T)
    print('M via t:', 'free' if free else 'general', None if s is None else len(s))
T2=prepend(0,mul(L0H,mul(LmH,LmH)))
s=solve(build(li3free=True),T2); print('K li3free', s)
