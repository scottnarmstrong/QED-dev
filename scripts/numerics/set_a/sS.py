from fitH import *
L0H,L1H,LmH=LOG['L0'],LOG['L1'],LOG['Lm']
a=add(L1H,scal(-1,LmH))            # ln u = ln(1-t)-ln(1+t)
b=add(const(l2),L0H,scal(-1,LmH))  # ln(1-u)
F=mul(a,mul(b,b))
# du/u = -[dt/(1-t)+dt/(1+t)] ; integrating t from 0..1 corresponds u from 1..0, so S(1)=int_0^1 F*(w1+wm) dt
T=add(prepend(1,F),prepend(-1,F))
for free in (True,False):
    B=build(li3free=free)
    s=solve(B,T)
    print('free' if free else 'general', None if s is None else len(s))
    if s:
        for k,v in s.items(): print('  ',k,v)
# also K = int L0 Lm^2/u in u
T2=prepend(0,mul(L0H,mul(LmH,LmH)))
print('K li3free', solve(build(True),T2))
