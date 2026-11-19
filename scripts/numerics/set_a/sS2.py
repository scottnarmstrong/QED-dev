from fitH2 import *
L0H,L1H,LmH=LOG['L0'],LOG['L1'],LOG['Lm']
S4s=[u,1-u,u/(u-1)]
T=add(prepend(0,mul(L0H,mul(L1H,L1H))),prepend(1,mul(L1H,mul(L0H,L0H))))
s=solve(build2(S4s,[u],LG=('L0','L1'),l2li3=False,li2li2=True),T)
print(s)
import mpmath as m
from numG import evalterm
def ev(k,x):
    return evalterm(k,x)
G=lambda x: sum(m.mpf(sp.Rational(v))*ev(k,x) for k,v in s.items())
print('G(1/2)-G(0+)', G(m.mpf(1)/2)-G(m.mpf('1e-30')), -m.pi**4/180)
print('G(0+)',G(m.mpf('1e-30')),'G(1/2)',G(m.mpf(1)/2))
