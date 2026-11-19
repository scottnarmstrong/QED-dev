from fitH import *
L0H,L1H,LmH=LOG['L0'],LOG['L1'],LOG['Lm']
S4s=[u,1-u,u/(u-1)]
for name,T in [('A',prepend(0,mul(L0H,mul(L1H,L1H)))),('B',prepend(1,mul(L1H,mul(L0H,L0H))))]:
    for free in (True,False):
        s=solve(build(S4=S4s,S2=S4s,li3free=free),T)
        print(name,'free' if free else 'general', s)
