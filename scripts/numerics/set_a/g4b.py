from fitH2 import *
L0H,L1H,LmH=LOG['L0'],LOG['L1'],LOG['Lm']
Phi=add(mul(L0H,add(scal(2,L1H),LmH)),scal(4,LiH(2,u)),scal(2,LiH(2,-u)))
T=add(prepend(-1,mul(Phi,add(L0H,scal(-2,LmH)))),prepend(0,mul(Phi,LmH)))
L1p=add(L1H,LmH)
R=add(prepend(0,mul(L0H,mul(L1p,L1p))),scal(-1,prepend(0,mul(L0H,mul(L1H,L1H)))))
T2=add(T,scal(-1,R))
S4=[u,-u,1-u,1/(1+u),u/(1+u),(1-u)/(1+u),-(1-u)/(1+u),(1+u)/2,(1-u)/2,2*u/(1+u),u**2,1-u**2,((1-u)/(1+u))**2,4*u/(1+u)**2]
S2=[u,-u,1-u,1/(1+u),u/(1+u),(1-u)/(1+u),-(1-u)/(1+u),(1+u)/2,(1-u)/2,2*u/(1+u)]
for kw in [dict(l2li3=False),dict()]:
    try:
        a,b,s=greedy(T2,S4,S2,**kw)
        print(kw,a,b,len(s)); print(s)
    except AssertionError: print(kw,'unsolvable')
