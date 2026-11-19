from fitH import *
L0H,L1H,LmH=LOG['L0'],LOG['L1'],LOG['Lm']
Phi=add(mul(L0H,add(scal(2,L1H),LmH)),scal(4,LiH(2,u)),scal(2,LiH(2,-u)))
T=add(prepend(-1,mul(Phi,add(L0H,scal(-2,LmH)))),prepend(0,mul(Phi,LmH)))
L1p=add(L1H,LmH)
R=add(prepend(0,mul(L0H,mul(L1p,L1p))),scal(-1,prepend(0,mul(L0H,mul(L1H,L1H)))))
T2=add(T,scal(-1,R))
import sys
S4=eval(sys.argv[1]); S2=eval(sys.argv[2])
s=solve(build(S4=S4,S2=S2,li3free=True),T2)
print(s)
