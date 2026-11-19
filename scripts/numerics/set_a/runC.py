from fitH import *
L0H,L1H,LmH=LOG['L0'],LOG['L1'],LOG['Lm']
Phi=add(mul(L0H,add(scal(2,L1H),LmH)),scal(4,LiH(2,u)),scal(2,LiH(2,-u)))
T=add(prepend(-1,mul(Phi,add(L0H,scal(-2,LmH)))),prepend(0,mul(Phi,LmH)))
print('T words',len(T))
import time; t=time.time()
B=build(li3free=('free' in sys.argv))
print('basis',len(B),time.time()-t)
sol=solve(B,T)
print(time.time()-t)
if sol is None: print('NO SOLUTION')
else:
    for k,v in sol.items(): print(' ',k,v)
    pickle.dump(sol,open('solC.pkl','wb'))
