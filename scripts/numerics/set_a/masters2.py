from fitH import *
L0H,L1H,LmH=LOG['L0'],LOG['L1'],LOG['Lm']
Phi=add(mul(L0H,add(scal(2,L1H),LmH)),scal(4,LiH(2,u)),scal(2,LiH(2,-u)))
T=add(prepend(-1,mul(Phi,add(L0H,scal(-2,LmH)))),prepend(0,mul(Phi,LmH)))
Bf=build(li3free=True)
names={'L0':L0H,'L1':L1H,'Lm':LmH}
cands={}
for a in (0,1,-1):
    for m in itertools.combinations_with_replacement(['L0','L1','Lm'],3):
        F=ONE
        for x in m: F=mul(F,names[x])
        cands[f'M[{a};{"*".join(m)}]']=prepend(a,F)
ks=list(cands)
for i in range(len(ks)):
  for j in range(i,len(ks)):
    B=dict(Bf); B[ks[i]]=cands[ks[i]]; B[ks[j]]=cands[ks[j]]
    s=solve(B,T)
    if s is not None: print('li3free works with:',ks[i],s.get(ks[i]),ks[j],s.get(ks[j]))
