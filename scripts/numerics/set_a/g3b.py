exec(open('g3.py').read().split("S=[u")[0])
S4set=[-u,1-u,1/(1+u),u/(1+u),-(1-u)/(1+u),(1+u)/2,2*u/(1+u),u**2,1-u**2,((1-u)/(1+u))**2,(1-u)/2]
for S2 in ([u/(1+u),(1-u)/2],[u/(1+u),(1-u)/2,1-u,-u,u]):
  for L3 in ([u,-u],[u,-u,1-u,1/(1+u),u/(1+u)]):
    s=solve(build3(S4set,S2,L3),T)
    print(len(S2),len(L3), s is not None)
S3=list(S4set); S2=[u,-u,u/(1+u),(1-u)/2,1-u]; L3=[u,-u]
def solvable(S3,S2,L3): return solve(build3(S3,S2,L3),T) is not None
if solvable(S3,S2,L3):
  for f in list(S3):
    t=[g for g in S3 if g!=f]
    if solvable(t,S2,L3): S3=t
  for f in list(S2):
    t=[g for g in S2 if g!=f]
    if solvable(S3,t,L3): S2=t
  print(S3,S2); s=solve(build3(S3,S2,L3),T); print(len(s),s)
  import pickle; pickle.dump(s,open('g3solb.pkl','wb'))
