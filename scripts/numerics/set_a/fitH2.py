from fitH import *
def build2(S4,S2,LG=('L0','L1','Lm','l2'),l2li3=True,li2li2=True,zeta=True):
    B={}
    for f in S4:
        B[f'P4[{f}]']=add(LiH(4,f),scal(-1,mul(logH(f),LiH(3,f))))
        if l2li3: B[f'l2*Li3[{f}]']=scal(l2,LiH(3,f))
    for g in S2:
        for a,b in itertools.combinations_with_replacement(LG,2):
            if a=='l2' and b=='l2' and not l2li3: continue
            B[f'Li2[{g}]*{a}*{b}']=mul(LiH(2,g),mul(LOG[a],LOG[b]))
        B[f'z2*Li2[{g}]']=scal(z2,LiH(2,g))
    if li2li2:
        for g,h in itertools.combinations_with_replacement(S2,2):
            B[f'Li2[{g}]*Li2[{h}]']=mul(LiH(2,g),LiH(2,h))
    LG4=('L0','L1','Lm','l2')
    for m in itertools.combinations_with_replacement(LG4,4):
        if all(x=='l2' for x in m): continue
        F=ONE
        for x in m: F=mul(F,LOG[x])
        B['*'.join(m)]=F
    for a,b in itertools.combinations_with_replacement(LG4,2):
        B[f'z2*{a}*{b}']=mul(const(z2),mul(LOG[a],LOG[b]))
    for a in LG4: B[f'z3*{a}']=scal(z3,LOG[a])
    return B
def greedy(T,S4,S2,**kw):
    S4=list(S4); S2=list(S2)
    assert solve(build2(S4,S2,**kw),T) is not None
    for f in list(S4):
        t=[g for g in S4 if g!=f]
        if solve(build2(t,S2,**kw),T) is not None: S4=t
    for f in list(S2):
        t=[g for g in S2 if g!=f]
        if solve(build2(S4,t,**kw),T) is not None: S2=t
    return S4,S2,solve(build2(S4,S2,**kw),T)
