from mpmath import mp, mpf, log, polylog, pi, zeta, matrix, qr_solve, identify, nstr, lu_solve
import itertools, sys
mp.dps=int(sys.argv[2]) if len(sys.argv)>2 else 50
# each basis elem: function u -> (val, der)
def Lif(n, f, df):
    def g(u):
        x=f(u); dx=df(u)
        v=polylog(n,x)
        lower = -log(1-x) if n==2 else polylog(n-1,x)
        return v, lower*dx/x
    return g
args={'u':(lambda u:u,lambda u:1),'-u':(lambda u:-u,lambda u:-1),'1-u':(lambda u:1-u,lambda u:-1),
 '1/(1+u)':(lambda u:1/(1+u),lambda u:-1/(1+u)**2),'u/(1+u)':(lambda u:u/(1+u),lambda u:1/(1+u)**2),
 '(1-u)/(1+u)':(lambda u:(1-u)/(1+u),lambda u:-2/(1+u)**2),'-(1-u)/(1+u)':(lambda u:-(1-u)/(1+u),lambda u:2/(1+u)**2),
 '(1+u)/2':(lambda u:(1+u)/2,lambda u:mpf(1)/2),'(1-u)/2':(lambda u:(1-u)/2,lambda u:-mpf(1)/2),
 '2u/(1+u)':(lambda u:2*u/(1+u),lambda u:2/(1+u)**2),'1-u^2':(lambda u:1-u*u,lambda u:-2*u)}
logs={'L0':lambda u:(log(u),1/u),'L1':lambda u:(log(1-u),-1/(1-u)),'Lm':lambda u:(log(1+u),1/(1+u)),'l2':lambda u:(log(2),0)}
def prod(fs):
    def g(u):
        vs=[f(u) for f in fs]
        v=mp.fprod([a for a,_ in vs]); d=0
        for i in range(len(vs)):
            d+=vs[i][1]*mp.fprod([vs[j][0] for j in range(len(vs)) if j!=i])
        return v,d
    return g
const=lambda c:(lambda u:(c,0))
F={}
A4=sys.argv[1].split(',') if len(sys.argv)>1 and sys.argv[1]!='all' else list(args)
for an in A4:
    f,df=args[an]
    F[f'Li4({an})']=Lif(4,f,df)
    for ln,lf in logs.items():
        F[f'Li3({an})*{ln}']=prod([Lif(3,f,df),lf])
L2args=['u','-u','(1-u)/2','(1+u)/2','(1-u)/(1+u)']
for an in L2args:
    f,df=args[an]
    for (n1,f1),(n2,f2) in itertools.combinations_with_replacement(list(logs.items()),2):
        if n1=='l2' and n2=='l2': continue
        F[f'Li2({an})*{n1}*{n2}']=prod([Lif(2,f,df),f1,f2])
    F[f'pi2*Li2({an})']=prod([Lif(2,f,df),const(pi**2)])
for a,b in itertools.combinations_with_replacement(L2args,2):
    F[f'Li2({a})*Li2({b})']=prod([Lif(2,*args[a]),Lif(2,*args[b])])
for combo in itertools.combinations_with_replacement(list(logs.items()),4):
    if all(n=='l2' for n,_ in combo): continue
    F['*'.join(n for n,_ in combo)]=prod([f for _,f in combo])
for (n1,f1),(n2,f2) in itertools.combinations_with_replacement(list(logs.items()),2):
    if n1=='l2' and n2=='l2': continue
    F[f'pi2*{n1}*{n2}']=prod([f1,f2,const(pi**2)])
for n1,f1 in logs.items():
    if n1!='l2': F[f'z3*{n1}']=prod([f1,const(zeta(3))])
names=list(F)
