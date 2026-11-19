import sympy as sp, pickle
u=sp.symbols('u',positive=True); L=sp.symbols('L')
H,N=pickle.load(open('red2.pkl','rb'))
# low N: weight<=2 (mon weight<=1)
def wt(m): return m[0]+m[1]+m[2]+2*m[3]+2*m[4]
low={k:v for k,v in N.items() if wt(k[1])<=1}
print(low)
n=6
ser={'L1':sp.series(sp.log(1-u),u,0,n).removeO(),'Lm':sp.series(sp.log(1+u),u,0,n).removeO(),
     'P2':sum(u**k/sp.Integer(k)**2 for k in range(1,n)),'M2':sum((-u)**k/sp.Integer(k)**2 for k in range(1,n))}
def monser(m):
    e=L**m[0]*ser['L1']**m[1]*ser['Lm']**m[2]*ser['P2']**m[3]*ser['M2']**m[4]
    return sp.expand(e)
G=0
for m,q in H.items(): G+=sp.series(q,u,0,4).removeO()*monser(m)
# low N primitives (vanishing at 0 except logs): 1/u -> L ; 1/(1+u)->Lm ; L0/u -> L^2/2 ; L0/(1+u) -> L0 Lm + Li2(-u) ; L1/u -> -Li2(u); Lm/(1+u)->Lm^2/2 ; Lm/u -> -Li2(-u)
prim={(0,(0,0,0,0,0)):L, (-1,(0,0,0,0,0)):ser['Lm'], (0,(1,0,0,0,0)):L**2/2, (-1,(1,0,0,0,0)):L*ser['Lm']+ser['M2'],
      (0,(0,1,0,0,0)):-ser['P2'], (-1,(0,0,1,0,0)):ser['Lm']**2/2, (0,(0,0,1,0,0)):-ser['M2']}
for k,c in low.items(): G+=c*prim[k]
G=sp.expand(G)
P=sp.Poly(G,u,1/u,L) if False else None
# collect u^k L^j for k<=0
terms=sp.collect(G,[u],evaluate=False)
for k in sorted(terms,key=lambda t: sp.degree(t,u) if t!=1 else 0):
    deg=sp.Poly(k,u).degree() if k.has(u) and not k.has(1/u) else None
    print(k, sp.simplify(terms[k])) if (k==1 or k.has(1/u) or k==u**-1) else None
print('const part:', sp.expand(G).subs(u,0) if False else '')
neg={}
for t in sp.Add.make_args(G):
    d=sp.degree(t.subs(L,1).as_numer_denom()[0],u)-sp.degree(t.subs(L,1).as_numer_denom()[1],u)
    if d<=0: neg[d]=neg.get(d,0)+t
for d in sorted(neg): print(d, sp.factor(neg[d]))
