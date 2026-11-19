import sympy as sp, pickle
exec(open('ana.py').read().split('import sys')[0])
G=pickle.load(open('G.pkl','rb'))
P0=near0(G,2); P1=near1(G,2)
c0=P0.as_dict()[(0,)*5]; c1=P1.as_dict()[(0,)*5]
print('G1(0+)=',sp.nsimplify(sp.limit(sp.factor(c0),y,0)))
print('G1(1-)=',sp.expand(sp.limit(sp.factor(c1),y,0)))
