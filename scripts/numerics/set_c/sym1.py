import sympy as sp
s=sp.symbols('s',positive=True)
L0,L1,L2,D1,D2=sp.symbols('L0 L1 L2 D1 D2')
u=-s
R1=(23*u**6-37*u**5+124*u**4-86*u**3-57*u**2+99*u+78)/(72*(u-1)**2*u*(u+1))
R2=(12*u**8-11*u**7-78*u**6+21*u**5+4*u**4-15*u**3+13*u+6)/(12*(u-1)**3*u*(u+1)**2)
R3=(u+1)*(-u**3+7*u**2+8*u+6)/(12*u**2)
R4=(-7*u**4-8*u**3+8*u+7)/(12*u**2)
R5=-(3*u**4+5*u**3+7*u**2+5*u+3)/(6*u**2)
Phi=4*D2+2*D1+L0*(2*L2+L1)
F4=R1+R2*L0+R3*L1+R4*L2+R5*Phi
kap=(1+s)/((1-s)*(-s))*2*F4
b=(1+s)/(1-s)
Da=-sp.Rational(8,9)+b**2/3-b*(3-b**2)/6*L0
lam=kap-2*s*Da
I=sp.expand(lam*Da)
P=sp.Poly(I,L0,L1,L2,D1,D2)
for mon,c in sorted(P.terms(),key=lambda t:-sum(t[0])):
    print(mon, sp.factor(sp.together(c)))
import pickle; pickle.dump((P.as_dict()),open('integrand_s.pkl','wb'))
print('Phi-structure: lam =',sp.factor(sp.together(sp.Poly(sp.expand(lam),L0,L1,L2,D1,D2).as_dict().get((0,0,0,1,0),0))))
print('Da log coeff',sp.factor(-b*(3-b**2)/6), ' Da rational', sp.factor(-sp.Rational(8,9)+b**2/3))
