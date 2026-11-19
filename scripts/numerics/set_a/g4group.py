from mpmath import *
mp.dps=40
L=lambda k,x: polylog(k,x)
P=lambda f: L(4,f)-log(abs(f))*L(3,f)
l2=log(2); z2=pi**2/6
def G4(u):
    t=(1-u)/(1+u); a=log(u); b=log(1-u); c=log(1+u); v=u/(1+u); h=(1-u)/2
    return (2*P(-u)+4*P(1-u)+6*P(1/(1+u))-6*P(v)+4*P(-t)+4*P((1+u)/2)-4*l2*L(3,(1+u)/2)
      +4*P(2*u/(1+u))+4*l2*L(3,2*u/(1+u))-P(u*u)/2-P(1-u*u)-P(t*t)/4
      +b*c*(-4*(L(2,v)-L(2,0.5))-2*(c**2-l2**2)) -2*L(2,v)*c**2
      +2*a**2*(L(2,h)-L(2,0.5)) -4*L(2,h)*a*c
      +2*a*a*b*c-2*a*a*b*l2+a*a*c*c/2+4*a*b*c*l2+a*c**3-2*a*c*l2**2-1.5*c**4+mpf(4)/3*c**3*l2-c*c*l2*l2
      +pi**2/3*a*c+pi**2/3*c*c)
def tgt(u):
    a=log(u); b=log(1-u); c=log(1+u)
    Phi=a*(2*b+c)+4*L(2,u)+2*L(2,-u); psid=a/(1+u)+c/u-2*c/(1+u)
    Rem=a*(b+c)**2/u-a*b*b/u
    return Phi*psid-Rem
for u in [mpf('0.2'),mpf('0.7')]:
    print(diff(G4,u), tgt(u))
e=mpf('1e-25')
print('G4(0)',G4(e),'G4(1)',G4(1-e))
z4=pi**4/90; Ph=L(4,0.5)-log(0.5)*L(3,0.5)
G0=4*z4+6*z4+4*(-mpf(7)/8*z4)+4*Ph-4*l2*L(3,0.5)-z4-z4/4
G1=2*(-mpf(7)/8*z4)+6*Ph-6*Ph+4*z4-4*l2*zeta(3)+4*z4+4*l2*zeta(3)-z4/2-1.5*l2**4+mpf(4)/3*l2**4-l2**4+pi**2/3*l2**2
print(G0,G1)
print('C check', G1-G0+pi**4/240, 7*pi**4/720+pi**2*l2**2/6-l2**4/6-4*L(4,0.5))
