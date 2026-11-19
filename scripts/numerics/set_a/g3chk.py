from mpmath import *
mp.dps=40
L=lambda k,x: polylog(k,x)
P3=lambda f: L(3,f)-log(abs(f))*L(2,f)
l2=log(2); z2=pi**2/6
def G3(u):
    a=log(u); b=log(1-u); c=log(1+u); v=u/(1+u); t=(1-u)/(1+u)
    return (-mpf(140)/9*P3(v)-mpf(92)/9*P3((1+u)/2)+mpf(20)/3*P3(2*u/(1+u))+mpf(8)/9*P3(1-u*u)
     -mpf(4)/9*P3(t*t)-mpf(32)/9*P3((1-u)/2)+mpf(16)/9*L(3,u)-6*L(3,-u)
     +L(2,v)*(-mpf(142)/9*a+mpf(88)/9*c+mpf(20)/3*l2)+L(2,1-u)*(-mpf(160)/9*a+mpf(176)/9*c-mpf(20)/3*l2)
     -mpf(160)/9*a*a*b+mpf(4)/9*a*a*c+16*a*b*c-mpf(20)/3*a*b*l2-mpf(43)/9*a*c*c+mpf(32)/9*b*c*c
     -mpf(64)/9*b*c*l2+mpf(32)/9*b*l2**2+mpf(20)/27*c**3-mpf(10)/3*c*c*l2+mpf(92)/9*c*l2**2
     +mpf(160)/9*z2*a-mpf(176)/9*z2*c)
def g3(u):
    a=log(u); b=log(1-u); c=log(1+u); P2=L(2,u); M2=L(2,-u)
    return (mpf(4)/9*a*a/(1+u)-mpf(100)/9*a*b/u-mpf(20)/3*a*b/(1+u)-6*a*c/u-mpf(8)/3*a*c/(1+u)
      +mpf(28)/3*b*c/u+4*c*c/u+mpf(176)/9*(P2+M2/2)*(1/u-1/(1+u)))
for u in [mpf('0.3'),mpf('0.8')]: print(diff(G3,u)-g3(u))
e=mpf('1e-30')
print(G3(e),G3(1-e), G3(1-e)-G3(e), mpf(13)/18*zeta(3)-mpf(7)/9*pi**2*l2)
