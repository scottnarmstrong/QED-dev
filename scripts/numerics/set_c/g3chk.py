from mpmath import mp, mpf, log, polylog, diff, zeta, pi
import pickle
mp.dps=30
g3terms=pickle.load(open('g3terms.pkl','rb'))
Li2=lambda z: polylog(2,z); Li3=lambda z: polylog(3,z)
P3=lambda f: Li3(f)-log(abs(f))*Li2(f)
l2=log(2)
def G3(u):
    L0,L1,Lm=log(u),log(1-u),log(1+u); t=(1-u)/(1+u)
    return (mpf(8)/3*P3(u/(1+u))-mpf(4)/3*P3(t)+4*P3((1+u)/2)-mpf(4)/3*P3((1-u)/2)
      -mpf(16)/3*P3(2*u/(1+u))-mpf(2)/3*P3(1-u**2)-mpf(14)/3*Li3(u)+Li3(-u)/2
      +Li2(u)*(-mpf(4)/9*L0-mpf(16)/3*l2+mpf(491)/108)+Li2(-u)*(-mpf(193)/18*L0+mpf(16)/3*l2+mpf(119)/54)
      +mpf(8)/9*Lm-L0*L1/27-mpf(131)/54*L0*Lm+mpf(97)/36*L0**2*L1-mpf(193)/36*L0**2*Lm
      -mpf(16)/3*L0*L1*Lm+mpf(8)/3*L0*Lm**2+mpf(4)/3*L1*(Lm-l2)**2-mpf(4)/3*Lm**3+mpf(16)/3*Lm**2*l2-4*Lm*l2**2)
def g3(u):
    at=[log(u),log(1-u),log(1+u),Li2(u),Li2(-u)]
    tot=0
    for a,m,c in g3terms:
        M=1
        for e,v in zip(m,at): M*=v**e
        tot+=c*M/(u-a)
    return tot
for u0 in ['0.2','0.7']:
    u0=mpf(u0); print(diff(G3,u0)-g3(u0))
print(G3(mpf('1e-25')), zeta(3)/3-mpf(8)/9*l2**3)
print(G3(1-mpf('1e-25')))
for a,m,c in g3terms: print(a,m,c)
