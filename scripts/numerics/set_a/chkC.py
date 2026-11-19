from numG import *
sol={'P4[-u]': 2, 'P4[1 - u]': 4, 'P4[1/(u + 1)]': 6, 'P4[u/(u + 1)]': -6, 'P4[(u - 1)/(u + 1)]': 4, 'P4[u/2 + 1/2]': 4, 'l2*Li3[u/2 + 1/2]': -4, 'P4[2*u/(u + 1)]': 4, 'l2*Li3[2*u/(u + 1)]': 4, 'P4[u**2]': -1/2, 'P4[1 - u**2]': -1, 'P4[(1 - u)**2/(u + 1)**2]': -1/4, 'Li2[u/(u + 1)]*L1*Lm': -4, 'Li2[u/(u + 1)]*Lm*Lm': -2, 'Li2[1/2 - u/2]*L0*L0': 2, 'Li2[1/2 - u/2]*L0*Lm': -4, 'L0*L0*L1*Lm': 2, 'L0*L0*L1*l2': -2, 'L0*L0*Lm*Lm': 1/2, 'L0*L0*l2*l2': 1, 'L0*L1*Lm*l2': 4, 'L0*Lm*Lm*Lm': 1, 'L0*Lm*l2*l2': -2, 'L1*Lm*Lm*Lm': -2, 'Lm*Lm*Lm*Lm': -3/2, 'Lm*Lm*Lm*l2': 4/3, 'Lm*Lm*l2*l2': -1, 'z2*L0*L0': -1, 'z2*L0*Lm': 2, 'z2*L1*Lm': 2, 'z2*Lm*Lm': 2}
sol={k:sp.nsimplify(v) for k,v in sol.items()}
for e in ['1e-10','1e-20','1e-30']:
    print('G(0+)',G(sol,m.mpf(e)), ' G(1-)',G(sol,1-m.mpf(e)))
l=m.log(2)
Cc=7*m.pi**4/720+m.pi**2*l**2/6-l**4/6-4*m.polylog(4,0.5)
Phi=lambda u: m.log(u)*m.log((1-u)**2*(1+u))+4*m.polylog(2,u)+2*m.polylog(2,-u)
Cn=m.quad(lambda u: Phi(u)*((1/u-2/(1+u))*m.log(1+u)+m.log(u)/(1+u)),[0,0.25,0.5,1])
print('C num',Cn,' closed',Cc)
print('G(1)-G(0)+pi^4/240', G(sol,1-m.mpf('1e-30'))-G(sol,m.mpf('1e-30'))+m.pi**4/240)
S1=m.quad(lambda y: m.log(y)*m.log(1-y)**2/y,[0,0.5,1]); print('S1',S1,-m.pi**4/180)
