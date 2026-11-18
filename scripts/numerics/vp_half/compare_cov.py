import mpmath as mp
mp.mp.dps = 20
m, M1, M2 = mp.mpf(1), mp.mpf(2), mp.mpf(3)
c1 = (M2**2 - m**2)/(M1**2 - M2**2); c2 = (M1**2 - m**2)/(M2**2 - M1**2)
fl = [(1, m), (c1, M1), (c2, M2)]
eps = mp.mpf('0.1'); k2 = -mp.mpf('0.6')**2 + mp.mpf('0.4')**2
A = mp.mpc('-0.2306369503', '3.034182593'); B = mp.mpc('9.057608087', '0.6855792398')
B0 = mp.mpc('0.883550549693', '0.0654782866273')/eps
LA = sum(c*mp.quad(lambda x: x*(1-x)*mp.log(M**2 - 1j*eps + x*(1-x)*k2), [0, 1]) for c, M in fl)
LB = sum(c*mp.quad(lambda x: mp.log(M**2 - 1j*eps + x*(1-x)*k2), [0, 1]) for c, M in fl)
LB0 = sum(c*mp.log(M**2 - 1j*eps) for c, M in fl)
print('A/LA', A/LA, ' A/LA / pi^2', A/LA/mp.pi**2)
print('B/LB', B/LB, ' B0/LB0', B0/LB0, ' /pi^2', B/LB/mp.pi**2)
