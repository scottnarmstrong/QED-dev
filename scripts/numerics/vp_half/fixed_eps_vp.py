# Energy-first one-loop vacuum polarization at k = 0, fixed eps, PV flavour sum.
# N^{st}/4 = 2 q^s q^t - g^{st} (q^2 + M^2), metric (-,+,+,+), denominators (q^2+M^2-i eps)^2.
# Energy integral by residues: int dq0 (q0^2+b)/(q0^2-E^2)^2 = i pi (b-E^2)/(2 E^3).
import mpmath as mp
mp.mp.dps = 30
m, M1, M2 = mp.mpf(1), mp.mpf(2), mp.mpf(3)
# PV: 1 + c1 + c2 = 0, m^2 + c1 M1^2 + c2 M2^2 = 0
c1 = (M2**2 - m**2)/(M1**2 - M2**2); c2 = (M1**2 - m**2)/(M2**2 - M1**2)
fl = [(1, m), (c1, M1), (c2, M2)]
def energy(b, E2):
    E = mp.sqrt(E2)
    return 1j*mp.pi*(b - E2)/(2*E**3)
# check residue formula once by direct quadrature
eps = mp.mpf('0.1'); q = mp.mpf('0.7'); E2 = q**2 + 1 - 1j*eps
b = q**2 + 1
direct = mp.quad(lambda t: (t**2 + b)/(t**2 - E2)**2, [-mp.inf, -2, 0, 2, mp.inf])
print('residue check', direct, energy(b, E2))
def comp00(eps):
    f = lambda q: 4*mp.pi*q**2*sum(c*energy(q**2+M**2, q**2+M**2-1j*eps) for c, M in fl)
    return mp.quad(f, [0, 1, 10, mp.inf])
def comp11(eps):
    f = lambda q: 4*mp.pi*q**2*sum(c*energy(-q**2/3-M**2, q**2+M**2-1j*eps) for c, M in fl)
    return mp.quad(f, [0, 1, 10, 100, 1000]) + mp.quad(f, [1000, 10**4, 10**5, 10**6])
for e in ['0.1', '0.01', '0.001']:
    e = mp.mpf(e)
    pred00 = -mp.pi*e/2*4*mp.pi*(-mp.mpf(1)/2)*sum(c*mp.log(M**2-1j*e) for c, M in fl)
    print('eps', e, 'Pi00(0) =', mp.nstr(comp00(e), 12), ' predicted', mp.nstr(pred00, 12),
          ' Pi11(0) =', mp.nstr(comp11(e), 12))
