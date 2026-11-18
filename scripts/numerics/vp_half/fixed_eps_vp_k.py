# Energy-first one-loop VP at k = (k0,0,0,kz), fixed eps: test the structure
#   Pi^{st}_eps(k) = (k^2 g^{st} - k^s k^t) A + eps g^{st} B.
# N^{st}/4 = q^s (q+k)^t + q^t (q+k)^s - g^{st} (q.(q+k) + M^2), metric (-,+,+,+).
import mpmath as mp, sys
mp.mp.dps = 25
m, M1, M2 = mp.mpf(1), mp.mpf(2), mp.mpf(3)
c1 = (M2**2 - m**2)/(M1**2 - M2**2); c2 = (M1**2 - m**2)/(M2**2 - M1**2)
fl = [(1, m), (c1, M1), (c2, M2)]
k0, kz = mp.mpf(sys.argv[1]), mp.mpf(sys.argv[2])
eps = mp.mpf(sys.argv[3])
g = {(0,0): -1, (1,1): 1, (3,3): 1, (0,3): 0}
def energy_int(comp, q, ct, M):
    # q spatial = (q st, 0, q ct) (azimuthal average handled for (1,1))
    st2 = 1 - ct**2
    qz = q*ct
    E1 = mp.sqrt(q**2 + M**2 - 1j*eps)
    E2 = mp.sqrt(q**2 + 2*q*ct*kz + kz**2 + M**2 - 1j*eps)
    def N(q0):
        qk0 = q0 + k0
        dot = -q0*qk0 + q**2 + qz*kz   # q.(q+k)
        s, t = comp
        if comp == (0,0):
            qs, qkt = q0, qk0; return 2*qs*qkt - g[comp]*(dot + M**2)
        if comp == (3,3):
            return 2*qz*(qz+kz) - (dot + M**2)
        if comp == (0,3):
            return q0*(qz+kz) + qz*qk0
        if comp == (1,1):
            return 2*(q**2*st2/2) - (dot + M**2)
    # f(q0) = N(q0) / ((q0^2 - E1^2)((q0+k0)^2 - E2^2)); close in upper half plane:
    # poles q0 = -E1 and q0 = -k0 - E2
    r1 = N(-E1)/((-2*E1)*((-E1+k0)**2 - E2**2))
    r2 = N(-k0-E2)/(((-k0-E2)**2 - E1**2)*(-2*E2))
    return 2j*mp.pi*(r1 + r2)
def Pi(comp):
    f = lambda q, ct: 2*mp.pi*q**2*sum(c*energy_int(comp, q, ct, M) for c, M in fl)
    pts = [0, 0.5, 2, 8, 40, 200, 1000, 5000]
    tot = 0
    for a, b in zip(pts[:-1], pts[1:]):
        tot += mp.quad(f, [a, b], [-1, 1])
    return tot
res = {c: Pi(c) for c in [(0,3), (1,1), (0,0), (3,3)]}
k2 = -k0**2 + kz**2
A = res[(0,3)]/(-k0*kz)
B = (res[(1,1)] - k2*A)/eps
pred00 = (k2*(-1) - k0**2)*A + eps*(-1)*B
pred33 = (k2 - kz**2)*A + eps*B
print('A', mp.nstr(A, 10), 'B', mp.nstr(B, 10))
print('00', mp.nstr(res[(0,0)], 10), 'pred', mp.nstr(pred00, 10))
print('33', mp.nstr(res[(3,3)], 10), 'pred', mp.nstr(pred33, 10))
