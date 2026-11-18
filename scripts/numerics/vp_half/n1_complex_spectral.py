# N1: the spectral identity with a complex mass M^2 - i eps:
#   int_0^1 x(1-x) log(1 + x(1-x) k2/(M2 - i eps)) dx = (1/2) int_0^1 rho(v) k2/(k2 + 4(M2 - i eps)/(1-v^2)) dv
# i.e. at fixed eps the spectral line of mass mu_v carries the prescription eps_v = 4 eps/(1-v^2).
import mpmath as mp
mp.mp.dps = 30
rho = lambda v: v**2*(1-v**2/3)/(1-v**2)
def lhs(k2, M2):
    pts = [0, 0.5, 1]
    if k2 < -4:  # branch point of the log near x(1-x) = 1/(-k2)
        xs = (1 - mp.sqrt(1 - 4/(-k2)))/2
        pts = sorted(set(pts + [xs, 1 - xs]))
    return mp.quad(lambda x: x*(1-x)*mp.log(1 + x*(1-x)*k2/M2), pts, maxdegree=10)
def rhs(k2, M2):
    pts = [0, 0.5, 0.9, 0.99, 1]
    if k2 < -4:  # resonance of the spectral line at 4/(1-v^2) = -k2
        vs = mp.sqrt(1 - 4/(-k2)); w = mp.mpf('0.02')
        pts = sorted(set(pts + [vs - w, vs - w/10, vs, vs + w/10, vs + w]))
    return mp.quad(lambda v: rho(v)*k2/(k2 + 4*M2/(1-v**2)), pts, maxdegree=10)/2
for k2 in [mp.mpf('0.3'), mp.mpf(5), mp.mpf(-2), mp.mpf(-7)]:
    for eps in [mp.mpf(0), mp.mpf('0.1'), mp.mpf('0.01')]:
        M2 = mp.mpf(1) - 1j*eps
        if eps == 0 and k2 < -4:  # on the cut at eps = 0
            continue
        a, b = lhs(k2, M2), rhs(k2, M2)
        print(f"k2={float(k2):6.2f} eps={float(eps):5.2f}  lhs={mp.nstr(a,15)}  rhs={mp.nstr(b,15)}  |diff|={mp.nstr(abs(a-b),3)}")
