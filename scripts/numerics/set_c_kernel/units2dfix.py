"""L and S units (inner mass^2 mu, outer nu) with fixed tanh-sinh rules on segments."""
import mpmath as mp
from units2d import fL, fS
import two_loop_unit_integrals as T
def segs(scales):
    pts = [mp.mpf(0), mp.mpf(1)]
    for m in scales:
        if 0 < m < 1:
            p = mp.sqrt(m)
            while p < 1:
                pts.append(p); p *= 100
    P = sorted(set(pts))
    return list(zip(P[:-1], P[1:]))
_N = {}
def nodes(level):
    if level not in _N: _N[level] = T.de_nodes(mp.mpf(1)/level)
    return _N[level]
def integ(f, scales, level):
    """int_0^1 f(u) du; f receives (u, 1-u) to keep 1-u accurate."""
    tot = 0
    for a, b in segs(scales):
        L = b - a
        for u, um, w in nodes(level):
            with mp.workdps(mp.mp.dps + T.bumped(min(u, um)*L)):
                xx = a + L*u; xm = (1 - b) + L*um
                tot += w*L*f(xx, xm)
    return tot
def F2(nu, level=16):
    return integ(lambda t, tm: t**2*tm/(t**2+tm*nu), [nu], level) if nu > 0 else mp.mpf(1)/2
def Vk(nu, level=16):
    if nu == 0: return mp.mpf(-1)
    return integ(lambda t, tm: -t**2*tm*(-4*nu*t**2+2*nu*t+2*nu+3*t**3+3*t**2)/(2*(t**2+tm*nu)**2), [nu], level)
def Vm(nu, level=16):
    if nu == 0: return mp.mpf(1)/2
    return integ(lambda t, tm: t**2*tm*(-3*nu*t+3*nu+2*t**2)/(2*(t**2+tm*nu)**2), [nu], level)
def L(mu, nu, level=12):
    f2 = F2(nu)
    def inner(Yv, Ym):
        c = Yv*Ym; Min = Yv**2 + Ym*mu
        g = lambda xx, xm: fL(Yv, xx, Min, (xx**2+xm*nu)/xx, c)
        return integ(g, [mu, nu], level) - f2*(Yv*(Yv**2+2*Yv-2)/(2*Min) - Yv/2*mp.log(Min))
    return integ(inner, [mu, nu], level)
def S(mu, nu, level=12):
    vk, vm = Vk(nu), Vm(nu)
    def inner(Yv, Ym):
        c = Yv*Ym; Min = Yv**2 + Ym*mu
        g = lambda xx, xm: fS(Yv, xx, Min, (xx**2+xm*nu)/xx, c)
        d2 = Ym*mp.log(Min)/2 + (1+Yv)*Yv*Ym/Min
        sig = -(1+Yv)/2*mp.log(Min)
        return integ(g, [mu, nu], level) + d2*vk + (d2-sig)*vm
    return 2*integ(inner, [mu, nu], level)
def ctC(l2, level=16):  # int_{Delta2} [(Y^2+2Y-2)/(2M) - ln M/2], M = Y^2+(1-Y) l2
    return integ(lambda Y, Ym: Y*((Y**2+2*Y-2)/(2*(Y**2+Ym*l2)) - mp.log(Y**2+Ym*l2)/2), [l2], level)
if __name__ == '__main__':
    import time
    mp.mp.dps = 20; l2 = mp.mpf('1e-4')
    for lev in (6, 8):
        t0 = time.time()
        print(lev, 'L', L(l2, l2, lev), 'S', S(l2, l2, lev), f'{time.time()-t0:.0f}s', flush=True)
    print('ref L 0.67140656253639147098  S -4.5793668181957424177')
