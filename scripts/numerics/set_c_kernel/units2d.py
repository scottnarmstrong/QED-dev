"""L and S units with inner photon mass^2 mu and outer photon mass^2 nu (Lambda = oo), mpmath."""
import pickle, sys, sympy as sp, mpmath as mp
sys.path.insert(0, '/home/scott/QED-dev/scripts/numerics')
import two_loop_unit_integrals as T
d = pickle.load(open('/tmp/claude-1004/-home-scott-QED-dev/12957a40-e5f1-4204-88fb-513fe97e836a/scratchpad/setCkernel/units.pkl', 'rb'))['out']
x = sp.Symbol('x', positive=True); Ys = sp.Symbol('Y', positive=True)
def _f(name):
    G = sp.expand_log(d[name]['E'] - d[name]['e0'], force=True)
    return sp.lambdify((Ys, x, T.MS, T.hS, T.betaS), G, 'mpmath')
fL, fS = _f('L'), _f('S+')
def pts(m):  # breakpoints for a mass^2 scale m
    if m == 0: return [0, 1]
    r = mp.sqrt(m); out = [0]
    for p in (r, mp.sqrt(r)):
        if p < 1 and p > out[-1]: out.append(p)
    return out + [1]
def F2(nu): return mp.quad(lambda t: t**2*(1-t)/(t**2+(1-t)*nu), pts(nu))
def Vk(nu): return T.ct_k(nu) if nu > 0 else mp.mpf(-1)
def Vm(nu): return T.ct_m(nu) if nu > 0 else mp.mpf(1)/2
def mpts(mu, nu):
    s = sorted(set([mp.mpf(0), mp.mpf(1)] + [p for m in (mu, nu) for p in pts(m)]))
    return s
def L(mu, nu):
    f2 = F2(nu); P = mpts(mu, nu)
    def inner(Yv):
        c = Yv*(1-Yv); Min = Yv**2 + (1-Yv)*mu
        g = lambda xx: fL(Yv, xx, Min, (xx**2+(1-xx)*nu)/xx, c)
        return mp.quad(g, P) - f2*(Yv*(Yv**2+2*Yv-2)/(2*Min) - Yv/2*mp.log(Min))
    return mp.quad(inner, P)
def S(mu, nu):
    vk, vm = Vk(nu), Vm(nu); P = mpts(mu, nu)
    def inner(Yv):
        c = Yv*(1-Yv); Min = Yv**2 + (1-Yv)*mu
        g = lambda xx: fS(Yv, xx, Min, (xx**2+(1-xx)*nu)/xx, c)
        d2 = (1-Yv)*mp.log(Min)/2 + (1+Yv)*Yv*(1-Yv)/Min
        sig = -(1+Yv)/2*mp.log(Min)
        return mp.quad(g, P) + d2*vk + (d2-sig)*vm
    return 2*mp.quad(inner, P)
if __name__ == '__main__':
    mp.mp.dps = 20
    l2 = mp.mpf('1e-4')
    print('L(0.01,0.01) =', L(l2, l2), ' doc 0.671406563')
    print('S(0.01,0.01) =', S(l2, l2), ' doc -4.5793668')
