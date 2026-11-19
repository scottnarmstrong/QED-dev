"""Vectorized (numpy) evaluation of the 3D units C and X with separate inner/outer photon
masses mu, nu (Lambda = infinity). Tanh-sinh product rules."""
import pickle, sys, numpy as np, sympy as sp, math
sys.path.insert(0, '/home/scott/QED-dev/scripts/numerics')
import two_loop_unit_integrals as T
d = pickle.load(open('units.pkl', 'rb'))['out']
MS, hS, betaS = T.MS, T.hS, T.betaS
x = sp.Symbol('x', positive=True); Y, y3, y4 = sp.symbols('Y y3 y4', positive=True)
DT = np.float64
def lam(name, sub):
    G = sp.expand_log((d[name]['E'] - d[name]['e0']), force=True)
    return sp.lambdify((y3, y4, x, MS, hS, betaS), G, 'numpy')
fC = lam('C+', None); fX = lam('X', None)
def ts(n, T_=3.2):
    h = 2*T_/n; k = np.arange(-n//2, n//2+1); t = k*h
    s = np.pi/2*np.sinh(t)
    u = 1/(1+np.exp(-2*s)); um = 1/(1+np.exp(2*s))
    w = h*np.pi/2*np.cosh(t)/(2*np.cosh(s)**2)
    return u, um, w
def F2(nu, n=400):
    u, um, w = ts(n, 4.0)
    return float(np.sum(w*u**2*um/(u**2+um*nu))) if nu > 0 else 0.5
def unit3(f, mu, nu, n=120, nx=120, ct=False):
    """2 * int_{Delta2} { int dx G - F2(nu)[...] } (ct=True, corner) or int_{Delta2} int dx G (X)."""
    u, um, w = ts(n); ux, uxm, wx = ts(nx)
    tot = 0.0
    for half in (0, 1):
        # s in (0,1/2) or (1/2,1): y3 = Y s
        for Yv, Ym, wy in zip(u, um, w):
            s = u/2 if half == 0 else 1-u/2
            a3 = Yv*s; a4 = Yv - a3
            ws = w/2
            g = a3*Ym - 0*a4; e = a3*a4
            # careful: yb = 1 - Y = Ym
            g = a3*Ym
            xs = g/(g+e)
            Min = Yv**2 + Ym*mu
            M = Min - nu*e
            vals = np.zeros_like(a3)
            for br in (0, 1):
                if br == 0:
                    X = xs[:, None]*ux[None, :]; W = xs[:, None]*wx[None, :]
                    B = np.broadcast_to(g[:, None], X.shape)
                    Xm = 1 - X
                else:
                    Xm = (1-xs)[:, None]*uxm[None, :]; X = 1 - Xm; W = (1-xs)[:, None]*wx[None, :]
                    B = e[:, None]*X/Xm
                H = (X**2 + Xm*nu)/X
                with np.errstate(all='ignore'):
                    v = f(a3[:, None], a4[:, None], X, M[:, None], H, B)
                v = np.where(np.isfinite(v), v, 0.0)
                vals += np.sum(W*v, axis=1)
            if ct:
                vals = vals - F2(nu)*((Yv**2+2*Yv-2)/(2*Min) - 0.5*np.log(Min))
            tot += wy*Yv*np.sum(ws*vals)
    return 2*tot if ct else tot
if __name__ == '__main__':
    import time
    for n in (60, 100, 140):
        t0=time.time()
        print(n, 'X(0,0) =', repr(unit3(fX, 0.0, 0.0, n, n)), ' target -0.467645446093613651', f'{time.time()-t0:.1f}s', flush=True)
    for n in (60, 100, 140):
        print(n, 'C(0,0) =', repr(unit3(fC, 0.0, 0.0, n, n, ct=False)*2 if False else None))
