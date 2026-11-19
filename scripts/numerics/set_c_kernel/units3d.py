"""C and X units with inner photon mass^2 mu and outer mass^2 nu (Lambda = oo), mpmath,
fixed tanh-sinh product rules (as run_corner of two_loop_unit_integrals.py), multiprocessing."""
import pickle, sys, time, sympy as sp, mpmath as mp
from multiprocessing import Pool
sys.path.insert(0, '/home/scott/QED-dev/scripts/numerics')
import two_loop_unit_integrals as T
HERE = '/tmp/claude-1004/-home-scott-QED-dev/12957a40-e5f1-4204-88fb-513fe97e836a/scratchpad/setCkernel/'
d = pickle.load(open(HERE + 'units.pkl', 'rb'))['out']
x = sp.Symbol('x', positive=True); y3, y4 = sp.symbols('y3 y4', positive=True)
def _f(name):
    G = sp.expand_log(d[name]['E'] - d[name]['e0'], force=True)
    return sp.lambdify((y3, y4, x, T.MS, T.hS, T.betaS), G, 'mpmath')
FN = {'C': _f('C+'), 'X': _f('X')}
de_nodes, bumped = T.de_nodes, T.bumped
G = {}
def xint(f, a3, a4, Yv, Ym, mu, nu, xn):
    gv, ev = a3*Ym, a3*a4; xs = gv/(gv+ev); tot = 0
    Min = Yv**2 + Ym*mu; M = Min - nu*ev
    for u, um, w in xn:
        with mp.workdps(mp.mp.dps + bumped(min(a3, a4, Ym, xs*u, (1-xs)*um, abs(a3-a4)))):
            try:
                X1 = xs*u
                tot += w*xs*f(a3, a4, X1, M, (X1**2+(1-X1)*nu)/X1, gv)
            except ZeroDivisionError:
                pass
            try:
                Xm = (1-xs)*um; X2 = 1 - Xm
                tot += w*(1-xs)*f(a3, a4, X2, M, (X2**2+Xm*nu)/X2, ev*X2/Xm)
            except ZeroDivisionError:
                pass
    return tot
def row(args):
    name, mu, nu, Yv, Ym, wy, level, xlevel, dps = args
    mp.mp.dps = dps
    f = FN[name]; N = de_nodes(mp.mpf(1)/level); xn = de_nodes(mp.mpf(1)/xlevel)
    sub = 0
    for u, um, wu in N:
        v = Yv*u/2
        sub += wu*(xint(f, v, Yv-v, Yv, Ym, mu, nu, xn) + xint(f, Yv-v, v, Yv, Ym, mu, nu, xn))/2
    return wy*Yv*sub
def unit(name, mu, nu, level=8, xlevel=16, dps=30, procs=int(__import__('os').environ.get('PROCS', '3'))):
    mp.mp.dps = dps
    mu, nu = mp.mpf(mu), mp.mpf(nu)
    N = de_nodes(mp.mpf(1)/level)
    jobs = [(name, mu, nu, Yv, Ym, wy, level, xlevel, dps) for Yv, Ym, wy in N]
    with Pool(procs) as p:
        two = mp.fsum(p.map(row, jobs, chunksize=1))
    if name == 'X':
        return two
    # corner counterterm, 1D in Y (area element Y dY), at the same rule
    f2 = mp.quad(lambda t: t**2*(1-t)/(t**2+(1-t)*nu), [0, mp.sqrt(nu), 1] if nu < 1 else [0, 1]) if nu > 0 else mp.mpf(1)/2
    def ctY(Yv):
        Min = Yv**2 + (1-Yv)*mu
        return Yv*((Yv**2+2*Yv-2)/(2*Min) - mp.log(Min)/2)
    P = [0, 1] if (mu == 0 or mu >= 1) else [0, mp.sqrt(mu), mp.sqrt(mp.sqrt(mu)), 1]
    ct = mp.quad(ctY, P) if mu > 0 else None
    return 2*(two - f2*ct) if ct is not None else (2*two, f2)
if __name__ == '__main__':
    which = sys.argv[1]; mu = sys.argv[2]; nu = sys.argv[3]
    level = int(sys.argv[4]) if len(sys.argv) > 4 else 8
    xlevel = int(sys.argv[5]) if len(sys.argv) > 5 else 16
    t0 = time.time()
    v = unit(which, mu, nu, level, xlevel)
    print(which, mu, nu, level, xlevel, v, f'{time.time()-t0:.0f}s', flush=True)
