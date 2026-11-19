import pickle, sys, time, sympy as sp, mpmath as mp
sys.path.insert(0, '/home/scott/QED-dev/scripts/numerics')
import two_loop_unit_integrals as T
d = pickle.load(open('units.pkl', 'rb'))['out']
x = sp.Symbol('x', positive=True); y3, y4 = sp.symbols('y3 y4', positive=True)
for name in ('L','S+','C+','X'):
    G = sp.expand_log(d[name]['E'] - d[name]['e0'], force=True)
    print(name, 'ops', sp.count_ops(G))
    Y = sp.Symbol('Y', positive=True)
    args = (Y, x, T.MS, T.hS, T.betaS) if name in ('L','S+') else (y3, y4, x, T.MS, T.hS, T.betaS)
    f = sp.lambdify(args, G, 'mpmath')
    mp.mp.dps = 30
    vals = [mp.mpf('0.3'), mp.mpf('0.45'), mp.mpf('0.6'), mp.mpf('0.2'), mp.mpf('0.7'), mp.mpf('0.15')]
    if name in ('L','S+'): vals = [mp.mpf('0.3'), mp.mpf('0.6'), mp.mpf('0.2'), mp.mpf('0.7'), mp.mpf('0.21')]
    t0 = time.time()
    for i in range(200): v = f(*vals)
    print('  t/pt ms', (time.time()-t0)/200*1e3, v)
