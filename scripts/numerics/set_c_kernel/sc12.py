import mpmath as mp, units2dfix as U, time
mp.mp.dps = 25
t = mp.mpf(1); l2 = mp.mpf('1e-40')
t0 = time.time()
a = U.S(l2, t, 12); cc = -2*U.F2(t)*U.ctC(l2, 24)
print('SC12 t=1 l2=1e-40 S(0,t)=', a, 'Cct=', cc, 'sum=', a+cc, f'{time.time()-t0:.0f}s', flush=True)
