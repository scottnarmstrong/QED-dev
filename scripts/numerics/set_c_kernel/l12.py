import mpmath as mp, units2dfix as U, time
mp.mp.dps = 25
t = mp.mpf(1); l2 = mp.mpf('1e-40')
t0 = time.time()
a = U.L(t, l2, 12); b = U.L(l2, t, 12); c = U.S(t, l2, 12)
print('L12 t=1 l2=1e-40 Lpair=', a+b, 'S(t,0)=', c, f'{time.time()-t0:.0f}s', flush=True)
