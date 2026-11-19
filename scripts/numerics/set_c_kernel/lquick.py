import mpmath as mp, units2dfix as U, time
mp.mp.dps = 22
t = mp.mpf(1)
for l2 in (mp.mpf('1e-20'), mp.mpf('1e-24')):
    t0 = time.time()
    a = U.L(t, l2, 6); b = U.L(l2, t, 6); c = U.S(t, l2, 6)
    print(l2, 'L(t,0)=', a, 'L(0,t)=', b, 'pair=', a+b, 'S(t,0)=', c, f'{time.time()-t0:.0f}s', flush=True)
