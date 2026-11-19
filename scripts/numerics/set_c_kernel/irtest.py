import mpmath as mp, units2dfix as U, time
mp.mp.dps = 25
t = mp.mpf(1)
for l2 in (mp.mpf('1e-20'), mp.mpf('1e-30')):
    t0=time.time()
    a = U.S(l2, t, 6); cc = -2*U.F2(t)*U.ctC(l2)
    print(l2, 'S(0,t)=', a, ' Cct=', cc, ' sum=', a+cc, f'{time.time()-t0:.0f}s', flush=True)
