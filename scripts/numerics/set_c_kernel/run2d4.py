import mpmath as mp, time, json
import units2dfix as U
import blp
res = {}
for t in (4,):
    mp.mp.dps = 25
    t = mp.mpf(t)
    for l2 in (mp.mpf('1e-40'),):
        t0 = time.time()
        a = U.L(t, l2, 8); b = U.L(l2, t, 8); c = U.S(t, l2, 8); dd = U.S(l2, t, 8)
        cc = -2*U.F2(t)*U.ctC(l2)
        ir = a + b + c + dd + cc
        print(f't={t} l2={l2}: L(t,0)={a} L(0,t)={b} S(t,0)={c} S(0,t)={dd} Cct(0,t)={cc}')
        print(f'    sum = {ir}   ({time.time()-t0:.0f}s)', flush=True)
        res[f'{t}_{l2}'] = dict(L1=str(a), L2=str(b), S1=str(c), S2=str(dd), Cct=str(cc), sum=str(ir))
    mp.mp.dps = 30
    st = blp.Astieltjes(t)
    print(f't={t}: Stieltjes int lam4 Q2/(Q2+t) = {st}', flush=True)
    res[f'{t}_stieltjes'] = str(st)
    json.dump(res, open('run2d4.json', 'w'), indent=1)
