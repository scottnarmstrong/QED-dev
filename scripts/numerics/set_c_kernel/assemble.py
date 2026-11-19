"""Assemble check 2: A_(c)(t) from the unit placements vs the Stieltjes transform of lambda4.
Reads run2d*.json (L, S, corner counterterm) and run3d*.out (C, X two-loop parts)."""
import json, re, glob, mpmath as mp
mp.mp.dps = 30
r2 = {}
for fn in sorted(glob.glob('run2d*.json')):
    r2.update(json.load(open(fn)))
v3 = {}   # (name, mu, nu) -> {level: value}
for fn in sorted(glob.glob('run3d*.out')):
    for line in open(fn):
        f = line.split()
        if len(f) < 6 or f[0] not in ('C', 'X'):
            continue
        nums = re.findall(r"-?\d+\.\d+(?:e-?\d+)?", line.split(None, 5)[5])
        v3.setdefault((f[0], f[1], f[2]), {})[int(f[3])] = mp.mpf(nums[0])
def best(k):
    d = v3[k]; return d[max(d)], max(d)
for t in ('1', '4'):
    if t + '.0_stieltjes' not in r2: continue
    st = mp.mpf(r2[t + '.0_stieltjes'])
    for k in sorted(k for k in r2 if k.startswith(t + '.0_') and 'stieltjes' not in k):
        d = {a: mp.mpf(b) for a, b in r2[k].items()}
        try:
            (ct0, lc1), (c0t, lc2), (xt0, lx1), (x0t, lx2) = (best(('C', t, '0')), best(('C', '0', t)),
                                                               best(('X', t, '0')), best(('X', '0', t)))
        except KeyError as e:
            print('missing', e); continue
        parts = [('L(t,0)+L(0,t)', d['L1'] + d['L2']), ('S(t,0)', d['S1']),
                 ('S(0,t)+Cct(0,t)', d['S2'] + d['Cct']), (f'C(t,0) [lev {lc1}]', ct0),
                 (f'C2loop(0,t) [lev {lc2}]', c0t), (f'X(t,0) [lev {lx1}]', xt0),
                 (f'X(0,t) [lev {lx2}]', x0t)]
        A = mp.fsum(p for _, p in parts)
        print(f'\nt = {t}, massless line lambda^2 = {k.split("_")[1]}')
        for a, b in parts: print(f'   {a:24s} {mp.nstr(b, 20)}')
        print(f'   {"A_(c)(t)":24s} {mp.nstr(A, 20)}')
        print(f'   {"int lam4 Q/(Q+t)":24s} {mp.nstr(st, 20)}')
        print(f'   difference {mp.nstr(A - st, 3)};  X(t,0)-X(0,t) = {mp.nstr(xt0 - x0t, 3)}')
print('\nall 3D values:')
for k, d in sorted(v3.items()):
    for lev, v in sorted(d.items()): print('  ', k, lev, mp.nstr(v, 22))
