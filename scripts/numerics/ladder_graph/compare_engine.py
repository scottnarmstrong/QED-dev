import sys, math
import numpy as np
import os; sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__)))); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lean_ladder import *
import two_loop_units as T

g = T.graph('L')
lam, Lam = 0.3, 2.0
mc = T.mass_combos(g, lam ** 2, Lam ** 2)

def f_eng(Zg):
    return g.integrand(np.array([Zg]), mc)[0]

def I_lean(Zg, n=6):
    zA, Y, za, zb = Zg
    x, w = np.polynomial.legendre.leggauss(n); s = (x + 1) / 2; w = w / 2
    tot = 0
    for i in range(n):
        for j in range(n):
            z = np.array([s[i] * zA, s[j] * Y, (1 - s[j]) * Y, (1 - s[i]) * zA, za, zb, 0, 0])
            t1, t2, t3 = parts_c2(z, 1.0)
            Vc = V0_nomass(z, 1.0)
            Vs = {(a, b): Vc + za * ma + zb * mb for a, ma in ((1, lam**2), (-1, Lam**2))
                  for b, mb in ((1, lam**2), (-1, Lam**2))}
            val = sum(a * b * (t1 * V ** -2 / 6 + t2 * V ** -1 / 2) for (a, b), V in Vs.items())
            tot += w[i] * w[j] * zA * Y * val
            if i == 0 and j == 0:
                print('   t3 (should be 0):', t3, ' t1,t2:', t1, t2)
    return tot

rng = np.random.default_rng(7)
for trial in range(3):
    Zg = rng.random(4); Zg /= Zg.sum()
    a = 16 * math.pi ** 4 / (64 * 1j) * I_lean(Zg)
    b = f_eng(Zg)
    print(Zg, 'lean-normalized', a, ' engine', b, ' ratio', a / b)
