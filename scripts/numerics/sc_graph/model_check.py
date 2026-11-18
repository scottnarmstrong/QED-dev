#!/usr/bin/env python3
"""The exact formulas R_i of symbolic_c2.py against the finite-difference model of lean_class.py
(paramNum by finite differences along the eigenvectors of G, independent of Wick's rule), at
random points with all eight parameters positive. NOT a proof.
Run: SC_CACHE=<dir> nice -n 10 python3 model_check.py   (uses the cache of engine_check.py)"""
import os, sys
import numpy as np
import sympy as sp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from lean_class import Cls, parts_c2, K
import engine_check as EC
import symbolic_c2 as S

R = EC.formulas()
g = {k: sp.Symbol(k) for k in ('zo', 'Y', 'y3', 'y4', 'za', 'zb')}
z = sp.symbols('z0:8')
rng = np.random.default_rng(11)
for name in ('Sp', 'Sm', 'Cp', 'Cm'):
    cls = Cls(name)
    for trial in range(2):
        zz = rng.random(8) + 0.05; zz /= zz.sum()
        sub = S.GROUPS[name](z, g)
        gv = {sp.Symbol(str(k)): None for k in ()}
        # group values from zz
        vals = {}
        for k, v in sub.items():
            pass
        if name == 'Sp':
            gval = {g['zo']: zz[0] + zz[1] + zz[3], g['Y']: zz[2]}
        elif name == 'Sm':
            gval = {g['zo']: zz[0] + zz[2] + zz[3], g['Y']: zz[1]}
        elif name == 'Cp':
            gval = {g['zo']: zz[0] + zz[1], g['y3']: zz[2], g['y4']: zz[3]}
        else:
            gval = {g['zo']: zz[2] + zz[3], g['y3']: zz[1], g['y4']: zz[0]}
        if name == 'Cm':
            gval.update({g['za']: zz[5] + zz[7], g['zb']: zz[4] + zz[6]})
        else:
            gval.update({g['za']: zz[4] + zz[6], g['zb']: zz[5] + zz[7]})
        gval.update({z[i]: zz[i] for i in range(8)})
        exact = [complex(sp.N(r.subs(gval))) for r in R[name]]
        fd = parts_c2(cls, zz) * K
        print(name, 'exact', np.round(exact, 9), ' model', np.round(fd, 9))
