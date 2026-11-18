#!/usr/bin/env python3
"""The pointwise formulas c2[T_i] = (Lambda^2 - m_gamma^2)^2 / K * R_i (symbolic_c2.py), merged over
the line splits and the Pauli-Villars pairs, against the engine integrand of ../two_loop_units.py
(graphs S+, S-, C+, C-). NOT a proof.

Merging: the electron groups give the volume factors (zo^2/2 for the three outer lines of S+-,
zo for the outer pair of C+-; the C+- formulas are affine in the split, so the split average is
the value at the midpoint), and the two Pauli-Villars pairs give the signed sum over the photon
masses of R1/(6 V^2) + R2/(2 V), V = E + mu_a za + mu_b zb.
Run: nice -n 10 python3 engine_check.py
"""
import os, sys, pickle
import numpy as np
import sympy as sp
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
import two_loop_units as T
import symbolic_c2 as S

lam, Lam = 0.3, 2.0
CACHE = os.path.join(os.environ.get('SC_CACHE', '/tmp'), 'sc_graph_R.pkl')


def formulas():
    if os.path.exists(CACHE):
        return pickle.load(open(CACHE, 'rb'))
    out = {}
    for name in ('Sp', 'Sm', 'Cp', 'Cm'):
        out[name] = S.grouped(name, S.main(name))
    pickle.dump(out, open(CACHE, 'wb'))
    return out


def massless_V(name, vals):
    """E = V(q = 0) without photon masses, from the Symanzik data (m = 1)."""
    z, U, a, b, C = S.symanzik_data(name)
    return z, U


def main():
    R = formulas()
    g = {k: sp.Symbol(k) for k in ('zo', 'Y', 'y3', 'y4', 'za', 'zb')}
    z = sp.symbols('z0:8')
    eng_names = {'Sp': 'S+', 'Sm': 'S-', 'Cp': 'C+', 'Cm': 'C-'}
    rng = np.random.default_rng(5)
    for name in ('Sp', 'Sm', 'Cp', 'Cm'):
        gr = T.graph(eng_names[name])
        mc = T.mass_combos(gr, lam ** 2, Lam ** 2)
        # massless V at q = 0 in group variables: put each group on one line
        zz, U, a_, b_, C_ = S.symanzik_data(name)
        sub = S.GROUPS[name](zz, g)
        split = {'Sp': [z[1], z[3]], 'Sm': [z[2], z[3]], 'Cp': [z[1]], 'Cm': [z[2]]}[name]
        # V0 = sum z (m^2 + p.p) - B A^-1 B with p.p = p.p' = -1 at q = 0, m = 1
        A6 = S.LOOP[name]; A = [A6[S.PVL[i]] for i in range(8)]
        M = sp.Matrix(2, 2, lambda s, t: sum(zz[i] * A[i][s] * A[i][t] for i in range(8)))
        Bv = [sum(zz[i] * A[i][s] for i in range(8) if S.PVL[i] < 4) for s in range(2)]
        E = sum(zz[i] for i in range(4)) * 0 + \
            (-(sp.Matrix(Bv).T * M.inv() * sp.Matrix(Bv))[0] * (-1)) * 0
        # direct: V0 = sum_e z_e (1 - 1) + B^T A^-1 B (since p.p = -1): E = B^T A^-1 B
        E = sp.together((sp.Matrix(Bv).T * M.adjugate() * sp.Matrix(Bv))[0] / M.det())
        Eg = sp.together(E.subs(sub))
        if name in ('Sp', 'Sm'):
            vol = g['zo'] ** 2 / 2
            Rs = [r.subs({s: 0 for s in split}) for r in R[name][:2]]
            Eg = Eg.subs({s: 0 for s in split})
            vars_ = (g['zo'], g['Y'], g['za'], g['zb'])
        else:
            vol = g['zo']
            Rs = [r.subs(split[0], g['zo'] / 2) for r in R[name][:2]]
            Eg = Eg.subs(split[0], g['zo'] / 2)
            vars_ = (g['zo'], g['y3'], g['y4'], g['za'], g['zb'])
        Eg = sp.simplify(Eg.subs({z[6]: 0, z[7]: 0}))
        fR = sp.lambdify(vars_, [vol * Rs[0], vol * Rs[1], Eg])
        for trial in range(3):
            v = rng.random(len(vars_)); v /= v.sum()
            r1, r2, e = fR(*v)
            tot = 0
            for sa, ma in ((1, lam ** 2), (-1, Lam ** 2)):
                for sb, mb in ((1, lam ** 2), (-1, Lam ** 2)):
                    V = e + ma * v[-2] + mb * v[-1]
                    tot += sa * sb * (r1 / (6 * V ** 2) + r2 / (2 * V))
            # engine group order: S+: [zo, Y, za, zb]; C+: [zo, y3, y4, za, zb]; S-, C- likewise
            # (C-: the engine orders its groups (y4, y3, zo, zb, za))
            ev = v if name != 'Cm' else np.array([v[2], v[1], v[0], v[4], v[3]])
            eng = gr.integrand(np.array([ev]), mc)[0]
            print(name, 'groups', [len(x) for x in gr.groups], 'formula', tot, ' engine', eng,
                  ' ratio', tot / eng)


if __name__ == '__main__':
    main()
