#!/usr/bin/env python3
"""The xi-integration of the crossed-ladder unit (step 4.5.2 of docs/TWO-LOOP-UNITS.md).
NOT a proof by itself: generates the rational data of QED/TwoLoop/UnitXXi{Defs,Rat,Ends}.lean,
whose identities Lean checks, and checks every step here in exact rational arithmetic.

With z2 = Y xi, z3 = Y (1 - xi), the integrand Phi_X = crossedPhi of
QED/TwoLoop/UnitXCloseOuterInt.lean (read from the Lean definitions of
QED/TwoLoop/UnitXCloseOuter.lean) is, eq. (4.5),
    Y Phi = R1 + RY log Y + Rx log xi + RA log(1 - Y xi) + RB log(xi + Y - 2 Y xi).
Steps:
 1. the letter coefficients R (crossedPhi_yxi);
 2. a xi-antiderivative F (xiF): partial fractions in xi (poles at 0, 1; the 1/(2 xi - 1) poles of
    Rx and RB have opposite residues r and give (r/2)(Li2(kappa (1 - 2 xi)) - Li2(1 - 2 xi)),
    kappa = 1 - 2Y); every coefficient of a log is a partial-fraction form pfXi;
 3. F' = Y Phi, one letter at a time (exact);
 4. the endpoint forms of F at xi -> 0+ (Taylor remainders lr2) and xi -> 1- (lr3), with
    coefficients regular at the endpoint (exact);
 5. K = F(1-) - F(0+); with the identities (4.6) it equals crossedKernel of
    QED/TwoLoop/UnitXKernelBasic.lean (read from the Lean source) exactly;
 6. numerics: (4.6) at three points (40 digits), and int_0^1 Y Phi dxi (quadrature of the Lean
    integrand) against crossedKernel at Y = 0.3, 0.7.
Run (from this directory, ~1 min):
    nice -n 10 python3 xi_integration.py            # checks only
    nice -n 10 python3 xi_integration.py --check    # also: generated blocks occur in the Lean files
    nice -n 10 python3 xi_integration.py --emit DIR # write the generated blocks to DIR
"""
import argparse
import os
import re
import sys
import time

import mpmath as mp
import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.normpath(os.path.join(HERE, '..', '..', '..', 'QED', 'TwoLoop'))

Y, x, t = sp.symbols('Y xi t', positive=True)
M, c, B = sp.symbols('M c B')


# ---------------------------------------------------------------- reading Lean definitions
def lean_defs(path):
    """{name: (args, body)} for the `noncomputable def name (args : ℝ) : ℝ :=` blocks of a file."""
    txt = open(path).read()
    out = {}
    for m in re.finditer(r'noncomputable def (\S+) \(([^)]*) : ℝ\) : ℝ :=\n(.*?)\n\n', txt, re.S):
        out[m.group(1)] = (m.group(2).split(), m.group(3))
    return out


def outer_coefficients():
    """the coefficients r_k, c, kappa of K = -Phi_X, from QED/TwoLoop/UnitXCloseOuter.lean."""
    defs = lean_defs(os.path.join(LEAN, 'UnitXCloseOuter.lean'))
    env = {}

    def ev(name):
        if name in env:
            return env[name]
        _, body = defs[name]
        b = '(' + body.replace('^', '**').replace('\n', ' ') + ')'
        loc = {}
        for n in sorted(defs, key=len, reverse=True):
            pat = re.escape(n) + r' (?:M|_M) (?:c|_c)(?: (?:B|_B))?'
            if re.search(pat, b):
                key = 'v%d' % len(loc)
                b = re.sub(pat, key, b)
                loc[key] = ev(n)
        loc.update({'M': M, 'c': c, 'B': B})
        env[name] = sp.sympify(eval(b, {}, loc))
        return env[name]
    names = ['xr₂', 'xr₃', 'xr₄', 'xr₅', 'xc₂₀', 'xc₃₀', 'xc₂ₑ', 'xc₃ₑ', 'xκe', 'xκp', 'xκq']
    return {n: ev(n) for n in names}


def lean_kernel():
    """crossedKernel of QED/TwoLoop/UnitXKernelBasic.lean in the symbols L, D, a, b, pi."""
    defs = lean_defs(os.path.join(LEAN, 'UnitXKernelBasic.lean'))
    L, D, a, b = sp.symbols('L D a b')
    rho = sp.sympify(defs['crossedRho'][1].replace('^', '**').replace('\n', ' '), locals={'Y': Y})
    s = defs['crossedKernel'][1].replace('\n', ' ')
    for old, new in [('Li₂ Y', 'L'), ('crossedD Y', 'D'), ('crossedRho Y', 'rho'),
                     ('log (1 - Y)', 'b'), ('log Y', 'a'), ('π', 'pi'), ('^', '**')]:
        s = s.replace(old, new)
    return sp.sympify(s, locals={'Y': Y, 'L': L, 'D': D, 'a': a, 'b': b, 'rho': rho, 'pi': sp.pi})


# ---------------------------------------------------------------- Lean printing
def lean_poly(e):
    return sp.sstr(e, order='lex').replace('**', ' ^ ').replace('*', ' * ').replace('xi', 'ξ')


def _atomic(s):
    return re.fullmatch(r'[\w\.]+( \^ \d+)?', s) is not None


def lean_rat(R):
    R = sp.factor(sp.cancel(R))
    n, d = sp.fraction(R)
    ns = lean_poly(sp.factor(n)) if len(str(sp.factor(n))) < 60 else lean_poly(sp.expand(n))
    ds = lean_poly(d)
    if not _atomic(ns):
        ns = '(' + ns + ')'
    if d == 1:
        return ns
    if not _atomic(ds):
        ds = '(' + ds + ')'
    return '(' + ns + ' / ' + ds + ')'


def wrap(line, indent=4, width=100):
    if len(line) <= width:
        return line
    lead = len(line) - len(line.lstrip())
    raw = line.strip().split(' ')
    toks, i = [], 0
    while i < len(raw):
        tk = raw[i]
        while i + 2 < len(raw) and raw[i + 1] == '^':
            tk = tk + ' ^ ' + raw[i + 2]
            i += 2
        if toks and tk in ('+', '-', '*', '/', '=', '≤', '<'):
            toks[-1] = toks[-1] + ' ' + tk
        else:
            toks.append(tk)
        i += 1
    out, cur = [], ' ' * lead
    for tk in toks:
        cand = cur + (' ' if cur.strip() else '') + tk
        if len(cand) > width and cur.strip():
            out.append(cur.rstrip())
            cur = ' ' * (lead + indent) + tk
        else:
            cur = cand
    out.append(cur.rstrip())
    return '\n'.join(out)


def wrapall(text):
    return '\n'.join(wrap(l) for l in text.split('\n'))


# ---------------------------------------------------------------- partial fractions in xi
SLOTS = [('x', 0), ('x', 1), ('x', 2), ('x', -1), ('x', -2), ('o', -1), ('o', -2), ('o', -3)]


def pf(R):
    """{('x', n): coefficient of xi^n, ('o', n): coefficient of (xi - 1)^n}."""
    out = {}
    for term in sp.Add.make_args(sp.apart(sp.cancel(R), x)):
        A, rest = term.as_independent(x, as_Add=False)
        A2, rest = sp.factor(rest).as_independent(x, as_Add=False)
        A = A * A2
        if rest == 1:
            k = ('x', 0)
        elif rest == x:
            k = ('x', 1)
        elif rest.is_Pow and rest.base == x:
            k = ('x', int(rest.exp))
        elif sp.expand(rest - (x - 1)) == 0:
            k = ('o', 1)
        elif rest.is_Pow and sp.expand(rest.base - (x - 1)) == 0:
            k = ('o', int(rest.exp))
        else:
            raise ValueError(term)
        out[k] = sp.factor(out.get(k, 0) + A)
    return out


def pf_eval(p):
    return sum(v * (x ** n if k == 'x' else (x - 1) ** n) for (k, n), v in p.items())


# ---------------------------------------------------------------- steps 1-5
def letters(o):
    """step 1: the letter coefficients of Y Phi at z2 = Y xi, z3 = Y (1 - xi)."""
    sub = {M: Y * x, c: Y * (1 - x)}
    g = Y * x * (1 - Y)
    r2, r3, r4, r5 = [o[n].subs(sub) for n in ['xr₂', 'xr₃', 'xr₄', 'xr₅']]
    c20, c30, c2e, c3e = [o[n].subs(sub) for n in ['xc₂₀', 'xc₃₀', 'xc₂ₑ', 'xc₃ₑ']]
    ke, kp, kq = [o[n].subs(sub) for n in ['xκe', 'xκp', 'xκq']]
    e = Y * x * Y * (1 - x)
    Q = -(c20 / g) - c30 / (2 * g ** 2) - c2e / (g + e) - c3e / (2 * (g + e) ** 2)
    S = -(r2 / g) - r3 / (2 * g ** 2) - r4 / (3 * g ** 3) - r5 / (4 * g ** 4)
    assert sp.cancel(ke + kp + kq) == 0
    return {'1': sp.factor(sp.cancel(-Y * Q)), 'Y': sp.factor(sp.cancel(-Y * S)),
            'x': sp.factor(sp.cancel(-Y * (ke + kp))), 'A': sp.factor(sp.cancel(-Y * (S + ke))),
            'B': sp.factor(sp.cancel(Y * (S - kq)))}


LETTER = {'x': x, 'A': 1 - Y * x, 'B': x + Y - 2 * Y * x}


def antiderivative(co):
    """step 2: F = P0 + Px log xi + PA log A + PB log B + PY log Y + dilogarithm terms.
    Returns ({'1','x','A','B','Y'}: coefficient, {argument: coefficient of Li(argument)})."""
    lx, l1x, lA, lB, lY, l1Y = sp.symbols('lx l1x lA lB lY l1Y')
    atom = {'x': lx, 'A': lA, 'B': lB}
    linear = [(x, lx), (x - 1, l1x), (1 - Y * x, lA), (x + Y - 2 * Y * x, lB)]
    Li = sp.Function('Li')

    def ratint(R):
        res = 0
        for term in sp.Add.make_args(sp.apart(sp.cancel(R), x)):
            if not term.has(x):
                res += term * x
                continue
            A, rest = term.as_independent(x, as_Add=False)
            base, n = (rest.base, int(rest.exp)) if rest.is_Pow else (rest, 1)
            if n > 0:
                res += sp.integrate(term, x)
                continue
            p = sp.diff(base, x)
            if n == -1:
                hit = [la for u, la in linear if not sp.cancel(base / u).has(x)]
                assert len(hit) == 1, term
                res += A / p * hit[0]
            else:
                res += A * base ** (n + 1) / ((n + 1) * p)
        return res
    rx = sp.cancel(sp.limit(co['x'] * (2 * x - 1), x, sp.Rational(1, 2)))
    rB = sp.cancel(sp.limit(co['B'] * (2 * x - 1), x, sp.Rational(1, 2)))
    assert sp.cancel(rx + rB) == 0
    pieces = {'x': sp.cancel(co['x'] - rx / (2 * x - 1)), 'A': co['A'],
              'B': sp.cancel(co['B'] - rB / (2 * x - 1))}
    al0 = {'A': (1, -Y), 'B': (Y, 1 - 2 * Y)}
    al1 = {'A': (1 - Y, Y), 'B': (1 - Y, -(1 - 2 * Y)), 'x': (1, -1)}
    logal = {1: 0, Y: lY, 1 - Y: l1Y}
    F = 0
    for nm, fac in (('1', 1), ('Y', lY)):
        for (k, n), A in pf(co[nm]).items():
            base, la = (x, lx) if k == 'x' else (x - 1, l1x)
            F += fac * A * (la if n == -1 else base ** (n + 1) / (n + 1))
    for L, R in pieces.items():
        ell = LETTER[L]
        for (k, n), A in pf(R).items():
            if n == -1:
                if k == 'x':
                    if L == 'x':
                        F += A * lx ** 2 / 2
                    else:
                        al, be = al0[L]
                        F += A * (logal[al] * lx - Li(sp.cancel(-be * x / al)))
                else:
                    al, be = al1[L]
                    F += A * (logal[al] * l1x - Li(sp.cancel(-be * (1 - x) / al)))
                continue
            P = A * (x if k == 'x' else x - 1) ** (n + 1) / (n + 1)
            F += P * atom[L] - ratint(sp.cancel(P * sp.diff(ell, x) / ell))
    F += rx / 2 * (Li(sp.expand((1 - 2 * Y) * (1 - 2 * x))) - Li(1 - 2 * x))
    F = sp.expand(F)
    lis = sorted(F.atoms(Li), key=str)
    P = sp.Poly(F, lx, l1x, lA, lB, lY, l1Y, *lis)
    coef, dil = {}, {}
    names = ['x', 'l1x', 'A', 'B', 'Y', 'l1Y']
    for m, cf in zip(P.monoms(), P.coeffs()):
        nz = [i for i, e in enumerate(m) if e]
        if not nz:
            coef['1'] = sp.factor(cf)
        else:
            assert len(nz) == 1 and m[nz[0]] == 1, m
            i = nz[0]
            if i < 6:
                coef[names[i]] = sp.factor(cf)
            else:
                dil[sp.factor(lis[i - 6].args[0])] = sp.factor(cf)
    assert set(coef) == {'1', 'x', 'A', 'B', 'Y'}, coef.keys()
    return coef, dil


def find_dil(dil, arg):
    hit = [v for k, v in dil.items() if sp.simplify(k - arg) == 0]
    assert len(hit) == 1, arg
    return hit[0]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--check', action='store_true', help='generated blocks occur in the Lean files')
    ap.add_argument('--emit', metavar='DIR', help='write the generated blocks to DIR')
    args = ap.parse_args()
    t0 = time.time()
    o = outer_coefficients()
    co = letters(o)
    print(f'1. letters of Y Phi: denominators', {k: str(sp.fraction(v)[1]) for k, v in co.items()})
    coef, dil = antiderivative(co)
    p = {k: pf(v) for k, v in coef.items()}
    assert all(set(v) <= set(SLOTS) for v in p.values())
    cL = find_dil(dil, Y * x)
    cq = find_dil(dil, 1 - x)
    assert sp.cancel(find_dil(dil, -Y * (1 - x) / (1 - Y)) - cq) == 0
    assert sp.cancel(find_dil(dil, (1 - 2 * Y) * (1 - x) / (1 - Y)) + cq) == 0
    assert sp.cancel(find_dil(dil, 1 - 2 * x) - 1 / (2 * Y ** 2)) == 0
    assert sp.cancel(find_dil(dil, (1 - 2 * Y) * (1 - 2 * x)) + 1 / (2 * Y ** 2)) == 0
    cD = find_dil(dil, (2 * Y - 1) * x / Y)
    print(f'2. antiderivative: {len(dil)} dilogarithm terms ({time.time() - t0:.0f} s)')
    # 3. F' = Y Phi, letter by letter (the dilogarithm derivatives in the letters)
    R0, Px, PA, PB, PY = (coef[k] for k in ['1', 'x', 'A', 'B', 'Y'])
    d = lambda f: sp.diff(f, x)
    chk = [d(R0) + Px / x + PA * (-Y / (1 - Y * x)) + PB * ((1 - 2 * Y) / (x + Y - 2 * Y * x)) - co['1'],
           d(Px) + cq / (1 - x) + 1 / (1 - 2 * x) / Y ** 2 - co['x'],
           d(PA) - cL / x + cq / (1 - x) - co['A'],
           d(PB) - cq / (1 - x) - 1 / (1 - 2 * x) / Y ** 2 - cD / x - co['B'],
           d(PY) + cD / x - co['Y']]
    assert all(sp.cancel(e) == 0 for e in chk)
    print('3. F\' = Y Phi: five letter identities exact')
    # 4. endpoint forms
    xB = (2 * Y - 1) / Y * x
    s = 1 - x
    yA, yB = -(Y / (1 - Y)) * s, (1 - 2 * Y) / (1 - Y) * s
    T2 = lambda z: z + z ** 2 / 2
    T3 = lambda z: z + z ** 2 / 2 + z ** 3 / 3
    ends = {'xiU0': R0 - PA * T2(Y * x) - PB * T2(xB), 'xiW0': PB + PY, 'xiV0': Px / x,
            'xiA0': PA * x ** 2, 'xiB0': PB * x ** 2,
            'xiU1': R0 - Px * T3(s) - PA * T3(yA) - PB * T3(yB), 'xiW1Y': PY, 'xiW1': PA + PB,
            'xiX1': Px * s ** 3, 'xiA1': PA * s ** 3, 'xiB1': PB * s ** 3}
    ends = {k: sp.factor(sp.cancel(v)) for k, v in ends.items()}
    for k, v in ends.items():
        den = sp.fraction(v)[1]
        pt = 0 if k.endswith('0') else 1
        assert sp.simplify(den.subs(x, pt)) != 0, k
    vals = {k: sp.factor(ends[k].subs(x, 0)) for k in ['xiU0', 'xiW0']}
    vals.update({k: sp.factor(ends[k].subs(x, 1)) for k in ['xiU1', 'xiW1Y', 'xiW1']})
    print('4. endpoint forms: coefficients regular at the endpoints; values', vals)
    # 5. K = F(1-) - F(0+) and (4.6)
    lY, l1Y, L, Pp, Mm, dA, dB, dC = sp.symbols('lY l1Y L Pp Mm dA dB dC')
    pi2 = sp.pi ** 2
    F0 = vals['xiU0'] + vals['xiW0'] * lY + cq * (pi2 / 6 + dA - dB) + (pi2 / 6 - Pp) / (2 * Y ** 2)
    F1 = (vals['xiU1'] + vals['xiW1Y'] * lY + vals['xiW1'] * l1Y + cL * L
          + (-pi2 / 12 - Mm) / (2 * Y ** 2) + cD * dC)
    Dv = Pp - Mm
    rep = {dA: -L - l1Y ** 2 / 2, dC: -Dv - L - lY ** 2 / 2 + pi2 / 12,
           dB: Dv + L - l1Y ** 2 / 2 + lY * l1Y - pi2 / 12}
    K = sp.expand((F1 - F0).subs(rep))
    Ls, Ds, a, b = sp.symbols('L D a b')
    KX = sp.expand(lean_kernel().subs({Ds: Pp - Mm, Ls: L, a: lY, b: l1Y}))
    diff = sp.Poly(sp.expand(K - KX), L, Pp, Mm, lY, l1Y, sp.pi)
    assert all(sp.cancel(cf) == 0 for cf in diff.coeffs())
    print('5. F(1-) - F(0+) with (4.6) equals crossedKernel of UnitXKernelBasic.lean exactly')
    # 6. numerics
    mp.mp.dps = 40
    worst = 0
    for y in (mp.mpf(1) / 7, mp.mpf(1) / 2 + mp.mpf(1) / 11, mp.mpf(9) / 10):
        Dn = mp.polylog(2, 1 - 2 * y) - mp.polylog(2, 2 * y - 1)
        Ln, A_, B_ = mp.polylog(2, y), mp.log(y), mp.log(1 - y)
        worst = max(worst, abs(mp.polylog(2, -y / (1 - y)) - (-Ln - B_ ** 2 / 2)),
                    abs(mp.polylog(2, (2 * y - 1) / y) - (-Dn - Ln - A_ ** 2 / 2 + mp.zeta(2) / 2)),
                    abs(mp.polylog(2, (1 - 2 * y) / (1 - y))
                        - (Dn + Ln - B_ ** 2 / 2 + A_ * B_ - mp.zeta(2) / 2)))
    print('6. (4.6) at three points: max deviation', mp.nstr(worst, 3))
    S = sum(-o[f'xr{k}'] / ((i + 1) * B ** (i + 1)) for i, k in enumerate(['₂', '₃', '₄', '₅']))
    Q = (-(o['xc₂₀'] / B) - o['xc₃₀'] / (2 * B ** 2) - o['xc₂ₑ'] / (B + M * c)
         - o['xc₃ₑ'] / (2 * (B + M * c) ** 2))
    Lg = 2 * sp.log(M + c) + sp.log(B + M * c) - sp.log(B + (M + c) * M) - sp.log(B + (M + c) * c)
    Kx = (Q + S * Lg + o['xκe'] * sp.log(B + M * c) + o['xκp'] * sp.log(B + (M + c) * M)
          + o['xκq'] * sp.log(B + (M + c) * c))
    phi = sp.lambdify((M, c), -Kx.subs(B, M * (1 - M - c)), 'mpmath')
    kern = sp.lambdify((Y, Ls, Ds, a, b), lean_kernel(), 'mpmath')
    for y in (mp.mpf('0.3'), mp.mpf('0.7')):
        def f(xi):
            m = min(xi, 1 - xi)
            if m < mp.mpf(10) ** -25:
                return mp.mpf(0)
            with mp.workdps(30 + 5 * int(-mp.log10(m))):
                return y * phi(y * xi, y * (1 - xi))
        mp.mp.dps = 25
        v = mp.quad(f, [0, mp.mpf(1) / 4, mp.mpf(1) / 2, mp.mpf(3) / 4, 1])
        with mp.workdps(40):
            kv = kern(y, mp.polylog(2, y), mp.polylog(2, 1 - 2 * y) - mp.polylog(2, 2 * y - 1),
                      mp.log(y), mp.log(1 - y))
        print(f'   Y = {mp.nstr(y, 2)}: int_0^1 Y Phi dxi = {mp.nstr(v, 20)},  K_X = {mp.nstr(kv, 20)},'
              f'  difference {mp.nstr(v - kv, 3)}')
    # generated Lean blocks
    blocks = {}
    out = []
    docs = {'xiR0': 'The rational part of the `ξ`-antiderivative.',
            'xiPx': 'The coefficient of `log ξ` in the `ξ`-antiderivative.',
            'xiPA': 'The coefficient of `log (1 - Y ξ)` in the `ξ`-antiderivative.',
            'xiPB': 'The coefficient of `log (ξ + Y - 2 Y ξ)` in the `ξ`-antiderivative.',
            'xiPY': 'The coefficient of `log Y` in the `ξ`-antiderivative.'}
    key = {'xiR0': '1', 'xiPx': 'x', 'xiPA': 'A', 'xiPB': 'B', 'xiPY': 'Y'}
    for name, k in key.items():
        al = [(lean_rat(p[k][s_]) if s_ in p[k] else '0') for s_ in SLOTS]
        args_ = '\n'.join('    ' + a_ for a_ in al)
        argsD = '\n'.join('    ' + a_ for a_ in al[1:])
        out.append(f"/-- {docs[name]} -/\nnoncomputable def {name} (Y ξ : ℝ) : ℝ :=\n  pfXi\n{args_}\n"
                   f"    ξ\n\n/-- The `ξ`-derivative of `{name}`. -/\nnoncomputable def {name}D (Y ξ : ℝ)"
                   f" : ℝ :=\n  pfXiD\n{argsD}\n    ξ\n\ntheorem hasDerivAt_{name} (Y : ℝ) {{ξ : ℝ}} (h0 : ξ ≠ 0)"
                   f" (h1 : ξ - 1 ≠ 0) :\n    HasDerivAt ({name} Y) ({name}D Y ξ) ξ :=\n"
                   f"  hasDerivAt_pfXi _ _ _ _ _ _ _ _ h0 h1\n")
    cdoc = [('xiCL', cL, 'The coefficient of `Li₂ (Y ξ)`.'),
            ('xiCq', cq, 'The coefficient of `Li₂ (1 - ξ) + Li(-Y (1 - ξ)/(1 - Y)) - '
                         'Li((1 - 2Y)(1 - ξ)/(1 - Y))`.'),
            ('xiCD', cD, 'The coefficient of `Li((2Y - 1) ξ/Y)`.')]
    for name, v, doc in cdoc:
        out.append(f"/-- {doc} -/\nnoncomputable def {name} (Y : ℝ) : ℝ :=\n  {lean_rat(v)}\n")
    pdoc = [('xiΦ1', '1', 'The rational part of `Y Φ_X(Y ξ, Y (1 - ξ))`.'),
            ('xiΦY', 'Y', 'The coefficient of `log Y` in `Y Φ_X(Y ξ, Y (1 - ξ))`.'),
            ('xiΦx', 'x', 'The coefficient of `log ξ` in `Y Φ_X(Y ξ, Y (1 - ξ))`.'),
            ('xiΦA', 'A', 'The coefficient of `log (1 - Y ξ)` in `Y Φ_X(Y ξ, Y (1 - ξ))`.'),
            ('xiΦB', 'B', 'The coefficient of `log (ξ + Y - 2 Y ξ)` in `Y Φ_X(Y ξ, Y (1 - ξ))`.')]
    for name, k, doc in pdoc:
        out.append(f"/-- {doc} -/\nnoncomputable def {name} (Y ξ : ℝ) : ℝ :=\n  {lean_rat(co[k])}\n")
    blocks['UnitXXiDefs.lean'] = wrapall('\n'.join(out))

    def divides(f, den):
        return sp.rem(sp.Poly(den, Y, x), sp.Poly(f, Y, x)).is_zero
    out = []
    for name, k in key.items():
        for suff, expr, base in [('', coef[k], 'pfXi'), ('D', sp.diff(coef[k], x), 'pfXiD')]:
            use = [s_ for s_ in SLOTS if s_ in p[k] and not (suff == 'D' and s_ == ('x', 0))]
            dens = [sp.fraction(sp.factor(p[k][s_]))[1] for s_ in use]
            dens.append(sp.fraction(sp.factor(sp.cancel(expr)))[1])
            fac = [('hY0 : Y ≠ 0', Y), ('hY1 : Y - 1 ≠ 0', Y - 1), ('hY2 : 2 * Y - 1 ≠ 0', 2 * Y - 1)]
            h = [f'({n})' for n, f in fac if any(divides(f, d_) for d_ in dens)]
            if any(s_[0] == 'x' and s_[1] < 0 for s_ in use) or divides(x, dens[-1]):
                h.append('(hξ0 : ξ ≠ 0)')
            if any(s_[0] == 'o' for s_ in use) or divides(x - 1, dens[-1]):
                h.append('(hξ1 : ξ - 1 ≠ 0)')
            extra = ('  have hY2b : Y * 2 - 1 ≠ 0 := by rwa [mul_comm]\n'
                     if any('hY2' in t_ for t_ in h) else '')
            out.append(f"theorem {name}{suff}_eq {{Y ξ : ℝ}} {' '.join(h)} :\n"
                       f"    {name}{suff} Y ξ = {lean_rat(expr)} := by\n{extra}"
                       f"  unfold {name}{suff} {base}\n  field_simp\n  ring\n")
    blocks['UnitXXiRat.lean'] = wrapall('\n'.join(out))
    edoc = {'xiU0': 'The rational part of `xiF` at `ξ → 0⁺`.',
            'xiW0': 'The coefficient of `log Y` in `xiF` at `ξ → 0⁺`.',
            'xiV0': 'The coefficient of `ξ log ξ` in `xiF` at `ξ → 0⁺`.',
            'xiA0': 'The coefficient of `lr2 (Y ξ)/ξ²` in `xiF` at `ξ → 0⁺`.',
            'xiB0': 'The coefficient of `lr2 ((2Y - 1) ξ/Y)/ξ²` in `xiF` at `ξ → 0⁺`.',
            'xiU1': 'The rational part of `xiF` at `ξ → 1⁻`.',
            'xiW1Y': 'The coefficient of `log Y` in `xiF` at `ξ → 1⁻`.',
            'xiW1': 'The coefficient of `log (1 - Y)` in `xiF` at `ξ → 1⁻`.',
            'xiX1': 'The coefficient of `lr3 (1 - ξ)/(1 - ξ)³` in `xiF` at `ξ → 1⁻`.',
            'xiA1': 'The coefficient of `lr3 (-Y (1 - ξ)/(1 - Y))/(1 - ξ)³` in `xiF` at `ξ → 1⁻`.',
            'xiB1': 'The coefficient of `lr3 ((1 - 2Y)(1 - ξ)/(1 - Y))/(1 - ξ)³` in `xiF` at '
                    '`ξ → 1⁻`.'}
    blocks['UnitXXiEnds.lean'] = wrapall('\n'.join(
        f"/-- {edoc[k]} -/\nnoncomputable def {k} (Y ξ : ℝ) : ℝ :=\n  {lean_rat(v)}\n"
        for k, v in ends.items()))
    if args.emit:
        os.makedirs(args.emit, exist_ok=True)
        for f, txt in blocks.items():
            open(os.path.join(args.emit, f + '.block'), 'w').write(txt)
        print('wrote', ', '.join(blocks), 'blocks to', args.emit)
    if args.check:
        ok = True
        for f, txt in blocks.items():
            hit = txt in open(os.path.join(LEAN, f)).read()
            ok &= hit
            print(f'   generated block {"occurs" if hit else "DOES NOT occur"} in {f}')
        if not ok:
            sys.exit(1)
    print(f'done ({time.time() - t0:.0f} s)')


if __name__ == '__main__':
    main()
