#!/usr/bin/env python3
"""The exact value of the sixth-order VP-chain set (b) (obligation O3-13 of docs/HIGHER-LOOP-PLAN.md).
NOT a proof by itself: derives and checks (exact rational arithmetic, sympy) the antiderivative used
in QED/Chain/VPChainSetB.lean, and checks the value numerically (mpmath).

With L = log(1 - x) and the closed form (QED.Chain.piHatX)
    Pi(x) = A + B L,  A = -5/9 - 4/(3x) + 4/(3x^2),  B = (x^3 - 6x + 4)/(3x^3),
of the one-loop VP function on the photon curve s = x^2/(1 - x), the set (b) integrand is
f = (1 - x) Pi^2. Steps:
 1. the t-integral 2 int_0^1 t(1-t) log(1 + t(1-t)s) dt equals Pi (exact, via the factorization
    1 + t(1-t)s = (1-tx)(1-x+tx)/(1-x)), and numerically (45 digits) at three points;
 2. an antiderivative F = P0 + Q1 (1-x)L + Q2 (1-x)L^2 - (8/45) Li2(x) + (4/3) S(x), with
    S(x) = log x L^2 + 2 L Li2(1-x) - 2 Li3(1-x) (QED.Polylog.logOneSubSqPrim, S' = L^2/x),
    found by solving a linear system for Laurent coefficients; F' = f exactly;
 3. the endpoint forms: at 0+, with L = x T1 + x^4 rho (T1 = -1 - x/2 - x^2/3 - x^3/4,
    rho = logRem(x)/x^4), F = Poly + U1 rho + U2 rho (2 T1 + rho x^3) - (8/45)Li2 + (4/3)S with Poly
    a polynomial (pole cancellation, exact); at 1-, the coefficients are regular;
 4. F(1-) - F(0+) = (8/3) zeta(3) - (4/135) pi^2 - 943/324, and the one-bubble analogue 119/36 - pi^2/3;
 5. numerics: tanh-sinh quadrature of (1 - x) Pi^2 at 40 digits against the closed form;
 6. the enclosure of QED/Chain/VPChainSetBBounds.lean in exact rationals: the telescoping tail bounds
    for zeta(3) after 40 terms, and 0.00255852 < A_(b) < 0.00255853 from the rounded bounds.
With --check, every generated polynomial must occur (up to whitespace) in QED/Chain/VPChainSetB.lean.
Run (~10 s):  nice -n 10 python3 set_b_antiderivative.py [--check] [--emit DIR]
"""
import argparse
import os

import mpmath as mp
import sympy as sp

x, t = sp.symbols('x t', positive=True)
l = sp.Symbol('L')
R = sp.Rational

A = -R(5, 9) - R(4, 3) / x + R(4, 3) / x**2
B = (x**3 - 6 * x + 4) / (3 * x**3)
T1 = -1 - x / 2 - x**2 / 3 - x**3 / 4


def step1():
    w = t**2 / 2 - t**3 / 3
    a = sp.expand(w - w.subs(t, 1 / x))
    b = sp.expand(w - w.subs(t, -(1 - x) / x))
    la, lb, l1 = sp.symbols('la lb l1')
    p = sp.expand(-sp.integrate(sp.expand(sp.cancel(a * (-x) / (1 - t * x)) +
                                          sp.cancel(b * x / (1 - x + t * x))), t) - l1 * w)
    G = p + a * la + b * lb
    dG = sp.diff(G, t) + a * (-x) / (1 - t * x) + b * x / (1 - x + t * x)
    assert sp.simplify(dG - t * (1 - t) * (la + lb - l1)) == 0
    assert sp.simplify(1 + t * (1 - t) * x**2 / (1 - x) - (1 - t * x) * (1 - x + t * x) / (1 - x)) == 0
    val = 2 * (G.subs(t, 1).subs({la: l, lb: 0, l1: l}) - G.subs(t, 0).subs({la: 0, lb: l, l1: l}))
    assert sp.expand(val - (A + B * l)) == 0
    print('step 1: t-antiderivative and closed form: exact OK')


def solve_antiderivative(f, c_names, lo=-6, hi=4):
    """Laurent P0 + P1 L + P2 L^2 + c1 Li2 + c2 S with F' = f (f polynomial in L)."""
    P = [[sp.Symbol(f'p{i}_{k - lo}') for k in range(lo, hi + 1)] for i in range(3)]
    Pf = [sum(P[i][k - lo] * x**k for k in range(lo, hi + 1)) for i in range(3)]
    c1, c2 = sp.symbols('c1 c2')
    D = (sp.diff(Pf[0], x) + sp.diff(Pf[1], x) * l - Pf[1] / (1 - x) + sp.diff(Pf[2], x) * l**2
         - 2 * Pf[2] * l / (1 - x) - c1 * l / x + c2 * l**2 / x)
    E = sp.expand(sp.numer(sp.together(D - f)))
    eqs = []
    for j in range(3):
        eqs += sp.Poly(sp.expand(E.coeff(l, j)), x).coeffs()
    unk = [s for row in P for s in row] + [c1, c2]
    sol = sp.solve(eqs, unk, dict=True)[0]
    sol = {u: sol.get(u, 0) for u in unk}  # free constant set to 0
    Pv = [sp.expand(p.subs(sol)) for p in Pf]
    return Pv, sol[c1], sol[c2]


def lean_poly(e):
    """a polynomial in x as Lean text (rational coefficients)."""
    terms = []
    for (k,), c in sorted(sp.Poly(sp.expand(e), x).terms(), key=lambda z: z[0]):
        c = sp.Rational(c)
        mon = '' if k == 0 else ('x' if k == 1 else f'x ^ {k}')
        num, den = abs(c.p), c.q
        coef = f'{num}' if den == 1 else f'{num} / {den}'
        if mon == '':
            body = coef
        elif num == 1 and den == 1:
            body = mon
        elif num == 1:
            body = f'{mon} / {den}'
        elif den == 1:
            body = f'{num} * {mon}'
        else:
            body = f'{num} * {mon} / {den}'
        terms.append(('-' if c < 0 else '+', body))
    s = ('-' if terms[0][0] == '-' else '') + terms[0][1]
    for sg, b in terms[1:]:
        s += f' {sg} {b}'
    return s


def step2_4(emit):
    out = {}
    # set (b)
    f = sp.expand((1 - x) * (A + B * l)**2)
    (P0, P1, P2), c1, c2 = solve_antiderivative(f, None)
    assert (c1, c2) == (R(-8, 45), R(4, 3)), (c1, c2)
    assert P1.subs(x, 1) == 0 and P2.subs(x, 1) == 0
    Q1 = sp.cancel(P1 / (1 - x))
    Q2 = sp.cancel(P2 / (1 - x))
    N0, N1, N2 = sp.expand(P0 * x**3), sp.expand(Q1 * x**4), sp.expand(Q2 * x**5)
    for N in (N0, N1, N2):
        assert not sp.denom(sp.together(N)).has(x)
    # F' = f with F written through (1-x)L, (1-x)L^2
    F = N0 / x**3 + N1 / x**4 * (1 - x) * l + N2 / x**5 * (1 - x) * l**2
    dF = sp.diff(F, x) + sp.diff(F, l) * (-1 / (1 - x)) - R(8, 45) * (-l / x) + R(4, 3) * l**2 / x
    assert sp.simplify(dF - f) == 0
    # endpoint 0
    U1 = sp.expand((1 - x) * N1)
    U2 = sp.expand((1 - x) * N2)
    Poly = sp.cancel(N0 / x**3 + (1 - x) * N1 / x**4 * x * T1 + (1 - x) * N2 / x**5 * x**2 * T1**2)
    assert not sp.denom(sp.together(Poly)).has(x)
    rho = sp.Symbol('rho')
    Lsub = x * T1 + x**4 * rho
    lhs = N0 / x**3 + N1 / x**4 * (1 - x) * Lsub + N2 / x**5 * (1 - x) * Lsub**2
    rhs = Poly + U1 * rho + U2 * rho * (2 * T1 + rho * x**3)
    assert sp.simplify(lhs - rhs) == 0
    F0 = Poly.subs(x, 0)            # + (4/3)(-2 zeta3)
    F1 = (N0 / x**3).subs(x, 1)     # - (8/45) pi^2/6
    print('step 2-4 (set b): F\' = f exact; Poly(0) =', F0, '; P0(1) =', F1,
          '; rational part =', F1 - F0)
    assert F1 - F0 == R(-943, 324)
    out.update(dN0=lean_poly(sp.diff(N0, x)), dN1=lean_poly(sp.diff(N1, x)),
               dN2=lean_poly(sp.diff(N2, x)))
    out.update(N0=lean_poly(N0), N1=lean_poly(N1), N2=lean_poly(N2), U1=lean_poly(U1),
               U2=lean_poly(U2), Poly=lean_poly(Poly))
    # one bubble: F = (13x^2+22x)/36 - 2/(3x) + (1-x)L (x^3-x^2+16x-4)/(6x^2) - 2 Li2
    g = sp.expand((1 - x) * (A + B * l))
    Fo = (13 * x**2 + 22 * x) / 36 - 2 / (3 * x) + (1 - x) * l * (x**3 - x**2 + 16 * x - 4) / (6 * x**2)
    dFo = sp.diff(Fo, x) + sp.diff(Fo, l) * (-1 / (1 - x)) - 2 * (-l / x)
    assert sp.simplify(dFo - g) == 0
    Polyo = sp.cancel(Fo.subs(l, x * T1))
    assert not sp.denom(sp.together(Polyo)).has(x)
    Uo = sp.expand((1 - x) * (x**3 - x**2 + 16 * x - 4) * x**2 / 6)
    assert sp.simplify(Fo.subs(l, Lsub) - (Polyo + Uo * rho)) == 0
    print('one bubble: F\' exact; Poly(0) =', Polyo.subs(x, 0), '; F(1) rational =',
          Fo.subs(l, 0).subs(x, 1), '-> 119/36 - pi^2/3')
    assert Fo.subs(l, 0).subs(x, 1) - Polyo.subs(x, 0) == R(119, 36)
    out.update(PolyOne=lean_poly(Polyo), UOne=lean_poly(Uo))
    if emit:
        os.makedirs(emit, exist_ok=True)
        with open(os.path.join(emit, 'set_b_blocks.txt'), 'w') as fh:
            for k, v in out.items():
                fh.write(f'{k} := {v}\n')
        print('wrote', os.path.join(emit, 'set_b_blocks.txt'))
    return out


def step5():
    mp.mp.dps = 45

    def pix(xv):
        L = mp.log(1 - xv)
        return -mp.mpf(5) / 9 - mp.mpf(4) / (3 * xv) + mp.mpf(4) / (3 * xv**2) + (xv**3 - 6 * xv + 4) / (3 * xv**3) * L

    for xv in ('0.3', '0.7', '0.95'):
        xv = mp.mpf(xv)
        s = xv**2 / (1 - xv)
        d = 2 * mp.quad(lambda u: u * (1 - u) * mp.log(1 + u * (1 - u) * s), [0, 1])
        assert abs(d - pix(xv)) < mp.mpf(10)**-40
    print('step 1 numerics: closed form vs defining t-integral < 1e-40 at x = 0.3, 0.7, 0.95')

    def pix_safe(xv):
        with mp.workdps(130):  # cancellation of the x^-3 poles near 0
            return pix(mp.mpf(xv))

    val = mp.quad(lambda u: (1 - u) * pix_safe(u)**2, [0, mp.mpf('0.5'), 1])
    tgt = mp.mpf(8) / 3 * mp.zeta(3) - mp.mpf(4) / 135 * mp.pi**2 - mp.mpf(943) / 324
    one = mp.quad(lambda u: (1 - u) * pix_safe(u), [0, mp.mpf('0.5'), 1])
    print('set (b): quadrature', mp.nstr(val, 40))
    print('         closed form', mp.nstr(tgt, 40), ' diff', mp.nstr(val - tgt, 3))
    print('one bubble: diff to 119/36 - pi^2/3', mp.nstr(one - (mp.mpf(119) / 36 - mp.pi**2 / 3), 3))
    assert abs(val - tgt) < mp.mpf(10)**-38 and abs(one - (mp.mpf(119) / 36 - mp.pi**2 / 3)) < mp.mpf(10)**-38


def step6():
    from fractions import Fraction as Fr
    zlo = lambda u: Fr(1, 2) / u**2 - Fr(1, 8) / u**4
    zhi = lambda u: zlo(u) + Fr(7, 96) / u**6
    k = sp.Symbol('k', nonnegative=True)
    for f, sgn, num in ((zlo, -1, [112, 448, 656, 416, 97]),
                        (zhi, 1, [7936, 47616, 118608, 156992, 116520, 46032, 7573])):
        fs = lambda u: sp.Rational(1, 2) / u**2 - sp.Rational(1, 8) / u**4 + \
            (sp.Rational(7, 96) / u**6 if f is zhi else 0)
        e = sp.factor(sgn * (fs(k + sp.Rational(1, 2)) - fs(k + sp.Rational(3, 2)) - 1 / (k + 1)**3))
        n, d = sp.fraction(e)
        assert sp.Poly(n, k).all_coeffs() == num, sp.Poly(n, k).all_coeffs()
    S = sum(Fr(1, (n + 1)**3) for n in range(40))
    lo = S + zlo(Fr(81, 2)) - zlo(Fr(40 + 10**6) + Fr(1, 2))
    hi = S + zhi(Fr(81, 2))
    assert Fr(1202056903, 10**9) < lo and hi < Fr(12020569033, 10**10)
    a = lambda z, p: Fr(8, 3) * z - Fr(4, 135) * p**2 - Fr(943, 324)
    plo, phi = Fr(314159265358979323846, 10**20), Fr(314159265358979323847, 10**20)
    assert Fr(255852, 10**8) < a(Fr(1202056903, 10**9), phi)
    assert a(Fr(12020569033, 10**10), plo) < Fr(255853, 10**8)
    print('step 6: telescoping numerators positive; 1.202056903 < zeta3 < 1.2020569033 '
          '(40 terms); 0.00255852 < A_(b) < 0.00255853: exact OK')


def check_lean(out):
    path = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..',
                                         'QED', 'Chain', 'VPChainSetB.lean'))
    txt = ' '.join(open(path).read().split())
    for key in ('N0', 'N1', 'N2', 'dN0', 'dN1', 'dN2', 'U1', 'U2', 'Poly', 'PolyOne', 'UOne'):
        assert ' '.join(out[key].split()) in txt, key
    print('check: generated polynomials occur in', path)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--emit', metavar='DIR', help='write the generated Lean blocks to DIR')
    ap.add_argument('--check', action='store_true', help='check the blocks against the Lean file')
    args = ap.parse_args()
    step1()
    out = step2_4(args.emit)
    if args.check:
        check_lean(out)
    step5()
    step6()
    print('all checks passed')
