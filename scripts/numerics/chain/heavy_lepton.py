#!/usr/bin/env python3
"""The heavy-lepton VP insertion A(y) (obligation O3-M3 of docs/HIGHER-LOOP-PLAN.md).
NOT a proof by itself: derives and checks (exact arithmetic with sympy, numerics with mpmath) the
objects used in QED/Chain/HeavyLepton*.lean.

A(y) = int_0^1 (1-x) PiHat(y^2 x^2/(1-x)) dx, loop mass M = 1/y, 0 < y < 1, with
PiHat(s) = 2 int_0^1 t(1-t) log(1 + t(1-t) s) dt (QED.Chain.piHat). Steps:
 1. PiHat(1/(p(1+p))) = piHatP(p) = (1/3)[-5/3 + 4p(1+p) + (1-2p(1+p))(2p+1)(log(1+p) - log p)]
    (numerically, 45 digits, at several p);
 2. the rationalizing map x = (1-w^2)/(1+yw), with -dx/dw = jac = (yw^2+2w+y)/(1+yw)^2,
    p = w(1+yw)/(y(1-w^2)), p(1+p) = (1-x)/(y^2 x^2) (exact), and the w-integrand
    (1-x) piHatP(p) jac = R0 + R1 ell, ell = log(y+w) - log w - log(1+yw) (exact);
 3. the antiderivative hlPrim = Q0 + c(log(1+yw) - log(y+w)) + Q1 ell + a(K1 + Km1) + b Ky with
    a = (y^2-5)/(2y^3), b = 2/y^4, c = (y^2-9)/(3y^2): the identities Q1' + a/(1-w) + a/(1+w)
    + b y/(1+yw) = R1 and Q0' + c(y/(1+yw) - 1/(y+w)) + Q1 ell' = R0 (exact), and
    hlPrim' = R0 + R1 ell with the dilogarithm blocks (numerically, 50 digits);
 4. the endpoint forms: B = Q0 + Q1(u + u^2/2 + u^3/3 + u^4/4), U = Q1 u^4 with
    u = y(1-w^2)/(y+w) are regular at w = 1, B(1) = 11(4y^2+9)/(36y^4), U(1) = 0 (exact); the
    difference of the limits equals a2Heavy after the dilogarithm identities (exact in the atoms);
 5. a2Heavy against Passera (10) at x = 1/y (real parts, 60 digits) and against quadrature of the
    defining integral;
 6. the enclosures of QED/Chain/HeavyLeptonBounds.lean in exact rationals (series with 11 terms,
    log y from 20 terms of the log series and the nine-digit bounds on log 2).
With --check, every generated coefficient must occur (up to whitespace) in
QED/Chain/HeavyLeptonPrim.lean. With --emit DIR, the coefficient tables are written to DIR.
Run (~20 s):  nice -n 10 python3 heavy_lepton.py [--check] [--emit DIR]
Requires mpmath (run with 1.3.0) and sympy (run with 1.14.0).
"""
import argparse
import math
import os
import re
from fractions import Fraction as Fr

import mpmath as mp
import sympy as sp

y, w, p = sp.symbols('y w p', positive=True)
R = sp.Rational

X = (1 - w**2) / (1 + y * w)
JAC = (y * w**2 + 2 * w + y) / (1 + y * w)**2
P = w * (1 + y * w) / (y * (1 - w**2))
ELLP = 1 / (y + w) - 1 / w - y / (1 + y * w)
A_ = (y**2 - 5) / (2 * y**3)
B_ = 2 / y**4
C_ = (y**2 - 9) / (3 * y**2)
U_ = y * (1 - w**2) / (y + w)


def say(*a):
    print(*a, flush=True)


def step1():
    mp.mp.dps = 45
    worst = 0
    for pv in ['0.01', '0.3', '1', '4.5', '70']:
        pv = mp.mpf(pv)
        S = 1 / (pv * (1 + pv))
        quad = 2 * mp.quad(lambda t: t * (1 - t) * mp.log(1 + t * (1 - t) * S), [0, 1])
        form = (-mp.mpf(5) / 3 + 4 * pv * (1 + pv)
                + (1 - 2 * pv * (1 + pv)) * (2 * pv + 1) * (mp.log(1 + pv) - mp.log(pv))) / 3
        worst = max(worst, abs(quad - form) / abs(form))
    say(f"1. PiHat(1/(p(1+p))) = piHatP(p): max relative deviation {mp.nstr(worst, 3)}")
    assert worst < mp.mpf(10)**-30


def step2():
    assert sp.simplify(-sp.diff(X, w) - JAC) == 0
    assert sp.simplify(P * (1 + P) - (1 - X) / (y**2 * X**2)) == 0
    q = P * (1 + P)
    R0 = sp.factor((1 - X) * R(1, 3) * (-R(5, 3) + 4 * q) * JAC)
    R1 = sp.factor((1 - X) * R(1, 3) * (1 - 2 * q) * (2 * P + 1) * JAC)
    say("2. substitution identities hold exactly; R0, R1 computed")
    return R0, R1


def step3(R0, R1):
    simple = A_ / (1 - w) + A_ / (1 + w) + B_ * y / (1 + y * w)
    Q1 = sp.integrate(sp.apart(sp.factor(R1 - simple), w), w)
    Q1 = sp.factor(sp.simplify(Q1 - Q1.subs(w, 0)))
    rest0 = sp.apart(sp.factor(R0 - Q1 * ELLP), w) - C_ * (y / (1 + y * w) - 1 / (y + w))
    Q0 = sp.factor(sp.simplify(sp.integrate(rest0, w)))
    assert sp.simplify(sp.diff(Q1, w) + simple - R1) == 0
    assert sp.simplify(sp.diff(Q0, w) + C_ * (y / (1 + y * w) - 1 / (y + w)) + Q1 * ELLP - R0) == 0
    # the full derivative, numerically, with the dilogarithm blocks
    mp.mp.dps = 50
    Li2 = lambda z: mp.polylog(2, z)

    q0f = sp.lambdify((y, w), Q0, 'mpmath')
    q1f = sp.lambdify((y, w), Q1, 'mpmath')
    r0f = sp.lambdify((y, w), R0, 'mpmath')
    r1f = sp.lambdify((y, w), R1, 'mpmath')

    def prim(yv, wv):
        ell = mp.log(yv + wv) - mp.log(wv) - mp.log(1 + yv * wv)
        k1 = Li2((1 - wv) / (1 + yv)) - Li2(yv * (1 - wv) / (1 + yv)) - Li2(1 - wv)
        km1 = (Li2((1 - yv) / (1 + wv)) - mp.log(wv) * mp.log(1 + wv) - 2 * Li2(-wv)
               - Li2((1 - yv) * wv / (1 + wv)) + Li2(-yv * wv))
        ky = (Li2((1 - yv**2) / (1 + yv * wv)) - mp.log(yv) * mp.log(1 + yv * wv)
              - mp.log(wv) * mp.log(1 + yv * wv) - Li2(-yv * wv))
        return (q0f(yv, wv) + (yv**2 - 9) / (3 * yv**2) * (mp.log(1 + yv * wv) - mp.log(yv + wv))
                + q1f(yv, wv) * ell + (yv**2 - 5) / (2 * yv**3) * (k1 + km1) + 2 / yv**4 * ky)

    worst = 0
    for yv, wv in [('0.37', '0.2'), ('0.37', '0.7'), ('0.05', '0.5'), ('0.9', '0.95')]:
        yv, wv = mp.mpf(yv), mp.mpf(wv)
        d = mp.diff(lambda t: prim(yv, t), wv)
        ell = mp.log(yv + wv) - mp.log(wv) - mp.log(1 + yv * wv)
        j = r0f(yv, wv) + r1f(yv, wv) * ell
        worst = max(worst, abs(d - j) / abs(j))
    say(f"3. Q0, Q1 derived; Q1', Q0' identities exact; hlPrim' = R0 + R1 ell to "
        f"{mp.nstr(worst, 3)} (relative)")
    assert worst < mp.mpf(10)**-35
    return Q0, Q1


def step4(Q0, Q1):
    B = sp.factor(Q0 + Q1 * (U_ + U_**2 / 2 + U_**3 / 3 + U_**4 / 4))
    U = sp.factor(Q1 * U_**4)
    nB, dB = sp.fraction(B)
    nU, dU = sp.fraction(U)
    assert dB.subs(w, 1) != 0 and dU.subs(w, 1) != 0
    assert sp.simplify(B.subs(w, 1) - 11 * (4 * y**2 + 9) / (36 * y**4)) == 0
    assert sp.simplify(U.subs(w, 1)) == 0
    assert sp.simplify(Q0.subs(w, 0) - (5 * y**2 - 11) * (5 * y**2 - 9) / (36 * y**4)) == 0
    # the dilogarithm identities, in the atoms
    L, L1, L2, D1, D2, D3, E1, E2, E3, E4, PI2 = sp.symbols('L L1 L2 D1 D2 D3 E1 E2 E3 E4 PI2')
    one = 11 * (4 * y**2 + 9) / (36 * y**4) + A_ * (PI2 / 6 + D2) + B_ * (E1 - L * L2 - D2)
    zero = ((5 * y**2 - 11) * (5 * y**2 - 9) / (36 * y**4) - C_ * L
            + A_ * (E4 - E3 - PI2 / 6 + E1) + B_ * E2)
    target = (-R(25, 36) + L / 3 + (4 - 3 * L) / y**2 + A_ * (L * (L1 - L2) + D1 - D2)
              + (2 * L * (L1 + L2) + D3) / y**4)
    subs = {E1: PI2 / 6 - L * L1 - D1,                       # reflection at y
            E2: PI2 / 6 - 2 * L * (L1 + L2) - D3,            # reflection at y^2
            E3: -D2 - L2**2 / 2,                             # Landen at 1/(1+y)
            D3: 2 * (D1 + D2)}                               # Li2(y) + Li2(-y) = Li2(y^2)/2
    subs4 = {E4: PI2 / 6 + L2 * (L - L2) - E3}               # reflection at 1/(1+y)
    diff = (one - zero - target).subs(subs4).subs(subs).subs(D3, 2 * (D1 + D2))
    assert sp.simplify(sp.expand(diff)) == 0
    say("4. B, U regular at w = 1, B(1) = 11(4y^2+9)/(36y^4), U(1) = 0; "
        "hlPrimOne - hlPrimZero = a2Heavy (exact, after the dilogarithm identities)")
    return B, U


def a2heavy(yv):
    yv = mp.mpf(yv)
    L = mp.log(yv)
    Li2 = lambda z: mp.polylog(2, z)
    return (-mp.mpf(25) / 36 + L / 3 + (4 - 3 * L) / yv**2
            + (yv**2 - 5) / (2 * yv**3) * (L * mp.log((1 - yv) / (1 + yv)) + Li2(yv) - Li2(-yv))
            + (2 * L * mp.log(1 - yv**2) + Li2(yv**2)) / yv**4)


def passera10(xv):
    xv = mp.mpf(xv)
    L = mp.log(xv)
    t1 = -mp.mpf(25) / 36 - L / 3 + xv**2 * (4 + 3 * L)
    br = (mp.pi**2 / 2 - L * mp.log(abs((1 - xv) / (1 + xv))) - mp.re(mp.polylog(2, xv))
          + mp.polylog(2, -xv))
    t3 = xv**4 * (mp.pi**2 / 3 - 2 * L * mp.log(abs(1 / xv - xv)) - mp.re(mp.polylog(2, xv**2)))
    return t1 + xv / 2 * (1 - 5 * xv**2) * br + t3


def step5():
    mp.mp.dps = 60
    worst = 0
    for yv in ['0.9', '0.37', '0.05', '0.00483633170', '0.000287585']:
        worst = max(worst, abs(a2heavy(yv) - passera10(1 / mp.mpf(yv))) / a2heavy(yv))
    say(f"5. a2Heavy(y) = Passera (10) at x = 1/y: max relative deviation {mp.nstr(worst, 3)}")
    assert worst < mp.mpf(10)**-25
    mp.mp.dps = 30
    for yv in ['0.37', '0.05']:
        yy = mp.mpf(yv)

        def pihat(S):
            return 2 * mp.quad(lambda t: t * (1 - t) * mp.log(1 + t * (1 - t) * S), [0, 1])
        q = mp.quad(lambda x: (1 - x) * pihat(yy**2 * x**2 / (1 - x)), [0, mp.mpf(1) / 2, 1])
        say(f"   quadrature of A({yv}) = {mp.nstr(q, 20)}, a2Heavy = {mp.nstr(a2heavy(yv), 20)}")
        assert abs(q - a2heavy(yv)) < mp.mpf(10)**-18


def lS(n, t):
    return sum(t**(i + 1) / Fr(i + 1) for i in range(n))


def lT(n, t):
    return sum(t**(i + 1) / Fr((i + 1)**2) for i in range(n))


def serP(n, yv):
    return Fr(-25, 36) + 4 / yv**2 + (yv**2 - 5) / (2 * yv**3) * (lT(n, yv) - lT(n, -yv)) \
        + lT(n, yv**2) / yv**4


def serQ(n, yv):
    return Fr(1, 3) - 3 / yv**2 + (yv**2 - 5) / (2 * yv**3) * (lS(n, -yv) - lS(n, yv)) \
        - 2 * lS(n, yv**2) / yv**4


def serE(n, yv, lam):
    return (5 - yv**2) / (2 * yv**3) * (2 * lam + 2) * (yv**(n + 1) / (1 - yv)) \
        + (2 * lam + 1) * ((yv**2)**(n + 1) / (1 - yv**2)) / yv**4


def logbounds(yv, k, n):
    z = 2**k * yv
    u = 1 - z
    s, r = lS(n, u), u**(n + 1) / z
    return -s - r - k * Fr(6931471808, 10**10), -s + r - k * Fr(6931471803, 10**10)


def step6():
    cases = [('muon', Fr(483633159, 10**11), Fr(483633181, 10**11), 7, 6,
              Fr(-53315987857, 10**10), Fr(-53315987316, 10**10),
              Fr(5197386525, 10**16), Fr(5197386998, 10**16)),
             ('tau', Fr(287566, 10**9), Fr(287604, 10**9), 11, 9,
              Fr(-40770290871, 5000000000), Fr(-81539260073, 10**10),
              Fr(18376481, 10**16), Fr(18381339, 10**16))]
    n = 11
    for name, ylo, yhi, k, lam, Llo, Lhi, lo, hi in cases:
        assert Llo <= logbounds(ylo, k, 20)[0] and logbounds(yhi, k, 20)[1] <= Lhi
        assert -lam <= logbounds(yhi, k, 20)[0]
        assert serQ(n, ylo) > 0 and serQ(n, yhi) > 0
        low = serP(n, ylo) + serQ(n, ylo) * Llo - serE(n, ylo, lam)
        up = serP(n, yhi) + serQ(n, yhi) * Lhi + serE(n, yhi, lam)
        assert lo <= low and up <= hi
        mp.mp.dps = 40
        say(f"6. {name}: y in [{float(ylo):.11g}, {float(yhi):.11g}]: A in [{float(lo):.11g}, "
            f"{float(hi):.11g}] (certified [{float(low):.13g}, {float(up):.13g}]; a2Heavy at the "
            f"ends {mp.nstr(a2heavy(mp.mpf(ylo.numerator) / ylo.denominator), 13)}, "
            f"{mp.nstr(a2heavy(mp.mpf(yhi.numerator) / yhi.denominator), 13)})")


def lean_coeffs(e, den):
    """Coefficients (in y) of the numerator of e * den as a polynomial in w."""
    numer = sp.expand(sp.cancel(e * den))
    poly = sp.Poly(numer, w)
    return [sp.factor(poly.coeff_monomial(w**i)) for i in range(poly.degree() + 1)]


def to_lean(c):
    s = str(c).replace('**', '^')
    s = re.sub(r'\s*\*\s*', ' * ', s)
    return re.sub(r'\s*\^\s*', ' ^ ', s)


def tables(R0, R1, Q0, Q1, B, U):
    Q0d = sp.diff(Q0, w)
    Q1d = sp.diff(Q1, w)
    dens = {'hlQ0': 36 * y**4 * (1 - w**2) * (1 + y * w)**2,
            'hlQ1': 6 * y**3 * (1 - w**2)**2 * (1 + y * w)**2,
            'hlQ0d': 18 * y**2 * (1 - w**2)**2 * (1 + y * w)**3,
            'hlQ1d': 3 * y**3 * (1 - w**2)**3 * (1 + y * w)**3,
            'hlR0': 9 * y**2 * (1 - w**2)**2 * (1 + y * w)**3,
            'hlR1': 3 * y**3 * (1 - w**2)**3 * (1 + y * w)**3,
            'hlB': 72 * y**4 * (1 + y * w)**2 * (y + w)**4,
            'hlU': 6 * (1 + y * w)**2 * (y + w)**4}
    exprs = {'hlQ0': Q0, 'hlQ1': Q1, 'hlQ0d': Q0d, 'hlQ1d': Q1d, 'hlR0': R0, 'hlR1': R1,
             'hlB': B, 'hlU': U}
    return {k: [to_lean(c) for c in lean_coeffs(exprs[k], dens[k])] for k in exprs}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--emit', metavar='DIR')
    args = ap.parse_args()
    step1()
    R0, R1 = step2()
    Q0, Q1 = step3(R0, R1)
    B, U = step4(Q0, Q1)
    step5()
    step6()
    tab = tables(R0, R1, Q0, Q1, B, U)
    if args.emit:
        os.makedirs(args.emit, exist_ok=True)
        with open(os.path.join(args.emit, 'heavy_lepton_coefficients.txt'), 'w') as fh:
            for k, cs in tab.items():
                fh.write(k + '\n' + '\n'.join(f'  w^{i}: {c}' for i, c in enumerate(cs)) + '\n')
        say(f"coefficient tables written to {args.emit}")
    if args.check:
        here = os.path.dirname(os.path.abspath(__file__))
        path = os.path.join(here, '..', '..', '..', 'QED', 'Chain', 'HeavyLeptonPrim.lean')
        txt = ' '.join(open(path).read().split())
        missing = [(k, c) for k, cs in tab.items() for c in cs if c != '0' and c not in txt]
        say(f"--check: {sum(len(cs) for cs in tab.values())} coefficients, "
            f"{len(missing)} missing from HeavyLeptonPrim.lean")
        assert not missing, missing


if __name__ == '__main__':
    main()
