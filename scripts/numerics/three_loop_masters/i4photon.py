#!/usr/bin/env python3
"""Integrate the AE photon analytically and quadrature the first three I4 coefficients.

By projective homogeneity, set the largest of (a,b,c,l,n) to 1, order the
other four as successive products of t in (0,1), and integrate m on (0,infty).
With U=U0+m U1, F=F0+m F1, let x=U0/U and B=F1 U0/U1.
The integrated kernel is U0**(-1+4 eps)/U1 times
B**(-3 eps) * hyp2f1(3 eps,1-eps,2-eps,1-F0/B)/(1-eps).
The code uses its Taylor moments, integrating 1, L and L**2/2 over x,
where L=4 log(U0)-3 log(B)-log(x)-3 log(1+(F0/B-1)*x).
"""
import argparse
from itertools import permutations

import mpmath as mp
import numpy as np

from i4sector import symanzik, targets


def coefficients(a, b, c, l, n):
    """Polynomial coefficients, computed without subtracting nearly equal values."""
    u0 = a*b*(c+l) + a*c*(l+n) + a*n*l + b*c*n + b*l*n + c*l*n
    u1 = a*b + a*c + a*n + b*c + b*(l+n) + c*l + l*n
    f0 = (
        a*b*c*(a+b+c+2*(l+n)) + a*b*(a+b)*l + a*c*(a+c)*(l+n)
        + a*n*(a*l+2*(b*l+c*l)) + b*c*(b+c)*n + b*b*l*n + c*l*(2*b+c)*n
    )
    f1 = (
        2*a*b*c + a*b*(a+b) + a*c*(a+c) + a*n*(a+2*b)
        + b*c*(b+c) + b*b*(l+n) + c*l*(2*b+c)
    )
    return u0, u1, f0, f1


def dilog_unit(x):
    """Li2 on [0,1], with the series evaluated only on [0,1/2]."""
    complement = 1 - x
    y = np.minimum(x, complement)
    result = y * 0
    for k in range(56, 0, -1):
        result = y * (result + np.longdouble(1) / k**2)
    with np.errstate(divide="ignore", invalid="ignore"):
        reflected = np.longdouble(str(mp.zeta(2))) - np.log(x)*np.log1p(-x) - result
    return np.where(x <= 0.5, result, np.where(x == 1, np.longdouble(str(mp.zeta(2))), reflected))


def moments(log_r):
    """Moments of -log(x)+3 log(r/(1+(r-1)x)), with x uniform."""
    # This centers the logarithm at F0, so the moments stay bounded for r large.
    d = -np.expm1(-log_r)
    q = np.exp(-log_r)
    safe = np.where(d == 0, 1, d)
    glog = q*log_r / safe
    first = 1 - glog
    second = 2 - glog*(2+log_r)
    cross = 2 - q*(log_r + dilog_unit(d) + log_r**2/2)/safe
    return np.where(d == 0, 1, 1+3*first), np.where(d == 0, 2, 2+6*cross+9*second)


def hypergeom_coefficients(a, c):
    """Power series for 2F1(a,1;c;x), used only at |x| <= 1/2."""
    coeffs = [mp.mpf(1)]
    for k in range(60):
        coeffs.append(coeffs[-1] * (a+k)/(c+k))
    return coeffs


def photon_series(eps, dtype):
    a, c = 3*eps, 2-eps
    s = c-a-1
    factor_a = mp.gamma(c)*mp.gamma(s)/(mp.gamma(c-a)*mp.gamma(c-1))
    factor_b = mp.gamma(c)*mp.gamma(-s)/mp.gamma(a)

    def cast(value):
        return dtype(str(value))

    direct = [cast(x) for x in hypergeom_coefficients(a, c)]
    continued = [cast(x) for x in hypergeom_coefficients(a, 1-s)]

    def evaluate(log_r):
        # Pfaff's transformation makes d=1-1/r the hypergeometric argument.
        # Continue about d=1 on the half where q=1-d is smaller.
        q = np.exp(-log_r)
        d = -np.expm1(-log_r)
        x = np.minimum(q, d)
        first = np.polynomial.polynomial.polyval(x, direct)
        other = np.polynomial.polynomial.polyval(x, continued)
        second = cast(factor_a)*other + cast(factor_b)*np.exp(
            -cast(s)*log_r - cast(1-eps)*np.log1p(-x)
        )
        return np.where(d <= 0.5, first, second)/cast(1-eps)

    return evaluate


def check_formula():
    a, b, c, l, n = (mp.mpf(k) for k in [2, 3, 5, 7, 11])
    u0, u1, f0, f1 = coefficients(a, b, c, l, n)
    for m in [0, 13]:
        assert (u0+m*u1, f0+m*f1) == symanzik(a, b, c, l, m, n)
    eps = mp.mpf("0.02")
    evaluate = photon_series(eps, np.longdouble)
    for r in [mp.mpf(1), mp.mpf("1.01"), mp.mpf(2), mp.mpf(100)]:
        log_r = np.longdouble(str(mp.log(r)))
        first, second = moments(np.array(log_r))

        def g(x):
            return -mp.log(x)+3*mp.log(r/(1+(r-1)*x))

        for k, actual in enumerate([first, second], 1):
            assert abs(mp.mpf(str(actual))-mp.quad(lambda x: g(x)**k, [0, 1])) < mp.mpf("1e-15")
        expected = r**(3*eps)*mp.hyp2f1(3*eps, 1-eps, 2-eps, 1-r)/(1-eps)
        assert abs(mp.mpf(str(evaluate(log_r)))-expected) < mp.mpf("1e-15")


def quadrature(degree, power, dtype, epsilons):
    xs, ws = mp.gauss_quadrature(degree, "legendre")
    s = np.array([str((1+x)/2) for x in xs], dtype=dtype)
    w = np.array([str(x/2) for x in ws], dtype=dtype) * power * s**(power-1)
    t = s**power
    orders = [
        p for p in permutations(range(5))
        if p < tuple(p[i] for i in (2, 1, 0, 4, 3))
    ]
    weight = w[:, None, None] * w[None, :, None] * w[None, None, :]
    t2, t3, t4 = np.ix_(t, t, t)
    evaluators = [photon_series(e, dtype) for e in epsilons]
    eps = [dtype(str(e)) for e in epsilons]
    totals = []
    for t1, w1 in zip(t, w):
        params = (dtype(1), t1, t1*t2, t1*t2*t3, t1*t2*t3*t4)
        jac = 2*w1*weight*t1**3*t2**2*t3
        for order in orders:
            u0, u1, f0, f1 = coefficients(*(params[i] for i in order))
            # Increasing the AE edge resistance raises R and lowers F/U=S-R.
            # Thus F0/U0 >= F1/U1, with clipping only for floating-point roundoff.
            log_r = np.maximum(0, np.log((f0/u0)/(f1/u1)))
            log_f = 4*np.log(u0)-3*np.log(f0)
            first, second = moments(log_r)
            density = jac / (u0*u1)
            totals.append((
                np.sum(density, dtype=np.longdouble),
                np.sum(density*(log_f+first), dtype=np.longdouble),
                np.sum(density*(log_f**2+2*log_f*first+second)/2, dtype=np.longdouble),
                *(np.sum(density*np.exp(e*log_f)*evaluate(log_r), dtype=np.longdouble)
                  for e, evaluate in zip(eps, evaluators)),
            ))
    return [mp.mpf(str(x)) for x in np.sum(totals, axis=0, dtype=np.longdouble)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, default=40)
    parser.add_argument("--power", type=int, default=6)
    parser.add_argument("--float64", action="store_true")
    parser.add_argument("--epsilon", nargs="*", default=[])
    args = parser.parse_args()
    mp.mp.dps = 45
    check_formula()
    eps = [mp.mpf(e) for e in args.epsilon]
    if any(not 0 < abs(e) < mp.mpf("0.125") for e in eps):
        parser.error("--epsilon requires 0 < |epsilon| < 1/8")
    pole, constant, linear = targets()
    expected = [3*pole, 3*constant, 3*(linear - mp.pi**2*pole/2)]
    dtype = np.float64 if args.float64 else np.longdouble
    values = quadrature(args.degree, args.power, dtype, eps)
    for j, (actual, target) in enumerate(zip(values, expected)):
        print(f"P{j}: {mp.nstr(actual, 21)}   error {mp.nstr(actual-target, 10)}")

    for e, value in zip(eps, values[3:]):
        master = mp.gamma(1+3*e)/mp.gamma(1+e)**3 * value/(3*e)
        residual = (master - (pole/e + constant + linear*e))/e**2
        print(f"eps={e}  I4/C={mp.nstr(master, 21)}  scaled residual={mp.nstr(residual, 12)}")


if __name__ == "__main__":
    main()
