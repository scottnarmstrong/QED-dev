#!/usr/bin/env python3
"""Ordered-sector quadrature of the LR96 I4 projective factor.

mpmath supplies Gauss nodes and the Laurent target. NumPy evaluates the tensor
rule in longdouble. Vary --degree and --power to check quadrature convergence.
The final column at nonzero epsilon is the residual divided by epsilon squared.
"""
import argparse
from itertools import permutations

import mpmath as mp
import numpy as np


def targets():
    """The pole, constant and linear coefficients in SetEMastersLaurent.lean."""
    pi2 = mp.pi**2
    z3, z5 = mp.zeta(3), mp.zeta(5)
    log2 = mp.log(2)
    c1 = 2*pi2*log2 + 25*pi2*z3/12 - 49*pi2**2/180 - 49*z5/4 + z3 - pi2/3
    c2 = 2*pi2*log2 + 53*pi2*z3/12 - 2*pi2**2/15 - 173*z5/4 + 18*z3 - 3*pi2
    constant = -7*pi2**2/90 + 2*z3 + pi2/3
    linear = (
        -4*pi2*log2 - 85*pi2*z3/6 - 7*pi2**2/15 + 4*c2 - 2*c1
        + 385*z5/2 - 82*z3 + 16*pi2
    )
    return 2*z3, constant, linear


def symanzik(a, b, c, l, m, n):
    """Positive monomial groupings used in SetEMastersI4Def.lean."""
    u = (
        a*b*(c+l+m) + a*c*(l+m+n) + a*n*(l+m) + b*c*(m+n)
        + b*(l*m+l*n+m*n) + c*l*(m+n) + l*m*n
    )
    f = (
        a*b*c*(a+b+c+2*(l+m+n)) + a*b*(a+b)*(l+m) + a*c*(a+c)*(l+m+n)
        + a*n*(a*(l+m)+2*(b*(l+m)+c*l)) + b*c*(b+c)*(m+n)
        + b**2*(l*m+l*n+m*n) + c*l*(2*b+c)*(m+n)
    )
    return u, f


def check_polynomials():
    for a, b, c, l, m, n in [(1, 2, 3, 4, 5, 6), (7, 1, 13, 2, 11, 5)]:
        matrix = mp.matrix([
            [a+b+l, a+b, b],
            [a+b, a+b+c+m, b+c],
            [b, b+c, b+c+n],
        ])
        v = mp.matrix([a+b, a+b+c, b+c])
        u, f = symanzik(a, b, c, l, m, n)
        assert mp.almosteq(u, mp.det(matrix))
        assert mp.almosteq(f, u * (v.T * mp.lu_solve(matrix, v))[0])


def quadrature(degree, power, epsilons, dtype):
    nodes, weights = mp.gauss_quadrature(degree, "legendre")

    def as_array(values):
        return np.array([str(x) for x in values], dtype=dtype)

    s = as_array((1 + x) / 2 for x in nodes)
    w = as_array(x / 2 for x in weights) * power * s**(power - 1)
    results = np.zeros(3 + len(epsilons), dtype=dtype)
    eps = as_array(epsilons)

    # Batch on t1 to keep memory O(degree^4).
    grid = np.ix_(s**power, s**power, s**power, s**power)
    weight = (
        w[:, None, None, None] * w[None, :, None, None]
        * w[None, None, :, None] * w[None, None, None, :]
    )
    orders = [
        order for order in permutations(range(6))
        if order < tuple(order[i] for i in (2, 1, 0, 5, 4, 3))
    ]
    for first, first_weight in zip(s**power, w):
        t = (first, *grid)
        params = [dtype(1)]
        for factor in t:
            params.append(params[-1] * factor)
        # Use homogeneity to combine the normalization and the Jacobian.
        jacobian = first_weight * weight * t[0]**4 * t[1]**3 * t[2]**2 * t[3]
        for order in orders:
            u, f = symanzik(*(params[i] for i in order))
            density = 2 * jacobian / u**2
            log_factor = 4*np.log(u) - 3*np.log(f)
            results[0] += np.sum(density)
            results[1] += np.sum(density * log_factor)
            results[2] += np.sum(density * log_factor**2 / 2)
            for i, e in enumerate(eps):
                results[3+i] += np.sum(density * np.exp(e * log_factor))
    return [mp.mpf(str(x)) for x in results]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, default=8)
    parser.add_argument("--power", type=int, default=2)
    parser.add_argument("--epsilon", nargs="+", default=["0.005", "0.01", "0.02"])
    parser.add_argument("--float64", action="store_true", help="use float64 for a faster scan")
    args = parser.parse_args()
    mp.mp.dps = 45
    check_polynomials()
    epsilons = [mp.mpf(e) for e in args.epsilon]
    pole, constant, linear = targets()
    expected = [3*pole, 3*constant, 3*(linear - mp.pi**2*pole/2)]
    dtype = np.float64 if args.float64 else np.longdouble
    values = quadrature(args.degree, args.power, epsilons, dtype)
    for j, (actual, target) in enumerate(zip(values[:3], expected)):
        print(f"P{j}: {mp.nstr(actual, 21)}   error {mp.nstr(actual-target, 10)}")
    for e, p in zip(epsilons, values[3:]):
        master = mp.gamma(1+3*e) / mp.gamma(1+e)**3 * p / (3*e)
        residual = (master - (pole/e + constant + linear*e)) / e**2
        print(f"eps={e}   I4/C={mp.nstr(master, 21)}   scaled residual={mp.nstr(residual, 12)}")


if __name__ == "__main__":
    main()
