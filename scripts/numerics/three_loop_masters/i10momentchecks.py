"""Check the auxiliary I10 logarithmic moments and kernels with mpmath."""

import mpmath as mp


def check(name, integral, value):
    error = abs(integral - value)
    print(f"{name}: absolute error {mp.nstr(error, 6)}")
    assert error < mp.mpf("1e-30"), name


def check_log_moments():
    z2, z3, z4 = [mp.zeta(n) for n in (2, 3, 4)]
    path = [0, mp.mpf("0.5"), 1]

    def bubble(r):
        return mp.log1p(-r)**2 / 2 * (z2 + mp.log(r)**2 / 2 + (1 + mp.log(r)) / r)

    def density_moment(r):
        c, log_c = 1 - r, mp.log1p(-r)
        return c * (log_c - mp.log(r)) * (r + c * log_c) / r**2

    check("K_a mixed log squares",
          mp.quad(lambda r: mp.log(r)**2 * mp.log1p(-r)**2, path),
          24 - 8 * z2 - 8 * z3 - z4)
    check("K_a cubic bubble", mp.quad(bubble, path), 6 - z2 - z3 - z4 / 2)
    check("K_2 linear density moment", mp.quad(density_moment, path), 1 + z2 - 2 * z3)
    check("K_2 regularized log product",
          mp.quad(lambda r: mp.log(r) * (mp.log1p(-r) + r) / r**2, path), z2 - 1)
    check("K_2 squared log over r squared",
          mp.quad(lambda r: mp.log1p(-r)**2 / r**2, path), 2 * z2)


def check_ka_swapped(z):
    c = 1 - z
    log_c = mp.log(c)
    li2 = mp.polylog(2, z)
    j = (mp.log(z) * log_c**2 + 2 * log_c * mp.polylog(2, c)
         - 2 * mp.polylog(3, c) + 2 * mp.zeta(3))
    first = (li2 - c * log_c) / z - 2
    second = 6 + (-c * log_c**2 + 4 * c * log_c - j - 2 * li2) / z
    for n, value in ((1, first), (2, second)):
        quad = mp.quad(lambda x: -mp.log(x) * mp.log1p(-z * x)**n, [0, mp.mpf("0.5"), 1])
        check(f"K_a swapped [{z}] log power {n}", quad, value)


def check_inner(t):
    c = 1 - t

    def first_primitive(x):
        return x**2 * (mp.log(x) / 2 - mp.mpf(1) / 4)

    def second_primitive(x):
        log = mp.log(x)
        return x**2 / 2 * (log**2 - log + mp.mpf(1) / 2)

    first = (first_primitive(1) - first_primitive(c)) / t
    second = (second_primitive(1) - second_primitive(c)) / t
    landen = mp.polylog(2, t) + mp.log(c)**2 / 2
    mixed = -(c**2 * landen / 2 +
              (first_primitive(1) - first_primitive(c) + c * (-1 - c * (mp.log(c) - 1))) / 2 -
              (1 - c**2) / 8 - c * t / 4) / t

    def base(u):
        return c + t * u

    def coeff(u, order):
        log_ratio = mp.log(t) - mp.log(u)
        log_base = mp.log(base(u))
        quotient = base(u) * log_base / t
        if order == 1:
            return -(1 - u) * log_ratio - 3 * quotient
        return -(1 - u) * log_ratio**2 / 2 - 3 * quotient * log_ratio + 9 * quotient * log_base / 2

    path = [0, mp.mpf("0.5"), 1]
    log_t = mp.log(t)
    first_coeff = -log_t / 2 - mp.mpf(3) / 4 - 3 * first / t
    second_coeff = (-log_t**2 / 4 - 3 * log_t / 4 - mp.mpf(7) / 8
                    - 3 * (log_t * first - mixed) / t + 9 * second / (2 * t))
    check(f"psi [{t}] pure log", mp.quad(lambda u: base(u) * mp.log(base(u)), path), first)
    check(f"psi [{t}] pure log squared",
          mp.quad(lambda u: base(u) * mp.log(base(u))**2, path), second)
    check(f"psi [{t}] mixed log",
          mp.quad(lambda u: base(u) * mp.log(base(u)) * mp.log(u), path), mixed)
    check(f"psi [{t}] degree one", mp.quad(lambda u: coeff(u, 1), path), first_coeff)
    check(f"psi [{t}] degree two", mp.quad(lambda u: coeff(u, 2), path), second_coeff)


def check_join(x):
    def weight(z):
        return mp.log(z * (1 - z))

    def kernel(z):
        return ((mp.log1p(-z)**2 - mp.log(z)**2) / 2 + mp.polylog(2, z) -
                mp.polylog(2, 1 - z))

    def primitive(z):
        log_z, log_c = mp.log(z), mp.log1p(-z)
        j = kernel(z)
        return (log_z + log_c + 1 - j) / z + log_z - log_c + j

    check(f"join [{x}] unweighted",
          mp.quad(lambda z: 1 / z, [x, 1]) - mp.quad(lambda z: 1 / (1 - z), [0, x]),
          mp.log1p(-x) - mp.log(x))
    check(f"join [{x}] weighted",
          mp.quad(lambda z: weight(z) / z, [x, 1]) -
          mp.quad(lambda z: weight(z) / (1 - z), [0, x]), kernel(x))
    check(f"join [{x}] radial", mp.quad(lambda z: kernel(z) / z**2, [x, 1]), 1 - primitive(x))


if __name__ == "__main__":
    with mp.workdps(85):
        check_log_moments()
        for z in map(mp.mpf, ("0.07", "0.42", "0.93")):
            check_ka_swapped(z)
        for t in map(mp.mpf, ("0.025", "0.4", "0.9", "0.999")):
            check_inner(t)
        for x in map(mp.mpf, ("0.07", "0.43", "0.88")):
            check_join(x)
