"""Generate HPL primitives and endpoint expansions for two reduced I10 integrals.

Run with Python 3 and sympy. Words use the conventions of QED/Polylog/HPLBasic.lean.
The coefficient and series checks are symbolic. Lean must still verify the analytic
reductions and justify the endpoint limits of the generated primitives.
"""

from collections import Counter, defaultdict
from functools import cache

import sympy as s


t, a, b, li2, j2 = s.symbols("t a b li2 j2")
z2, z3, z4 = s.symbols("z2 z3 z4")
delta, log_delta = s.symbols("delta log_delta")
c = 1 - t


@cache
def shuffle(u, v):
    if not u or not v:
        return Counter({u + v: 1})
    return (Counter({u[0] + w: n for w, n in shuffle(u[1:], v).items()})
            + Counter({v[0] + w: n for w, n in shuffle(u, v[1:]).items()}))


def hpl_product(left, right):
    out = defaultdict(int)
    for u, uc in left.items():
        for v, vc in right.items():
            for w, mult in shuffle(u, v).items():
                out[w] += uc * vc * mult
    return out


def hpl_form(expr):
    out = defaultdict(int)
    generators = ({"0": 1}, {"1": -1}, {"01": 1}, {"011": 2})
    for powers, coefficient in s.Poly(s.cancel(expr), a, b, li2, j2).terms():
        product = {"": 1}
        for generator, power in zip(generators, powers, strict=True):
            for _ in range(power):
                product = hpl_product(product, generator)
        for w, number in product.items():
            out[w] += number * coefficient
    return {w: r for w, raw in out.items() if (r := s.cancel(raw)) != 0}


def kernel(letter):
    return 1 / (t if letter == "0" else c)


def primitive(expr):
    pending = hpl_form(expr)
    out = defaultdict(int)
    for length in range(max(map(len, pending)), -1, -1):
        for w in sorted(w for w in pending if len(w) == length):
            residue = [0, 0]
            rational = 0
            for term in s.Add.make_args(s.apart(pending[w], t)):
                if not term.has(t):
                    rational += term * t
                    continue
                numerator, denominator = term.as_numer_denom()
                shift = 0 if denominator.subs(t, 0) == 0 else 1
                if s.degree(denominator, t) == 1 and s.degree(numerator, t) == 0:
                    factor = t if shift == 0 else c
                    residue[shift] += s.cancel(term * factor)
                else:
                    rational += s.integrate(term, t)
            assert not rational.has(s.log)
            out["0" + w] += residue[0]
            out["1" + w] += residue[1]
            out[w] += rational
            if w:
                tail = w[1:]
                pending[tail] = pending.get(tail, 0) - rational * kernel(w[0])
    return {w: r for w, raw in sorted(out.items()) if (r := s.cancel(raw)) != 0}


@cache
def regularized_one(w):
    # Values for words starting with 0 from QED.Polylog.HPLValues{,3,4}.
    values = {"": 1, "01": z2, "001": z3, "010": -2 * z3, "011": z3,
              "0001": z4, "0010": -3 * z4, "0011": z4 / 4, "0100": 3 * z4,
              "0101": 3 * z4 / 4, "0110": -5 * z4 / 4, "0111": z4}
    if not w or w[0] == "0":
        return 0 if w and "1" not in w else values[w]
    if "0" not in w:
        return 0
    products = shuffle("1", w[1:])
    return s.expand(-sum(n * regularized_one(v) for v, n in products.items() if v != w)
                    / products[w])


@cache
def hpl_series(w, right, depth):
    if not w:
        return s.S.One
    # The left expansion uses the all-zero convention and vanishing for nonzero words.
    if not right and "1" not in w:
        return log_delta**len(w) / s.factorial(len(w))
    tail = hpl_series(w[1:], right, depth)
    pole = (w[0] == "1") if right else (w[0] == "0")
    sign = -1 if right else 1
    derivative = tail / delta if pole else tail * sum(delta**n for n in range(depth))
    out = regularized_one(w) if right else 0
    derivative = s.expand(sign * derivative)
    for n in range(-1, depth):
        coefficient = derivative.coeff(delta, n)
        if n == -1:
            out += s.integrate(coefficient, log_delta)
        else:
            # Primitive for delta^n times a polynomial in log(delta).
            log_degree = s.degree(coefficient, log_delta)
            if coefficient != 0:
                reduced = sum((-1)**k * s.diff(coefficient, log_delta, k) / (n + 1)**(k + 1)
                              for k in range(log_degree + 1))
                out += delta**(n + 1) * reduced
    return s.expand(out)


def endpoint(anti, right):
    val = 0
    at = 1 - delta if right else delta
    for w, coeff in anti.items():
        rational = s.series(coeff.subs(t, at), delta, 0, 1).removeO().expand()
        depth = max(0, -min(term.as_powers_dict().get(delta, 0)
                            for term in s.Add.make_args(rational)))
        val += rational * hpl_series(w, right, depth)
    small = s.expand(val)
    for n in (-3, -2, -1):
        assert small.coeff(delta, n) == 0, (right, n, small.coeff(delta, n))
    constant = small.coeff(delta, 0)
    assert not constant.has(log_delta), (right, constant)
    return constant


def ka():
    l = a + b
    f = (li2 - c * b) / t - 2
    g = 6 + (-c * b**2 + 4 * c * b - j2 - 2 * li2) / t
    f_end, g_end = z2 - 2, 6 - 2 * z3 - 2 * z2
    return (g / (2 * t) + l * f / t
            + (1 / c + 1 / c**2) * ((g - a**2 - 2 * f_end * a - g_end) / 2
                                    + l * (f - a - f_end)) + (z3 - z2 * l) / c)


def k2():
    def derivative(f):
        return s.diff(f, t) + s.diff(f, a) / t - s.diff(f, b) / c - s.diff(f, li2) * b / t
    p1 = -a / 2 - s.Rational(3, 2) + 3 / (2 * t) + 3 * c**2 * b / (2 * t**2)
    p2 = -a**2 / 4 + 3 * c * a / (2 * t) - 5 + 6 / t + (
        3 * c**2 * (-li2 + a * b - 2 * b**2 + 3 * b) / (2 * t**2))
    d0 = 2 * t * c * (b - a)
    d1 = (2 * c * (3 * t - 1) * (li2 + a * b) - t * c * a**2 - 2 * t * (2 - t) * a
          + c * (1 - 2 * t) * b**2 + 2 * c * (1 + t) * b)
    return d0 * derivative(p2) + d1 * derivative(p1)


def verify_derivative(expr, anti):
    derivative = defaultdict(int)
    for w, r in anti.items():
        derivative[w] += s.diff(r, t)
        if w:
            derivative[w[1:]] += r * kernel(w[0])
    target = hpl_form(expr)
    assert all(s.cancel(derivative[w] - target.get(w, 0)) == 0 for w in derivative)
    assert target.keys() <= derivative.keys()


def main():
    for name, expr, expected in [
        ("Ka", ka(), 13 * (z4 - z2)),
        ("K2", k2(), 363 * z4 / 2 - 60 * z2 - 38 * z3 - 49),
    ]:
        anti = primitive(expr)
        verify_derivative(expr, anti)
        print(name, "primitive")
        for w, coeff in anti.items():
            print(f"{w or '[]':6} {s.apart(coeff, t)}")
        low, high = endpoint(anti, False), endpoint(anti, True)
        actual = s.expand(high - low).subs(z2**2, 5 * z4 / 2)
        assert s.expand(actual - expected) == 0, (name, actual, expected)
        print("at 0:", low)
        print("at 1:", high)
        print("value:", actual)


if __name__ == "__main__":
    main()
