"""Check the four remainder coefficients of SetEMastersI10Def.lean with mpmath.

Run with Python 3 and mpmath. Two tanh-sinh meshes are compared with the
proposed coefficients, using an independently integrated Taylor integrand.
"""
import mpmath as mp


def nodes(step):
    """Symmetric double-exponential trapezoid rule on (0,1)."""
    step = mp.mpf(step)
    half_count = int(mp.mpf("4.2") / step)
    for j in range(-half_count, half_count + 1):
        y = j * step
        scale = mp.exp(mp.pi * mp.sinh(y))
        x = scale / (1 + scale)
        yield x, step * mp.pi * mp.cosh(y) * x * (1 - x)


def ka(mesh):
    totals = [mp.mpf(0), mp.mpf(0)]
    def integrand(z, r):
        c = 1 - z
        lw = mp.log(z * c)
        la = mp.log1p(-z * (1 - r))
        lr = mp.log(r)
        lb = mp.log(z) + lr
        ld = -mp.log1p(-r)
        b1 = (la - lb) / c + c * lb - z / r
        b2 = ((la - lb) * (la + lb) / c + c * lb**2) / 2 - z * lr / r
        w = ld / (z * c)
        return w * b1, w * (b2 + (lw + ld / 2) * b1)

    # Split the corner r, 1-z -> 0 along r = 1-z, then map each sector to a square.
    for a, wa in mesh:
        h = a / 2
        for b, wb in mesh:
            regions = (
                (h, b, mp.mpf("0.5")),
                (1 - h, (1 + b) / 2, mp.mpf("0.25")),
                (1 - h, h * b, h / 2),
                (1 - h * b, h, h / 2),
            )
            for z, r, jac in regions:
                f0, f1 = integrand(z, r)
                w = wa * wb * jac
                totals[0] += w * f0
                totals[1] += w * f1
    return totals


def joining_primitive(t, lt, lc, li, lic):
    """Primitive of J(t)/t^2 for the logarithm of the joining weight."""
    j = (lc**2 - lt**2) / 2 + li - lic
    return (lt + lc + 1 - j) / t + lt - lc + j


def joining_densities(t):
    """K2 acting on a function of tau, after transferring one t derivative.

    For r < t < s, put a=t-r, b=s-t. Integration in z gives log(b/a).
    With log(z(1-z)) inserted it gives J(a/(a+b)), where J is the expression
    in joining_primitive. Integrate over 0<a<t, 0<b<1-t and double by
    symmetry. For J, change variables to a+b and a/(a+b).
    """
    c = 1 - t
    lt, lc = mp.log(t), mp.log(c)
    li, lic = mp.polylog(2, t), mp.polylog(2, c)
    p = joining_primitive(t, lt, lc, li, lic)
    pc = joining_primitive(c, lc, lt, lic, li)
    log_joining = t**2 * (1 - p) - c**2 * (1 - pc)
    # Moments of -log(1-r) and -log(1-s), with and without log(a), log(b).
    a0 = t + c * lc
    b0 = c * (1 - lc)
    k = t / c
    avg = (-lc / t) - 1
    # Li2(-t/(1-t)) = -Li2(t) - log(1-t)^2/2.
    a1 = -t * ((lt - 1) * lc + (lt - 1) * avg + 1 - (li + lc**2 / 2) / k)
    b1 = -c * (lc**2 - 2 * lc + 2 - mp.zeta(2))
    log_bubbles = 2 * (c * (lc - 1) * a0 - c * a1 + t * b1 - t * (lt - 1) * b0)
    return 2 * t * c * (lc - lt), log_joining + log_bubbles


def k2(mesh):
    totals = [mp.mpf(0), mp.mpf(0)]
    log_mesh = [(u, mp.log(u), wu) for u, wu in mesh]
    for t, wt in mesh:
        d0, d1 = joining_densities(t)
        lt = mp.log(t)
        for u, lu, wu in log_mesh:
            v = 1 - u
            q = 1 - v * t
            lq = mp.log1p(-v * t)
            h = q * lq / t
            dh = (-v * (1 + lq) - h) / t
            dh2 = dh * lq - h * v / q
            dg1 = -v / t - 3 * dh
            dg2 = -v * (lt - lu) / t - 3 * (dh * (lt - lu) + h / t) + 9 * dh2 / 2
            totals[0] += wt * wu * d0 * dg1
            totals[1] += wt * wu * (d0 * dg2 + d1 * dg1)
    return totals


def main():
    with mp.workdps(155):
        p2 = mp.pi**2
        z3 = mp.zeta(3)
        proposed = [
            3 + p2 / 6 - 2 * z3,
            6 - 7 * p2 / 3 - z3 + 5 * p2**2 / 36,
            -5 - p2 + 12 * z3,
            121 * p2**2 / 60 - 10 * p2 - 38 * z3 - 49,
        ]
        labels = ("Ka[2]", "Ka[3]", "K2[1]", "K2[2]")
        for step in ("0.035", "0.03"):
            mesh = list(nodes(step))
            values = ka(mesh) + k2(mesh)
            for label, value, target in zip(labels, values, proposed):
                err = abs(value - target)
                print(step, label, mp.nstr(value, 33), "absolute error", mp.nstr(err, 4),
                      flush=True)
            assert all(abs(v - t) < mp.mpf("1e-30") for v, t in zip(values, proposed))


if __name__ == "__main__":
    main()
