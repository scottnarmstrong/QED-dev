# Provenance: scripts/numerics/three_loop_masters/i10grid.py (numpy + scipy).
# Usage: python i10grid.py 100,140,200 0.1 0.05
# I10 C^-1 = Gam(3e-1)/Gam(1+e)^3 * T(e),
# T = int_(0,1)^3 (1-rho)^-e (1-sig)^-e (z(1-z))^(e-1) tau^(e-1) Xi(tau),
# tau = z rho + (1-z) sig, Xi(tau) = 2F1(3e-1, 1; 2-e; tau)/(1-e).
# Tensor Gauss-Legendre after endpoint-flattening substitutions. Run with scipy (python3 + scipy).
import sys
import numpy as np
from scipy.special import hyp2f1, gamma, zeta
def nodes(n, e, lo_pow, hi_pow):
    # map (0,1/2) by x = s^(1/lo_pow)/2 and (1/2,1) by 1-x = r^(1/hi_pow)/2; return x, weights
    g, wg = np.polynomial.legendre.leggauss(n)
    s = (g + 1) / 2; ws = wg / 2
    xa = s ** (1 / lo_pow) / 2; wa = ws * (1 / lo_pow) * s ** (1 / lo_pow - 1) / 2
    yb = s ** (1 / hi_pow) / 2; wb = ws * (1 / hi_pow) * s ** (1 / hi_pow - 1) / 2
    # return x, 1 - x (computed without cancellation), weights
    return (np.concatenate([xa, 1 - yb]), np.concatenate([1 - xa, yb]),
            np.concatenate([wa, wb]))
def T(e, n):
    r, rc, wr = nodes(n, e, e, 1 - e)  # rho: rho^(e-1)-type near 0, (1-rho)^-e near 1
    z, zc, wz = nodes(n, e, e, e)      # z: z^(e-1), (1-z)^(e-1)
    R = r[:, None]; S = r[None, :]; Rc = rc[:, None]; Sc = rc[None, :]
    W2 = wr[:, None] * wr[None, :]
    base = Rc ** (-e) * Sc ** (-e)
    tot = 0.0
    for k in range(len(z)):  # one z-slice at a time (memory)
        tau = z[k] * R + zc[k] * S
        f = base * tau ** (e - 1) * hyp2f1(3 * e - 1, 1, 2 - e, tau) / (1 - e)
        tot += wz[k] * (z[k] * zc[k]) ** (e - 1) * np.sum(W2 * f)
    return tot
z3 = zeta(3); pi = np.pi
def L(e):
    return (-1/3/e**3 - 5/3/e**2 + (-2*pi**2/3 - 4)/e + (-26*z3/3 - 7*pi**2/3 + 10/3)
            + (-35*pi**4/18 - 94*z3/3 - pi**2 + 302/3) * e)
NS = [int(x) for x in sys.argv[1].split(',')]
for e in [float(x) for x in sys.argv[2:]]:
    for n in NS:
        t = T(e, n)
        v = gamma(3 * e - 1) / gamma(1 + e) ** 3 * t
        print(e, n, t, v, L(e), (v - L(e)) / e ** 2, flush=True)
