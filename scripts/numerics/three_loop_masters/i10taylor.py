# Provenance: scripts/numerics/three_loop_masters/i10taylor.py (numpy + scipy).
# I10: the Taylor coefficients at e = 0 of the convergent integrals of
# QED/ThreeLoopE/SetEMastersI10Def.lean, computed directly: every integrand is evaluated as a
# truncated power series in e (x^(a + b e) = x^a sum_k (b log x)^k e^k / k!) at each node of a
# tensor tanh-sinh rule, and each coefficient is integrated. No fit in e.
#   Ka  (pair (z, rho)),  Kab (triple (z, rho, sig)),  G0 (sig, u),  K2 ((z, rho, sig), u),
#   Rest = (2 Ka + e Kab)/(1 - e) + 2 (e B(e, 1 + e)) G0 + e K2   (= e (T - Closed)).
# Run: python i10taylor.py n [M]   (n nodes per dimension, M orders e^0 .. e^(M-1))
import sys
import numpy as np
from scipy.special import zeta

M = 6

def ts_nodes(n, tmax=3.2):
    """tanh-sinh nodes on (0,1): x, 1 - x (without cancellation), log x, log(1 - x), weights."""
    t = np.linspace(-tmax, tmax, n); h = t[1] - t[0]
    u = np.pi * np.sinh(t)
    x = 1 / (1 + np.exp(-u)); xc = 1 / (1 + np.exp(u))
    w = h * np.pi * np.cosh(t) * x * xc
    m = (x > 0) & (xc > 0)
    x, xc, w = x[m], xc[m], w[m]
    with np.errstate(divide='ignore'):
        lx = np.where(x < 0.5, np.log(x), np.log1p(-xc))
        lxc = np.where(xc < 0.5, np.log(xc), np.log1p(-x))
    return x, xc, lx, lxc, w

def sexp(L):
    """exp(e L) as a series: [L^k / k!]."""
    out = [np.ones_like(L)]
    for k in range(1, M):
        out.append(out[-1] * L / k)
    return out

def smul(a, b):
    return [sum(a[i] * b[k - i] for i in range(k + 1)) for k in range(M)]

def sscale(a, c):
    return [ak * c for ak in a]

def ssub(a, b):
    return [x - y for x, y in zip(a, b)]

def sshift(a):
    """e * a."""
    return [np.zeros_like(a[0])] + a[:-1]

def sint(a, w):
    return np.array([np.sum(ak * w) for ak in a])

def ka(n):
    x, xc, lx, lxc, w = ts_nodes(n)
    Z, Zc, lZ, lZc = x[:, None], xc[:, None], lx[:, None], lxc[:, None]
    R, lR, lRc = x[None, :], lx[None, :], lxc[None, :]
    lZR = lZ + lR
    Am1 = sexp(-lRc); Am1[0] = np.zeros_like(Am1[0])          # A(rho) - 1
    W = sscale(sexp(lZ + lZc), 1 / (Z * Zc))                    # (z(1 - z))^(e - 1)
    # the bracket, two forms without cancellation (z < 1/2, z >= 1/2)
    lo = Z < 0.5
    l1 = np.log1p(-Z * xc[None, :])                                 # log(1 - z(1 - rho))
    L1 = np.log1p(Zc / (Z * R))                                 # log((1 - z(1 - rho))/(z rho))
    zr = sexp(lZR)
    br = [np.zeros_like(Z * R)]
    fk = 1.0
    for k in range(1, M):
        fk *= k
        # z < 1/2: [l1^k - lZR^k z(2 - z)] / ((1 - z) k!)  (the term -(1-z)(1-(z rho)^e) included)
        a = (l1 ** k - lZR ** k * Z * (2 - Z)) / (Zc * fk)
        # z >= 1/2: (z rho)^e expm1(e L1) / (1 - z) + (1 - z) (z rho)^e, coefficient k
        b = sum(zr[j] * L1 ** (k - j) / np.prod(range(1, k - j + 1)) for j in range(k)) / Zc
        b = b + Zc * zr[k]
        c = -Z / R * lR ** (k - 1) / np.prod(range(1, k))      # - e z rho^(e - 1)
        br.append(np.where(lo, a, b) + c)
    f = smul(smul(Am1, W), br)
    return sint(f, w[:, None] * w[None, :])

def kab(n):
    x, xc, lx, lxc, w = ts_nodes(n)
    R, lR, lRc = x[:, None], lx[:, None], lxc[:, None]
    S, lS, lSc = x[None, :], lx[None, :], lxc[None, :]
    Ar = sexp(-lRc); Ar[0] = np.zeros_like(Ar[0])
    As = sexp(-lSc); As[0] = np.zeros_like(As[0])
    Am = smul(Ar, As)
    W2 = w[:, None] * w[None, :]
    sR = sscale(sexp(lR), 1 / R); sS = sscale(sexp(lS), 1 / S)
    tot = np.zeros(M)
    for k in range(len(x)):
        z, zc = x[k], xc[k]
        tau = z * R + zc * S
        br = ssub(ssub(sscale(sexp(np.log(tau)), 1 / tau), sscale(sS, zc)), sscale(sR, z))
        Wz = sscale(sexp(np.full(1, lx[k] + lxc[k])), w[k] / (z * zc))
        tot += sint(smul(Wz, smul(Am, br)), W2)
    return tot

def gfun(t, tc, lt, u, uc):
    """g(t) = t^(e - 1) ((1 - (1 - u) t)^(1 - 3e) - 1) as a series (tc = 1 - t, uc = 1 - u)."""
    q1 = uc * t
    q = tc + u * t                                              # 1 - (1 - u) t
    with np.errstate(divide='ignore', invalid='ignore'):
        lq = np.where(q1 < 0.5, np.log1p(-q1), np.log(q))
    h = [-uc * np.ones_like(t)]                                 # ((q - 1)/t), order 0
    c = np.ones_like(t)
    for k in range(1, M):
        c = c * (-3 * lq) / k
        h.append(q * c / t)
    return smul(sexp(lt), h)

def g0(n):
    x, xc, lx, lxc, w = ts_nodes(n)
    S, lS, lSc = x[:, None], lx[:, None], lxc[:, None]
    U, Uc, lU = x[None, :], xc[None, :], lx[None, :]
    f = smul(smul(sexp(-lSc), sexp(-lU)), gfun(S, xc[:, None], lS, U, Uc))
    I = sint(f, w[:, None] * w[None, :])
    # divide by (1 - e)
    return np.array([I[:k + 1].sum() for k in range(M)])

def k2(n):
    x, xc, lx, lxc, w = ts_nodes(n)
    R, lR, lRc = x[:, None, None], lx[:, None, None], lxc[:, None, None]
    S, lS, lSc = x[None, :, None], lx[None, :, None], lxc[None, :, None]
    U, Uc, lU = x[None, None, :], xc[None, None, :], lx[None, None, :]
    Rc, Sc = xc[:, None, None], xc[None, :, None]
    AA = smul(sexp(-lRc), sexp(-lSc))
    Uf = sexp(-lU)
    pref = smul(AA, Uf)
    W3 = w[:, None, None] * w[None, :, None] * w[None, None, :]
    gR = gfun(R, Rc, lR, U, Uc); gS = gfun(S, Sc, lS, U, Uc)
    tot = np.zeros(M)
    for k in range(len(x)):
        z, zc = x[k], xc[k]
        tau = z * R + zc * S
        tauc = z * Rc + zc * Sc
        br = ssub(ssub(gfun(tau, tauc, np.log(tau), U, Uc), sscale(gS, zc)), sscale(gR, z))
        Wz = sscale(sexp(np.full(1, lx[k] + lxc[k])), w[k] / (z * zc))
        tot += sint(smul(Wz, smul(pref, br)), W3)
    return tot

def ebeta():
    """Taylor coefficients of e B(e, 1 + e) = Gam(1 + e)^2 / Gam(1 + 2e)."""
    # log = sum_(k >= 2) (-1)^k zeta(k) (2 - 2^k) / k e^k  (log Gam(1 + z) = -gamma z + ...)
    lg = np.array([0.0] + [0.0] + [(-1) ** k * zeta(k) * (2 - 2 ** k) / k for k in range(2, M)])
    out = np.zeros(M); out[0] = 1.0
    term = out.copy()
    for j in range(1, M):
        term = series_mul(term, lg) / j
        out = out + term
    return out

def series_mul(a, b):
    return np.array([sum(a[i] * b[k - i] for i in range(k + 1)) for k in range(M)])

if __name__ == '__main__':
    n = int(sys.argv[1])
    if len(sys.argv) > 2:
        M = int(sys.argv[2])
    Ka, Kab, G0, K2 = ka(n), kab(n), g0(n), k2(n)
    geo = np.ones(M)
    shift = lambda a: np.concatenate([[0.0], a[:-1]])
    Rest = (series_mul(2 * Ka + shift(Kab), geo) + 2 * series_mul(ebeta(), G0) + shift(K2))
    np.set_printoptions(precision=15, linewidth=120)
    for name, v in [('Ka', Ka), ('Kab', Kab), ('G0', G0), ('K2', K2), ('Rest', Rest)]:
        print(n, name, ' '.join(repr(float(c)) for c in v), flush=True)
