# Provenance: scripts/numerics/three_loop_masters/i10rep.py (numpy + scipy).
# I10: the subtracted representation of QED/ThreeLoopE/SetEMastersI10Def.lean (full-range
# subtraction, all closed parts Gamma functions), evaluated at real e near 0.
#   I10 C^-1 = Gam(3e-1) / Gam(1+e)^3 * T(e),
#   T  = S/(1-e) + 2 B(e,1+e) G0 + K2,
#   S  = S0 + 2 (Ca + Ka/e) + Cab + Kab.
# Run: python i10rep.py n e1 e2 ...
import sys
import numpy as np
from scipy.special import hyp2f1, gamma

def ts_nodes(n, tmax=3.2):
    """tanh-sinh nodes on (0,1): x, 1 - x (without cancellation), weights."""
    t = np.linspace(-tmax, tmax, n); h = t[1] - t[0]
    u = np.pi * np.sinh(t)
    x = 1 / (1 + np.exp(-u)); xc = 1 / (1 + np.exp(u))
    w = h * np.pi * np.cosh(t) * x * xc
    m = (x > 0) & (xc > 0)
    return x[m], xc[m], w[m]

def B(a, c): return gamma(a) * gamma(c) / gamma(a + c)

def psi(e, tau):  # int_0^1 u^-e tau^(e-1) ((1-(1-u) tau)^(1-3e) - 1) du
    return tau ** (e - 1) * (hyp2f1(3 * e - 1, 1, 2 - e, tau) - 1) / (1 - e)

def closed(e):
    S0 = (B(e - 1, e - 1) - 2 * B(2 * e, e - 1)) / (e * (1 + e))
    a0 = 1 / (1 - e) - 1                            # int (A - 1)
    a1 = gamma(1 + e) * gamma(1 - e) - 1 / (1 + e)  # int (A - 1) x^e
    a2 = gamma(e) * gamma(1 - e) - 1 / e            # int (A - 1) x^(e-1)
    Ca = B(e, 1 + e) * a0 / e - B(2 * e, 1 + e) * a1 / e + B(1 + e, e) * a2
    Cab = B(e, 1 + e) * a0 * a2 + B(1 + e, e) * a2 * a0
    return S0, Ca, Cab

def pieces(e, n):
    x, xc, w = ts_nodes(n)
    A = xc ** (-e)
    S0, Ca, Cab = closed(e)
    # Ka: pair (z, rho)
    Z = x[:, None]; Zc = xc[:, None]; R = x[None, :]
    ZR = Z * R  # ((1 - z(1 - rho))^e - (z rho)^e) / (1 - z), without cancellation:
    br = (ZR ** e * np.expm1(e * np.log1p(Zc / ZR)) / Zc - Zc * (1 - ZR ** e)
          - e * Z * R ** (e - 1))
    Ka = np.sum(w[:, None] * w[None, :] * (A[None, :] - 1) * (Z * Zc) ** (e - 1) * br)
    # Kab, K2: triple (z, rho, sig)
    Rr = x[:, None]; Ss = x[None, :]; W2 = w[:, None] * w[None, :]
    Am = (A[:, None] - 1) * (A[None, :] - 1); AA = A[:, None] * A[None, :]
    psR = psi(e, Rr); psS = psi(e, Ss)
    Kab = 0.0; K2 = 0.0
    for k in range(len(x)):
        z, zc = x[k], xc[k]
        tau = np.minimum(z * Rr + zc * Ss, 1.0)
        wz = w[k] * (z * zc) ** (e - 1)
        Kab += wz * np.sum(W2 * Am * (tau ** (e - 1) - zc * Ss ** (e - 1) - z * Rr ** (e - 1)))
        K2 += wz * np.sum(W2 * AA * (psi(e, tau) - zc * psS - z * psR))
    G0 = np.sum(w * A * psi(e, x)) / (1 - e)
    S = S0 + 2 * (Ca + Ka / e) + Cab + Kab
    T = S / (1 - e) + 2 * B(e, 1 + e) * G0 + K2
    return dict(S0=S0, Ca=Ca, Cab=Cab, Ka=Ka, Kab=Kab, G0=G0, K2=K2, S=S, T=T)

if __name__ == '__main__':
    n = int(sys.argv[1])
    for e in [float(v) for v in sys.argv[2:]]:
        p = pieces(e, n)
        print(e, n, repr(p['T']), gamma(3 * e - 1) / gamma(1 + e) ** 3 * p['T'],
              {k: float(v) for k, v in p.items()}, flush=True)
