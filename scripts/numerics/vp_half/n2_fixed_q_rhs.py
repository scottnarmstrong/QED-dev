# N2: the fixed-q right side of VPHalfSubAt (spectral superposition of five-mass one-loop kernels)
# equals the one-loop vertex kernel of the photon function (Pi_loop(K) - Pi_loop(0)) K D(K)^2,
# K = C/(1-y), C = y^2 (m^2 + x(1-x) s), at m = 1:
#   A(s) = sum_f c_f int_0^1 rho(v) (b^2-a^2)^2/2 int kernVP(1,a,b,mu_{f,v},s) dz dv
#   B(s) = sum_f c_f int dz 2 y^2 K D(K)^2 L_f(K),  L_f(K) = int_0^1 x(1-x) log(1 + x(1-x) K/M_f^2) dx
# (Pi_loop(K) - Pi_loop(0) = (e^2/(2 pi^2)) sum_f c_f L_f(K), Srednicki (62.25)).
import numpy as np
def gl(n, a, b):
    t, w = np.polynomial.legendre.leggauss(n)
    return 0.5*(b-a)*t + 0.5*(b+a), 0.5*(b-a)*w
a, b = 0.5, 3.0
M1, M2 = 2.0, 3.5
c1 = (M2**2-1)/(M1**2-M2**2); c2 = (M1**2-1)/(M2**2-M1**2)
flav = [(1.0, 1.0), (c1, M1), (c2, M2)]
rho = lambda v: v**2*(1-v**2/3)/(1-v**2)
def grid(n):
    # y in (0,1) with clustering at both ends via y = (1-cos(pi t))/2
    t, w = gl(n, 0.0, 1.0)
    y = (1-np.cos(np.pi*t))/2; wy = w*np.pi*np.sin(np.pi*t)/2
    x, wx = gl(n, 0.0, 1.0)
    return x, wx, y, wy
def A(s, n=200, nv=200):
    x, wx, y, wy = grid(n)
    X, Y = np.meshgrid(x, y, indexing='ij'); W = np.outer(wx, wy)
    C = Y**2*(1 + X*(1-X)*s)
    kd = lambda M: (1-Y)*M**2 + C
    # v = tanh(r): rho(v) dv = v^2(1-v^2/3) dr, mu^2 = 4 M^2 cosh(r)^2; r in (0, R)
    r, wr = gl(nv, 0.0, 12.0)
    v = np.tanh(r)
    tot = 0.0
    for cf, M in flav:
        acc = 0.0
        for ri, wri, vi in zip(r, wr, v):
            mu2 = 4*M**2*np.cosh(ri)**2
            k5 = 2*Y**2*(1-Y)*C**2*(1-Y)**2/(kd(a)**2*kd(b)**2*((1-Y)*mu2 + C))
            acc += wri*vi**2*(1-vi**2/3)*(b**2-a**2)**2/2*np.sum(W*k5)
        tot += cf*acc
    return tot
def L(K, M):
    xx, ww = gl(200, 0.0, 1.0)
    return np.sum(ww[None,None,:]*xx*(1-xx)*np.log1p(xx*(1-xx)*K[...,None]/M**2), axis=-1)
def B(s, n=200):
    x, wx, y, wy = grid(n)
    X, Y = np.meshgrid(x, y, indexing='ij'); W = np.outer(wx, wy)
    C = Y**2*(1 + X*(1-X)*s)
    K = C/(1-Y)
    D = 1/(K + a**2) - 1/(K + b**2)
    return sum(cf*np.sum(W*2*Y**2*K*D**2*L(K, M)) for cf, M in flav)
for s in [0.0, 0.7, 3.0]:
    av, bv = A(s), B(s)
    print(f"s={s}: A={av:.12e}  B={bv:.12e}  rel.diff={abs(av-bv)/abs(bv):.2e}")
