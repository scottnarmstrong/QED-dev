#!/usr/bin/env python3
"""Numerical sanity checks for the one-loop vertex route. NOT a proof.

These floating-point checks guard the hand derivation in
docs/ONE-LOOP-DERIVATION.md and docs/REGULARIZATION.md against algebra slips.
They certify nothing; every statement checked here is a proof obligation.

Conventions: metric (+,-,-,-), Dirac representation, m = 1, the vertex numerator
k-slash gamma^mu k'-slash + m^2 gamma^mu - 2m(k+k')^mu (Feynman gauge).

Checks:
  1. Clifford relations; the 4D contraction identity for the vertex numerator.
  2. On-shell reduction after the Feynman-parameter shift k = l - y q + z p:
     ubar' N u = ubar'[A gamma^mu + B (p+p')^mu + C q^mu] u with
     A = -l^2/2 + (1-x)(1-y) q^2 + (1-2z-z^2) m^2, B = m z(z-1),
     C = m (z-2)(x-y).
  3. Gordon identity.
  4. Energy-fiber integrals for w in C minus [0, inf), principal branch.
  5. 3D radial integral, and the product reproducing -i pi^2/(2 Delta).
  6. Regulated coefficient C1(mu, Lambda) approaching 1/2.
  7. Light-cone growth: the k0-integral of |(k^2 - D + i eps)^-3| at spatial
     radius rho decays only like 1/rho, so the 4D integral of the absolute
     value diverges (docs/campaign/FINDINGS.md, F-1).
  8. Breit-frame magnetic structure: the spatial current between Dirac-
     representation spinors is -i eps^{ijk} q^j xi'^dag sigma^k xi (F1 + F2),
     exactly in q.

Requires numpy and mpmath. Run: python3 scripts/numerics/one_loop_sanity.py
"""
import numpy as np, mpmath as mp
rng = np.random.default_rng(1)
I2 = np.eye(2); Z2 = np.zeros((2,2))
sig = [np.array([[0,1],[1,0]],complex), np.array([[0,-1j],[1j,0]]), np.array([[1,0],[0,-1]],complex)]
g0 = np.block([[I2,Z2],[Z2,-I2]]).astype(complex)
gs = [np.block([[Z2,s],[-s,Z2]]) for s in sig]
G = [g0]+gs                      # gamma^mu (upper index)
eta = np.diag([1.,-1,-1,-1])
def low(v): return eta@v
def slash(p): return sum(G[m]*low(p)[m] for m in range(4))
# Clifford check
for a in range(4):
    for b in range(4):
        assert np.allclose(G[a]@G[b]+G[b]@G[a], 2*eta[a,b]*np.eye(4))
m = 1.0
def onshell(pvec):
    return np.array([np.sqrt(m*m+pvec@pvec), *pvec])
def spinors(p):
    # columns: u(p,s) = (pslash + m) u0 / sqrt(E+m) ; normalized ubar u = 2m
    E = p[0]; out=[]
    for s in range(2):
        xi = np.zeros(2,complex); xi[s]=1
        u0 = np.concatenate([xi, np.zeros(2)])
        out.append((slash(p)+m*np.eye(4))@u0/np.sqrt(E+m))
    return out
def bar(u): return u.conj()@g0
p = onshell(rng.normal(size=3)*0.7); pp = onshell(rng.normal(size=3)*0.7); q = pp-p
U, Up = spinors(p), spinors(pp)
for u in U:
    assert np.allclose(slash(p)@u, m*u); assert np.isclose(bar(u)@u, 2*m)
# contraction identity: gamma^nu (k'slash+m) gamma^mu (kslash+m) gamma_nu = -2[kslash g^mu k'slash + m^2 g^mu - 2m (k+k')^mu]
k = rng.normal(size=4); kp = k+q
for mu in range(4):
    lhs = sum(G[n]@(slash(kp)+m*np.eye(4))@G[mu]@(slash(k)+m*np.eye(4))@G[n]*eta[n,n] for n in range(4))
    rhs = -2*(slash(k)@G[mu]@slash(kp) + m*m*G[mu] - 2*m*(k+kp)[mu]*np.eye(4))
    assert np.allclose(lhs, rhs)
# shifted numerator: k = l - y q + z p; drop odd l terms; l^a l^b -> eta^{ab} l^2/4
x,y = rng.uniform(size=2)*0.5; z = 1-x-y
c = -y*q + z*p   # k = l + c
def N(kk, mu): kpp = kk+q; return slash(kk)@G[mu]@slash(kpp) + m*m*G[mu] - 2*m*(kk+kpp)[mu]*np.eye(4)
l2 = 0.37   # arbitrary value of l^2
for mu in range(4):
    # l-independent part + symmetric-integration replacement of l l term
    N0 = N(c, mu)
    ll = sum(G[a]@G[mu]@G[b]*eta[a,b] for a in range(4) for b in range(4))*l2/4  # lslash g lslash -> g_a g^mu g^a l^2/4
    Nsym = N0 + ll
    A = -0.5*l2 + (1-x)*(1-y)*(q@eta@q) + (1-2*z-z*z)*m*m
    B = m*z*(z-1); C = m*(z-2)*(x-y)
    for up in Up:
        for u in U:
            lhs = bar(up)@Nsym@u
            rhs = bar(up)@(A*G[mu] + B*(p+pp)[mu]*np.eye(4) + C*q[mu]*np.eye(4))@u
            assert np.isclose(lhs, rhs), (mu, lhs, rhs)
# Gordon identity: ubar' (p+p')^mu u = ubar' [2m gamma^mu - i sigma^{mu nu} q_nu] u
def sigma(a,b): return 0.5j*(G[a]@G[b]-G[b]@G[a])
for mu in range(4):
    S = sum(sigma(mu,n)*low(q)[n] for n in range(4))
    for up in Up:
        for u in U:
            assert np.isclose(bar(up)@u*(p+pp)[mu], bar(up)@(2*m*G[mu]-1j*S)@u)
print("Dirac algebra, on-shell reduction, Gordon identity: OK")
# energy-fiber integrals with principal branch, w in C \ [0,inf)
for w in [mp.mpc(2,-0.3), mp.mpc(-1.5,0.2), mp.mpc(0.5,-1e-1), mp.mpc(3,1)]:
    r = mp.sqrt(abs(w)); pts=[-mp.inf,-2*r,-r-0.01,-r,-r+0.01,0,r-0.01,r,r+0.01,2*r,mp.inf]
    f3 = mp.quad(lambda t: 1/(t*t-w)**3, pts, maxdegree=10)
    f3t = mp.quad(lambda t: t*t/(t*t-w)**3, pts, maxdegree=10)
    assert abs(f3 - 3*mp.pi/(8*(-w)**mp.mpf(2.5))) < 1e-8, (w, f3)
    assert abs(f3t - mp.pi/(8*(-w)**mp.mpf(1.5))) < 1e-8, (w, f3t)
print("Energy-fiber integrals: OK")
# 3D radial: int d^3l (l^2+D)^(-5/2) = 4 pi/(3 D); so Minkowski int d^4l (l^2-D+i0)^-3 = -i pi^2/(2D)
D = mp.mpf(0.7)
r3 = 4*mp.pi*mp.quad(lambda r: r*r*(r*r+D)**mp.mpf(-2.5), [0, mp.inf])
assert abs(r3 - 4*mp.pi/(3*D)) < 1e-10
print("3D radial integral: OK; fiber*radial =", mp.chop(3*mp.pi/8*r3/(1j)), "vs", -1j*mp.pi**2/(2*D))
# F2(0) with photon mass mu and Pauli-Villars Lambda (units m=1): coefficient of alpha/pi
def C1(mu, Lam):
    f = lambda z, M: 2*z*(1-z)**2/((1-z)**2 + z*M*M)
    return 0.5*mp.quad(lambda z: f(z,mu)-f(z,Lam), [0,1])
for mu_, L_ in [(1e-1,1e1),(1e-2,1e2),(1e-3,1e3),(1e-4,1e4)]:
    print(f"mu={mu_:g} Lambda={L_:g}  C1={mp.nstr(C1(mu_,L_),10)}")

print('Light-cone check (eps = 0.1, Delta = 1):')
eps = mp.mpf('0.1'); D = mp.mpf(1)
def inner_abs(rho):
    w = rho*rho + D
    r = mp.sqrt(w)
    f = lambda t: 1/abs((t*t - w + 1j*eps))**3
    return 2*mp.quad(f, [0, r-0.5, r-0.01, r, r+0.01, r+0.5, 2*r, mp.inf])
for rho in [1, 10, 100, 1000]:
    v = inner_abs(mp.mpf(rho))
    print(f"rho={rho:5d}  int dk0 |f| = {mp.nstr(v,6)}   rho^2 * that = {mp.nstr(rho*rho*v,6)}")

# 8. Breit-frame magnetic structure: with Dirac-representation spinors
#    u(p, xi) = (sqrt(E+m) xi, (sigma.p) xi / sqrt(E+m)), ubar u = 2m, and
#    Gamma^mu = F1 gamma^mu + F2 i sigma^{mu nu} q_nu / (2m), the Breit frame
#    p = (E, -q/2), p' = (E, q/2) gives exactly
#    ubar(p', xi') Gamma^i u(p, xi) = -i eps^{ijk} q^j xi'^dag sigma^k xi (F1 + F2).
def sigma_mn(a, b): return 0.5j*(G[a]@G[b] - G[b]@G[a])
def u_dirac(p, xi):
    E = p[0]; sp = sum(sig[i]*p[1+i] for i in range(3))
    return np.concatenate([np.sqrt(E+m)*xi, sp@xi/np.sqrt(E+m)])
def levi(i, j, k): return (i-j)*(j-k)*(k-i)/2
F1, F2 = 0.83, 0.27
rngB = np.random.default_rng(3)
for trial in range(4):
    qv = rngB.normal(size=3)*0.6
    p = onshell(-qv/2); pp = onshell(qv/2); q = pp - p
    for i in range(3):
        Gam = F1*G[i+1] + F2/(2*m)*1j*sum(sigma_mn(i+1, n)*low(q)[n] for n in range(4))
        M = np.array([[bar(u_dirac(pp, np.eye(2)[a].astype(complex)))@Gam@u_dirac(p, np.eye(2)[b].astype(complex))
                       for b in range(2)] for a in range(2)])
        target = sum(-1j*levi(i, j, k)*qv[j]*sig[k] for j in range(3) for k in range(3))*(F1+F2)
        assert np.allclose(M, target)
print("Breit-frame magnetic current = -i eps q sigma (F1+F2): OK")
