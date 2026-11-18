#!/usr/bin/env python3
"""Checks (not proofs) of the pointwise targets of QED/TwoLoop/UnitXGraphTraceMain.lean and of
the merged integrand of QED/TwoLoop/UnitXGraphReduce*.lean.

1. c2[T1] = (3/K) Psi1/U^6, c2[T2] = -(1/K) Psi2/U^5, c2[T3] = 0 (K = 16 pi^4/(64 i), the factor
   (Lambda^2 - m_gamma^2)^2 = 1 here) against the finite-difference model of lean_crossed.py, at
   several points z (including an unequal split of the electron pair).
2. Psi1, Psi2 are affine in the split t = z1 of the pair, and the merged integrand
   M Psi1(M/2)/(2 U^6), -M Psi2(M/2)/(2 U^5) equals the engine coefficients A[2], A[1] of
   ../two_loop_unit_integrals.py (`integrand_parts('X', [A, M, c, a, b])`): engine group order
   z1 = A (line 0), z2 = M (lines 1, 2), z3 = c (line 3), za = a (lines 4, 6), zb = b (5, 7).
Run: nice -n 10 python3 target_check.py
"""
import math, os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from lean_crossed import parts_c2

K = 16 * math.pi ** 4 / (64j)


def groups(z):
    return z[0], z[1], z[1] + z[2], z[3], z[4] + z[6], z[5] + z[7]


def lean_data(A, t, M, c, a, b):
    U = A*M + A*c + A*b + M*c + M*a + M*b + c*a + a*b
    an = [A*M + A*b + M*b + a*b, -(A*c) + a*b, -(A*c) + a*b, M*c + M*a + c*a + a*b]
    bn = [A*t + A*b + M*b + t*a + a*b, A*t + A*b + t*c + t*a + t*b + a*b,
          -(A*M - A*t + A*c + M*c + M*a + M*b - t*c - t*a - t*b + c*a), -(M*b) + t*c + t*b]
    Cn = [A + a, A + a, -M, A + c + a + b, c + b, c + b]
    return U, an, bn, Cn


def psi1(a0, a1, a2, a3, b0, b1, b2, b3, u):
    return (2*a0*a1*a2*a3 - a0*a1*a2*u - 2*a0*a1*a3*b2 + a0*a1*b2*u - a0*a1*b3*u - a0*a1*u**2
            + 2*a0*a2*a3*b1 - a0*a2*a3*u - a0*a2*b1*u + a0*a2*b3*u + a0*a3*b1*u - a0*a3*b2*u
            - a0*b1*u**2 + a0*b2*u**2 + a1*a2*b0*u - a1*a2*b3*u - a1*a2*u**2 - a1*a3*b0*u
            + a1*a3*b2*u + a1*b0*u**2 - a1*b2*u**2 + a1*b3*u**2 + a2*a3*b0*u - a2*a3*b1*u
            - a2*a3*u**2 - a2*b0*u**2 + a2*b1*u**2 - a2*b3*u**2 + 2*a2*u**3 - a3*b1*u**2
            + a3*b2*u**2 - a3*u**3 - b0*u**3 + 2*b1*u**3 - 2*b2*u**3 + b3*u**3)


def psi2(a0, a1, a2, a3, b0, b1, b2, b3, c01, c02, c03, c12, c13, c23, u):
    return (c01*(a2*a3 + a2*b3 - 2*a2*u - a3*b2 + a3*u + 2*b2*u - b3*u)
            + c02*(a1*a3 - a1*b3 - a1*u + a3*b1 - 2*a3*u + 2*b3*u)
            + c03*(4*a1*a2 - 4*a1*b2 - a1*u + 4*a2*b1 - a2*u)
            + c12*(a3*u + b0*u - b3*u)
            + c13*(a0*a2 - a0*b2 + a2*b0 - a2*u - 2*b0*u)
            + c23*(a0*a1 + a0*b1 - a1*b0 + b0*u - 2*b1*u))


def Psi(A, t, M, c, a, b):
    U, an, bn, Cn = lean_data(A, t, M, c, a, b)
    return U, psi1(*an, *bn, U), psi2(*an, *bn, *Cn, U)


print('1. pointwise second coefficients against the model (ratios should be 1, t3 ~ 0)')
rng = np.random.default_rng(11)
for trial in range(4):
    z = rng.random(8) + 0.1
    z[6] = z[7] = 0.0 if trial < 2 else z[6]
    A, t, M, c, a, b = groups(z)
    U, P1, P2 = Psi(A, t, M, c, a, b)
    t1, t2, t3 = parts_c2(z, 1.0)
    print('   ', np.round(t1 / ((3 / K) * P1 / U ** 6), 7), np.round(t2 / (-(1 / K) * P2 / U ** 5), 7),
          ' |t3| =', abs(t3))

print('2. affine in the split, and the merged integrand against the engine')
import sympy as sp
import two_loop_unit_integrals as E
As, Ms, cs, as_, bs, ts = sp.symbols('A M c a b t', positive=True)
U, P1, P2 = Psi(As, ts, Ms, cs, as_, bs)
print('    d2 Psi1/dt2 =', sp.expand(sp.diff(P1, ts, 2)), '  d2 Psi2/dt2 =', sp.expand(sp.diff(P2, ts, 2)))
Aeng, Ueng, D0 = E.integrand_parts('X', [As, Ms, cs, as_, bs])
print('    U engine - U lean =', sp.expand(Ueng - U))
m1 = Ms * P1.subs(ts, Ms / 2) / (2 * U ** 6)
m2 = -Ms * P2.subs(ts, Ms / 2) / (2 * U ** 5)
pt = {As: sp.Rational(3, 7), Ms: sp.Rational(2, 9), cs: sp.Rational(5, 11), as_: sp.Rational(1, 3),
      bs: sp.Rational(4, 13)}
print('    A[2] engine / merged T1 :', sp.nsimplify(Aeng[2].subs(pt) / m1.subs(pt)))
print('    A[1] engine / merged T2 :', sp.nsimplify(Aeng[1].subs(pt) / m2.subs(pt)))
print('    exact identities: ', sp.simplify(sp.together(Aeng[2] - m1)) == 0,
      sp.simplify(sp.together(Aeng[1] - m2)) == 0)
