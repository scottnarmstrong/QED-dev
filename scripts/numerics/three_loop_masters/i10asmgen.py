# Provenance: scripts/numerics/three_loop_masters/i10asmgen.py (system python3 with sympy).
# I10, the remainder Rest = (2 Ka + e Kab)/(1 - e) + 2 E_B G0 + e K2 of
# QED/ThreeLoopE/SetEMastersI10Wire.lean, assembled in QED/ThreeLoopE/SetEMastersI10Asm.lean.
# Inputs: G0 (closed form, i10g0gen.py), Kab (proved, QED/ThreeLoopE/SetEMastersI10KabVal.lean),
# Ka and K2 (identified from i10taylor.py; the e^2 coefficient of K2 is forced by Rest_L),
# E_B = G(1 + e)^2 / G(1 + 2e) = exp(-e^2 (pi^2/6 - 2 z3 e + 7 pi^4/180 e^2 + ...)).
# Checks that the orders e^0 .. e^3 of
#   2 Ka_L + e Kab_L + (1 - e)(2 E_Bp G0_L + e K2_L) - (1 - e) Rest_L
# vanish and prints the quotient by e^4 (i10AsmW of i10Asm_key; P = pi, Z = zeta3).
# Run: python3 i10asmgen.py
import sympy as sp

e, P, Z = sp.symbols('e P Z')
R = sp.Rational

def Ep(x0, x1, x2):
    return 1 + x0 * e**2 + x1 * e**3 + (x2 + x0**2 / 2) * e**4

EBp = Ep(-P**2 / 6, 2 * Z, -R(7, 180) * P**4)
KaL = (3 + P**2 / 6 - 2 * Z) * e**2 + (6 - R(7, 3) * P**2 - Z + R(5, 36) * P**4) * e**3
KabL = (R(2, 3) * P**2 - P**4 / 18 - 2 * Z) * e**2
G0L = (-R(1, 2) + (P**2 / 2 - 5) * e + (R(2, 3) * P**2 + 18 * Z - 28) * e**2
       + (R(143, 120) * P**4 - R(11, 6) * P**2 + 27 * Z - 127) * e**3)
K2L = (-5 - P**2 + 12 * Z) * e + (R(121, 60) * P**4 - 10 * P**2 - 38 * Z - 49) * e**2
RL = (-1 + (P**2 - 10) * e + (R(5, 6) * P**2 + 44 * Z - 55) * e**2
      + (R(401, 90) * P**4 - R(47, 3) * P**2 + 6 * Z - 285) * e**3)

X = sp.expand(2 * KaL + e * KabL + (1 - e) * (2 * EBp * G0L + e * K2L) - (1 - e) * RL)
assert all(sp.simplify(X.coeff(e, k)) == 0 for k in range(4))
W = sp.expand(sp.cancel(X / e**4))
for k in range(5):
    print('W coeff e^%d:' % k, W.coeff(e, k))
