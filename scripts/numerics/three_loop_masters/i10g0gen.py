# Provenance: scripts/numerics/three_loop_masters/i10g0gen.py (system python3 with sympy, mpmath).
# I10, the face integral G0 of QED/ThreeLoopE/SetEMastersI10Def.lean: closed form
#   e (1 - e) G0 = N = G(1 + e) (G(1 - e)^2 G(3 - 5e) / (G(2 - 2e) G(3 - 4e)) - G(1 - e)/(1 - e))
# (QED/ThreeLoopE/SetEMastersI10G0Cl.lean, QED/ThreeLoopE/SetEMastersI10G0.lean).
# 1. Checks the Laurent coefficients of G0 against the closed form (mpmath, Cauchy integral).
# 2. Writes N D = E_a (E_b q1 - q2) with the exp truncations E_p of the balanced Gamma ratios
#    E_a = G(1 + e) G(1 - e), E_b = G(1 - e) G(1 - 5e) / (G(1 - 2e) G(1 - 4e)) and prints the
#    polynomial i10G0W = (P_a (P_b q1 - q2) - e (1 - e) L D) / e^5 of i10G0_key (P = pi, Z = zeta3).
# Run: python3 i10g0gen.py
import sympy as sp
import mpmath as mm

e, P, Z = sp.symbols('e P Z')
L = (-sp.Rational(1, 2) + (P**2 / 2 - 5) * e + (sp.Rational(2, 3) * P**2 + 18 * Z - 28) * e**2
     + (sp.Rational(143, 120) * P**4 - sp.Rational(11, 6) * P**2 + 27 * Z - 127) * e**3)

def check():
    mm.mp.dps = 40
    B = lambda a, b: mm.gamma(a) * mm.gamma(b) / mm.gamma(a + b)
    g0 = lambda x: (B(1 - x, 1 - x) * B(x, 3 - 5 * x) - B(x, 1 - x) / (1 - x)) / (1 - x)
    c = mm.taylor(lambda x: g0(x) if x != 0 else g0(mm.mpf(10)**-30), 0, 3,
                  method='quad', radius=mm.mpf(1) / 10)
    for k in range(4):
        ex = L.coeff(e, k)
        val = mm.mpf(sp.N(ex.subs({P: sp.pi, Z: sp.zeta(3)}), 40))
        print('G0 coeff', k, mm.nstr(c[k], 25), 'diff', mm.nstr(abs(c[k] - val), 3))

def Ep(x0, x1, x2):
    return 1 + x0 * e**2 + x1 * e**3 + (x2 + x0**2 / 2) * e**4

def wire():
    Pa = Ep(P**2 / 6, 0, P**4 / 180)
    Pb = Ep(P**2 / 2, 18 * Z, sp.Rational(59, 60) * P**4)
    q1 = (2 - 5 * e) * (1 - 5 * e) * (1 - e)
    q2 = (1 - 2 * e) * (2 - 4 * e) * (1 - 4 * e)
    X = sp.expand(Pa * (Pb * q1 - q2) - e * (1 - e) * L * q2 * (1 - e))
    assert all(sp.simplify(X.coeff(e, k)) == 0 for k in range(5))
    W = sp.expand(sp.cancel(X / e**5))
    for k in range(7):
        print('W coeff e^%d:' % k, W.coeff(e, k))

if __name__ == '__main__':
    check()
    wire()
