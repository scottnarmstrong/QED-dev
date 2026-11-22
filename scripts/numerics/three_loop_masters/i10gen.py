# Provenance: scripts/numerics/three_loop_masters/i10gen.py (sympy).
# I10: the expansion of the remainder Rest = e (T - Closed) forced by the LR96 table, and the
# polynomial data of QED/ThreeLoopE/SetEMastersI10Wire.lean. In SetEMastersI10Def.lean,
#   I10 C^-1 = Gam(3e-1)/Gam(1+e)^3 * T,   T = Closed + Rest/e,
#   Closed = (S0 + 2 Ca + Cab)/(1 - e)   (Gamma functions only).
# With A, B, C, D = Gam(1+e), Gam(1-e), Gam(1+2e), Gam(1+3e):
#   B(e-1, e-1) = A^2/C * 4(2e-1)/(e(e-1)),   B(2e, e-1) = A C/D * 3(3e-1)/(2e(e-1)),
#   B(e, 1+e) = A^2/(e C),   B(2e, 1+e) = A C/(2 e D),   Gam(e) Gam(1-e) = A B/e,
#   Gam(3e-1) = D/(3e(3e-1)).
# Then e^3 Den I10 C^-1 = sum_i P_i E_i + P_5 E_5 Rest with the balanced Gamma ratios
#   E1 = D/(A C), E2 = C/A^2, E3 = B D/C, E4 = B C/A, E5 = D/A^3,
# each exp(e^2 (x0 + x1 e + x2 e^2) + e^5 Y). Run: python3 i10gen.py [--lean]
import sys
import sympy as sp

e = sp.symbols('e')
pi, z3, z5 = sp.symbols('pi zeta3 zeta5')
A, B, C, D, Rs = sp.symbols('A B C D Rest')

# --- the master as a combination of Gamma ratios -------------------------------------------
B11 = A ** 2 / C * 4 * (2 * e - 1) / (e * (e - 1))
B21 = A * C / D * 3 * (3 * e - 1) / (2 * e * (e - 1))
Be = A ** 2 / (e * C)
B2e = A * C / (2 * e * D)
a2 = A * B / e - 1 / e
S0 = (B11 - 2 * B21) / (e * (1 + e))
Ca = Be * (1 / (1 - e) + a2) - B2e * (A * B - 1 / (1 + e)) / e
Cab = 2 * Be * e / (1 - e) * a2
closed = (S0 + 2 * Ca + Cab) / (1 - e)
pref = D / (A ** 3 * 3 * e * (3 * e - 1))
master = sp.expand(pref * closed + pref * Rs / e)

E = {1: D / (A * C), 2: C / A ** 2, 3: B * D / C, 4: B * C / A, 5: D / A ** 3 * Rs}
Es = sp.symbols('E1:6')
# collect: substitute monomials
coef = {}
rest_expr = master
for i in [5, 3, 4, 1, 2]:
    pass
terms = sp.Add.make_args(master)
groups = {i: 0 for i in E}
for t in terms:
    found = False
    for i, m in E.items():
        q = sp.simplify(t / m)
        if not q.has(A) and not q.has(B) and not q.has(C) and not q.has(D) and not q.has(Rs):
            groups[i] += q
            found = True
            break
    assert found, t
groups = {i: sp.factor(sp.together(v)) for i, v in groups.items()}
den = sp.lcm([sp.denom(v) for v in groups.values()])
den = sp.factor(den)
# normalize: Den = den / e^3 (we want e^3 Den master = sum P_i E_i)
P = {i: sp.factor(sp.cancel(v * den)) for i, v in groups.items()}

# --- the Gamma ratios as exponentials --------------------------------------------------------
zeta = {2: pi ** 2 / 6, 3: z3, 4: pi ** 4 / 90, 5: z5}
SIG = {1: {3: 1, 1: -1, 2: -1}, 2: {2: 1, 1: -2}, 3: {-1: 1, 3: 1, 2: -1},
       4: {-1: 1, 2: 1, 1: -1}, 5: {3: 1, 1: -3}}

def mom(i, k):
    return sum(s * a ** k for a, s in SIG[i].items())

def xs(i):
    # log Gam(1 + z) = -gamma z + pi^2/12 z^2 - zeta3/3 z^3 + pi^4/360 z^4 - zeta5/5 z^5 + ...
    assert mom(i, 1) == 0
    return (pi ** 2 / 12 * mom(i, 2), -z3 / 3 * mom(i, 3), pi ** 4 / 360 * mom(i, 4))

def ep(i):
    x0, x1, x2 = xs(i)
    return 1 + x0 * e ** 2 + x1 * e ** 3 + (x2 + x0 ** 2 / 2) * e ** 4

L = (-sp.Rational(1, 3) / e ** 3 - sp.Rational(5, 3) / e ** 2 + (-2 * pi ** 2 / 3 - 4) / e
     + (-sp.Rational(26, 3) * z3 - sp.Rational(7, 3) * pi ** 2 + sp.Rational(10, 3))
     + (-sp.Rational(35, 18) * pi ** 4 - sp.Rational(94, 3) * z3 - pi ** 2
        + sp.Rational(302, 3)) * e)

r0, r1, r2, r3 = sp.symbols('r0:4')
RL = r0 + r1 * e + r2 * e ** 2 + r3 * e ** 3
num = sp.expand(sum(P[i] * ep(i) for i in range(1, 5)) + P[5] * ep(5) * RL
                - sp.expand(den * L))
sol = sp.solve([num.coeff(e, k) for k in range(5)], [r0, r1, r2, r3, ], dict=True)
# the e^0 equation must hold identically; r's from e^1..e^4
assert len(sol) == 1, sol
sol = {k: sp.expand(v) for k, v in sol[0].items()}
wire = sp.expand(num.subs(sol))
for k in range(5):
    assert sp.simplify(wire.coeff(e, k)) == 0, k
wireP = sp.expand(sp.cancel(wire / e ** 5))

if __name__ == '__main__':
    print('Den =', den)
    for i in range(1, 6):
        print('P%d =' % i, P[i])
        print('  x =', xs(i), ' m5 =', mom(i, 5))
    for k in range(4):
        v = sol[[r0, r1, r2, r3][k]]
        print('r%d =' % k, v, '=', sp.N(v.subs({pi: sp.pi, z3: sp.zeta(3), z5: sp.zeta(5)}), 20))
    print('wireP degree', sp.degree(wireP, e))
    if '--lean' in sys.argv:
        print(sp.Poly(wireP, e).all_coeffs()[::-1])


def lean(expr):
    """Lean text of a polynomial in pi, zeta3 with rational coefficients."""
    expr = sp.expand(expr)
    poly = sp.Poly(expr, pi, z3)
    out = []
    for (i, j), cf in sorted(poly.terms(), reverse=True):
        mon = []
        if i: mon.append('(π : ℂ) ^ %d' % i if i > 1 else '(π : ℂ)')
        if j: mon.append('(zeta3 : ℂ) ^ %d' % j if j > 1 else '(zeta3 : ℂ)')
        cf = sp.Rational(cf)
        sgn = '-' if cf < 0 else '+'
        a = abs(cf)
        cs = str(a.p) if a.q == 1 else '%d / %d' % (a.p, a.q)
        if mon:
            body = ' * '.join(mon) if a == 1 else cs + ' * ' + ' * '.join(mon)
        else:
            body = cs
        out.append((sgn, body))
    s = ('-' if out[0][0] == '-' else '') + out[0][1]
    for sgn, body in out[1:]:
        s += ' %s %s' % (sgn, body)
    return s

if '--lean' in sys.argv:
    cs = sp.Poly(wireP, e).all_coeffs()[::-1]
    for k, cf in enumerate(cs):
        print('WP%d:' % k, lean(cf))
    L3 = sp.expand(e ** 3 * L)
    for k in range(5):
        print('L3e%d:' % k, lean(L3.coeff(e, k)))
