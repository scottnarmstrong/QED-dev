#!/usr/bin/env python3
"""The outer integrations of the crossed-ladder unit (section 4.2 of docs/TWO-LOOP-UNITS.md).
NOT a proof by itself: generates QED/TwoLoop/UnitXCloseOuter.lean, whose identities Lean checks.

In the hierarchical variables b = z_A + z2 zb, w = z_a + z2 z3, U = b + w, Y = z2 + z3,
zb = 1 - Y, the massless merged integrand crossedTerm 0 0 of QED/TwoLoop/UnitXGraphReduce.lean is
    T = z2 (P1 - P2 Et)/(2 U^4 Et^2),   Et = Y^2 U + b^2,
P1, P2 = Psi1(z_M/2), Psi2(z_M/2) as polynomials in (z2, z3, b, w). Steps:
 1. partial fractions in U:  T = a1/U + a2/U^2 + a3/U^3 + a4/U^4 + beta2/Et^2 - a1 Y^2/Et
    (the residues at U = 0 and Et = 0 cancel); the z_a-antiderivative vanishing at infinity is
    -a2/U - a3/(2U^2) - a4/(3U^3) - beta2/(Y^2 Et) + a1 log(Y^2 U/Et);
 2. at w = e = z2 z3 (z_a = 0), Et = (b + p)(b + q), p = Y z2, q = Y z3, so
    F1(b) = a2/(b+e) + a3/(2(b+e)^2) + a4/(3(b+e)^3) + beta2/(Y^2 (b+p)(b+q)) - a1 L,
    L = 2 log Y + log(b+e) - log(b+p) - log(b+q);
 3. a1 = -sum_{k=2..5} r_k/b^k, and the z_A-antiderivative vanishing at infinity is
    K = Q + S L + ke log(b+e) + kp log(b+p) + kq log(b+q),  S = sum -r_k/((k-1) b^(k-1)),
    Q = -c20/b - c30/(2b^2) - c2e/(b+e) - c3e/(2(b+e)^2),  ke + kp + kq = 0;
 4. Phi_X(z2, z3) = -K(g), g = z2 zb; checked against crossed_Phi of ../two_loop_unit_integrals.py.
Run: nice -n 10 python3 outer_integrals.py > ../../../QED/TwoLoop/UnitXCloseOuter.lean  (~10 s)
"""
import os, re, sys
import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
_src = open(os.path.join(HERE, 'target_check.py')).read()
exec(_src[_src.index('def lean_data'):_src.index("print('1.")])   # lean_data, psi1, psi2, Psi

A, M, c, a, b = sp.symbols('A M c a b', positive=True)
B, W, U = sp.symbols('B W U', positive=True)
Y = M + c; zb = 1 - Y; g = M*zb; e = M*c; p = Y*M; q = Y*c
_, P1, P2 = Psi(A, M/2, M, c, a, b)
sub = {b: zb, A: B - g, a: W - e}
P1h = sp.expand(sp.expand(P1).subs(sub)); P2h = sp.expand(sp.expand(P2).subs(sub))
Et = Y**2*U + B**2
# 1. partial fractions in U
Nn = sp.expand(M*(P1h - P2h*(Y**2*(B + W) + B**2)).subs(W, U - B)/2)       # T = Nn/(U^4 Et^2)
ser = sp.expand(sp.series(Nn/Et**2, U, 0, 4).removeO())
al = {k: sp.factor(ser.coeff(U, 4 - k)) for k in range(1, 5)}
U0 = -B**2/Y**2
g0 = sp.together(Nn/U**4/Y**4)                                             # T = g0/(U - U0)^2
be2 = sp.factor(Y**4*g0.subs(U, U0))
be1 = sp.factor(sp.diff(g0, U).subs(U, U0))
assert sp.cancel(al[1] + be1) == 0
pf = sum(al[k]/U**k for k in al) + be2/Et**2 - al[1]*Y**2/Et
pt = {M: sp.Rational(1, 5), c: sp.Rational(2, 7), B: sp.Rational(3, 7), U: sp.Rational(5, 3)}
assert sp.cancel((pf - Nn/(U**4*Et**2)).subs(pt)) == 0
# 2.-3. the z_A-integration
Ete = (B + p)*(B + q)
assert sp.expand(Ete - (Y**2*(B + e) + B**2)) == 0
R0 = al[2]/(B + e) + al[3]/(2*(B + e)**2) + al[4]/(3*(B + e)**3) + be2/(Y**2*Ete)
R1e = sp.expand(sp.cancel(-al[1]*B**5))
r = {k: sp.factor(R1e.coeff(B, 5 - k)) for k in range(0, 6)}
assert r[0] == 0 and r[1] == 0
S = sum(-r[k]/((k - 1)*B**(k - 1)) for k in range(2, 6))
Lp = 1/(B + e) - 1/(B + p) - 1/(B + q)
Rr = sp.together(R0 - S*Lp)
num, den = sp.fraction(sp.factor(Rr))
dfac = sp.factor(den)
kap = {}
for nm, d, mult in (('0', 0, 3), ('e', e, 3), ('p', p, 1), ('q', q, 1)):
    h = num/sp.cancel(dfac/(B + d)**mult)
    if mult > 1:
        h = sp.diff(h, B, mult - 1)/sp.factorial(mult - 1)
    kap[nm] = sp.factor(sp.cancel(sp.together(h.subs(B, -d))))
assert kap['0'] == 0 and sp.cancel(kap['e'] + kap['p'] + kap['q']) == 0
cc = {}
for nm, d in (('0', 0), ('e', e)):
    h = num/sp.cancel(dfac/(B + d)**3)
    cc['3' + nm] = sp.factor(sp.cancel(sp.together(h.subs(B, -d))))
    cc['2' + nm] = sp.factor(sp.cancel(sp.together(sp.diff(h, B).subs(B, -d))))
Q = -cc['20']/B - cc['30']/(2*B**2) - cc['2e']/(B + e) - cc['3e']/(2*(B + e)**2)
L = 2*sp.log(Y) + sp.log(B + e) - sp.log(B + p) - sp.log(B + q)
K = Q + S*L + kap['e']*sp.log(B + e) + kap['p']*sp.log(B + p) + kap['q']*sp.log(B + q)
F1 = R0 - al[1]*L
ptB = {M: sp.Rational(1, 5), c: sp.Rational(2, 7)}
for Bv in (sp.Rational(3, 7), sp.Rational(11, 3)):
    assert abs(sp.N((sp.diff(K, B) - F1).subs(ptB).subs(B, Bv), 40)) < 1e-35
Phi = -K.subs(B, g)
print('-- Phi(0.2, 0.3) =', sp.N(Phi.subs({M: sp.Rational(1, 5), c: sp.Rational(3, 10)}), 25),
      '(crossed_Phi of two_loop_unit_integrals.py: -0.164669212281415263775591295416)', file=sys.stderr)

# ------------------------------------------------------------------ Lean output


def lean_poly(P, gens, width=94, indent='    '):
    P = sp.Poly(sp.expand(P), *gens)
    terms = []
    for mon, co in zip(P.monoms(), P.coeffs()):
        co = sp.Rational(co)
        m = ' * '.join(f'{gg} ^ {k}' if k > 1 else str(gg) for gg, k in zip(gens, mon) if k > 0)
        ca = abs(co); cs = f'{ca.p}' if ca.q == 1 else f'({ca.p} / {ca.q})'
        body = cs if m == '' else (m if ca == 1 else f'{cs} * {m}')
        terms.append(('-' if co < 0 else '+', body))
    if not terms:
        return '0'
    out, line = [], ('-' if terms[0][0] == '-' else '') + terms[0][1]
    for sg, body in terms[1:]:
        if len(line) + len(body) + 3 > width:
            out.append(line + f' {sg}'); line = indent + body
        else:
            line += f' {sg} {body}'
    out.append(line)
    return '\n'.join(out)


def lean_factor(D, gens):
    c0, fl = sp.factor_list(D)
    parts = [] if c0 == 1 else [str(c0)]
    for f, k in fl:
        fs = lean_poly(f, gens, 1000)
        fs = f'({fs})' if len(sp.Add.make_args(sp.expand(f))) > 1 else fs
        parts.append(f'{fs} ^ {k}' if k > 1 else fs)
    return ' * '.join(parts) if parts else '1'


def binders(gens, used):
    return ' '.join(str(gg) if gg in used else f'_{gg}' for gg in gens)


def poly_def(name, gens, P, doc, CH=24):
    P = sp.Poly(sp.expand(P), *gens)
    ts = [sp.Rational(co)*sp.prod([gg**k for gg, k in zip(gens, mon)]) for mon, co in zip(P.monoms(), P.coeffs())]
    argn = ' '.join(map(str, gens))
    if len(ts) <= CH:
        body = sum(ts)
        return [f'/-- {doc} -/\nnoncomputable def {name} ({binders(gens, body.free_symbols)} : ℝ) : ℝ :=\n  '
                + lean_poly(body, gens) + '\n'], [name]
    out, parts = [], []
    for k in range(0, len(ts), CH):
        nm = f'{name}_{k//CH}'; parts.append(nm); body = sum(ts[k:k+CH])
        out.append(f'/-- Part {k//CH} of `{name}`. -/\nnoncomputable def {nm} ({binders(gens, body.free_symbols)} : ℝ) : ℝ :=\n  '
                   + lean_poly(body, gens) + '\n')
    sm = ' +\n    '.join(f'{pp} {argn}' for pp in parts)
    out.append(f'/-- {doc} -/\nnoncomputable def {name} ({argn} : ℝ) : ℝ :=\n  {sm}\n')
    return out, parts + [name]


def rat_def(name, gens, R, doc):
    nu, de = sp.fraction(sp.factor(sp.together(R)))
    o, names = poly_def(name + 'N', gens, nu, f'The numerator of `{name}`.')
    argN = ' '.join(map(str, gens))
    o.append(f'/-- {doc} -/\nnoncomputable def {name} ({argN} : ℝ) : ℝ :=\n  '
             f'{name}N {argN} / ({lean_factor(de, gens)})\n')
    return o, names + [name]


defs, unf = [], {}
for nm, P, doc in (('crossedP1h', P1h, '`Ψ₁(z_M/2)` in the hierarchical variables `b = z_A + z₂ z_b`, `w = z_a + z₂ z₃`.'),
                   ('crossedP2h', P2h, '`Ψ₂(z_M/2)` in the hierarchical variables.')):
    o, n_ = poly_def(nm, (M, c, B, W), P, doc); defs += o; unf[nm] = n_
sub_ = '₀₁₂₃₄₅'
for k in (1, 2, 3, 4):
    o, n_ = rat_def(f'xα{sub_[k]}', (M, c, B), al[k], f'The coefficient of `U^-{k}` in the partial fractions of the `z_a`-integrand.')
    defs += o; unf[f'xα{sub_[k]}'] = n_
o, n_ = rat_def('xβ₂', (M, c, B), be2, 'The coefficient of `Ẽ^-2` in the partial fractions of the `z_a`-integrand.')
defs += o; unf['xβ₂'] = n_
for k in (2, 3, 4, 5):
    o, n_ = rat_def(f'xr{sub_[k]}', (M, c), r[k], f'The coefficient of `b^-{k}` in `-α₁`.')
    defs += o; unf[f'xr{sub_[k]}'] = n_
for nm, key, doc in (('xc₂₀', '20', '`b⁻²`'), ('xc₃₀', '30', '`b⁻³`'), ('xc₂ₑ', '2e', '`(b + e)⁻²`'),
                     ('xc₃ₑ', '3e', '`(b + e)⁻³`')):
    o, n_ = rat_def(nm, (M, c), cc[key], f'The coefficient of {doc} in `Q\'`.')
    defs += o; unf[nm] = n_
for nm, key in (('xκe', 'e'), ('xκp', 'p'), ('xκq', 'q')):
    o, n_ = rat_def(nm, (M, c), kap[key], f'The coefficient of `log (b + d)` in the `z_A`-antiderivative, `d = {key}`.')
    defs += o; unf[nm] = n_


def wrap_list(items, first, indent='    ', close=']'):
    out, line = [], first
    for k, it in enumerate(items):
        piece = it + (',' if k < len(items) - 1 else close)
        if len(line) + len(piece) + 1 > 100:
            out.append(line.rstrip()); line = indent
        line += piece + ' '
    out.append(line.rstrip())
    return '\n'.join(out)


def U_(*names):
    return [x for nm in names for x in unf[nm]]


HDR = '''/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXCloseInnerPrim
public import QED.TwoLoop.UnitXGraphReduceChengWu
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The outer integrations of the crossed ladder: explicit functions and their identities

Section 4.2 of `docs/TWO-LOOP-UNITS.md`. Generated by
`scripts/numerics/crossed_graph/outer_integrals.py` (exact arithmetic, sympy); every identity is
checked here by `field_simp` and `ring`. In the hierarchical variables `b = z_A + z₂ z_b`,
`w = z_a + z₂ z₃`, `U = b + w`, `Y = z₂ + z₃`, `z_b = 1 - Y`:

* `crossedTerm_zero_hier`: `T(0, 0) = z₂ (Ψ₁ - Ψ₂ Ẽ)/(2 U⁴ Ẽ²)`, `Ẽ = Y² U + b²`, with
  `Ψ₁ = crossedP1h`, `Ψ₂ = crossedP2h` polynomials in `(z₂, z₃, b, w)`;
* `crossedPF`: in `U`, `T(0, 0) = α₁/U + α₂/U² + α₃/U³ + α₄/U⁴ + β₂/Ẽ² - α₁ Y²/Ẽ`
  (`outerPF`), so the `z_a`-antiderivative is `outerPrim`;
* `xα₁_eq`: `α₁ = -∑_{k=2}^{5} r_k/b^k` (`xr₂ … xr₅`), so `S = ∑ -r_k/((k-1) b^{k-1})` has
  `S' = -α₁`;
* `crossedKRat`: the rational part of the derivative of the `z_A`-antiderivative
  `K = Q + S L + κ_e log (b + e) + κ_p log (b + p) + κ_q log (b + q)`
  (`e = z₂ z₃`, `p = Y z₂`, `q = Y z₃`, `L = 2 log Y + log (b + e) - log (b + p) - log (b + q)`);
* `xκ_sum`: `κ_e + κ_p + κ_q = 0`.
-/

@[expose] public section

namespace QED.TwoLoop.UnitXClose

open QED.TwoLoop.UnitXGraph
'''
P1u = U_('crossedP1h'); P2u = U_('crossedP2h')
TH = f'''
theorem gPsi1_hier (A M c a : ℝ) :
    gPsi1 A (M / 2) M c a (1 - M - c) = crossedP1h M c (A + M * (1 - M - c)) (a + M * c) := by
{wrap_list(['gPsi1', 'psiT1h', 'gXan', 'gXbn', 'gXU', 'Matrix.cons_val'] + P1u, '  simp only [')}
  ring

theorem gPsi2_hier (A M c a : ℝ) :
    gPsi2 A (M / 2) M c a (1 - M - c) = crossedP2h M c (A + M * (1 - M - c)) (a + M * c) := by
{wrap_list(['gPsi2', 'psiT2h', 'gXan', 'gXbn', 'gXU', 'Matrix.cons_val'] + P2u, '  simp only [')}
  ring

theorem gXEn_hier (A M c a : ℝ) :
    gXEn A M c a (1 - M - c) = (M + c) ^ 2 * ((A + M * (1 - M - c)) + (a + M * c)) +
      (A + M * (1 - M - c)) ^ 2 := by
  unfold gXEn; ring

/-- **The massless integrand in the hierarchical variables.** -/
theorem crossedTerm_zero_hier {{A M c a : ℝ}} (hA : 0 < A) (hM : 0 < M) (hc : 0 < c) (ha : 0 < a)
    (hb : 0 < 1 - M - c) :
    crossedTerm 0 0 A M c a (1 - M - c) =
      M * (crossedP1h M c (A + M * (1 - M - c)) (a + M * c) -
          crossedP2h M c (A + M * (1 - M - c)) (a + M * c) *
            ((M + c) ^ 2 * ((A + M * (1 - M - c)) + (a + M * c)) + (A + M * (1 - M - c)) ^ 2)) /
        (2 * ((A + M * (1 - M - c)) + (a + M * c)) ^ 4 *
          ((M + c) ^ 2 * ((A + M * (1 - M - c)) + (a + M * c)) +
            (A + M * (1 - M - c)) ^ 2) ^ 2) := by
  have hU := gXU_pos hA hM hc ha hb
  have hEn : 0 < gXEn A M c a (1 - M - c) := by unfold gXEn; positivity
  unfold crossedTerm gXE
  rw [gPsi1_hier, gPsi2_hier, ← gXEn_hier, ← gXU_frame]
  field_simp
  ring

/-- **The partial fractions in `U`.** -/
theorem crossedPF {{M c B U : ℝ}} (hB : 0 < B) (hU : 0 < U) (hY : 0 < M + c) :
    M * (crossedP1h M c B (U - B) - crossedP2h M c B (U - B) * ((M + c) ^ 2 * U + B ^ 2)) /
        (2 * U ^ 4 * ((M + c) ^ 2 * U + B ^ 2) ^ 2) =
      outerPF (M + c) B (xα₁ M c B) (xα₂ M c B) (xα₃ M c B) (xα₄ M c B) (xβ₂ M c B) U := by
  have hE : 0 < (M + c) ^ 2 * U + B ^ 2 := by positivity
{wrap_list(['outerPF'] + U_('xα₁', 'xα₂', 'xα₃', 'xα₄', 'xβ₂') + P1u + P2u, '  simp only [')}
  field_simp
  ring

/-- `α₁ = -∑_{{k=2}}^{{5}} r_k/b^k`. -/
theorem xα₁_eq {{M c B : ℝ}} (hB : B ≠ 0) :
    xα₁ M c B = -(xr₂ M c / B ^ 2 + xr₃ M c / B ^ 3 + xr₄ M c / B ^ 4 + xr₅ M c / B ^ 5) := by
{wrap_list(U_('xα₁', 'xr₂', 'xr₃', 'xr₄', 'xr₅'), '  simp only [')}
  field_simp
  ring

/-- `κ_e + κ_p + κ_q = 0`. -/
theorem xκ_sum {{M c : ℝ}} (hM : 0 < M) (hc : 0 < c) (hMc : M ≠ c) :
    xκe M c + xκp M c + xκq M c = 0 := by
  have h1 : -M + c ≠ 0 := by intro h; apply hMc; linarith
  have h2 : M - c ≠ 0 := sub_ne_zero.mpr hMc
{wrap_list(U_('xκe', 'xκp', 'xκq'), '  simp only [')}
  field_simp
  ring

/-- **The rational part of the derivative of the `z_A`-antiderivative**:
`Q' + S L' + ∑ κ_d/(b + d) = α₂/(b+e) + α₃/(2(b+e)²) + α₄/(3(b+e)³) + β₂/(Y²(b+p)(b+q))`, with
`Q = -c₂₀/b - c₃₀/(2b²) - c₂ₑ/(b+e) - c₃ₑ/(2(b+e)²)`, `S = ∑ -r_k/((k-1) b^{{k-1}})` and
`L' = 1/(b+e) - 1/(b+p) - 1/(b+q)`. -/
theorem crossedKRat {{M c B : ℝ}} (hM : 0 < M) (hc : 0 < c) (hMc : M ≠ c) (hB : 0 < B) :
    (xc₂₀ M c / B ^ 2 + xc₃₀ M c / B ^ 3 + xc₂ₑ M c / (B + M * c) ^ 2 +
        xc₃ₑ M c / (B + M * c) ^ 3) +
      (-(xr₂ M c / B) - xr₃ M c / (2 * B ^ 2) - xr₄ M c / (3 * B ^ 3) - xr₅ M c / (4 * B ^ 4)) *
        (1 / (B + M * c) - 1 / (B + (M + c) * M) - 1 / (B + (M + c) * c)) +
      (xκe M c / (B + M * c) + xκp M c / (B + (M + c) * M) + xκq M c / (B + (M + c) * c)) =
    xα₂ M c B / (B + M * c) + xα₃ M c B / (2 * (B + M * c) ^ 2) +
      xα₄ M c B / (3 * (B + M * c) ^ 3) +
      xβ₂ M c B / ((M + c) ^ 2 * ((B + (M + c) * M) * (B + (M + c) * c))) := by
  have h1 : -M + c ≠ 0 := by intro h; apply hMc; linarith
  have h2 : M - c ≠ 0 := sub_ne_zero.mpr hMc
  have h3 : 0 < B + M * c := by positivity
  have h4 : 0 < B + (M + c) * M := by positivity
  have h5 : 0 < B + (M + c) * c := by positivity
{wrap_list(U_('xα₂', 'xα₃', 'xα₄', 'xβ₂', 'xr₂', 'xr₃', 'xr₄', 'xr₅', 'xc₂₀', 'xc₃₀', 'xc₂ₑ', 'xc₃ₑ', 'xκe', 'xκp', 'xκq'), '  simp only [')}
  field_simp
  ring

end QED.TwoLoop.UnitXClose

end'''
print(HDR + '\n' + '\n'.join(defs) + TH)
# numerical checks (stderr): Phi_X against crossed_Phi, and the xi-integral against K_X of eq. (4.7)
import mpmath as mp
mp.mp.dps = 50
fPhi = sp.lambdify((M, c), Phi, 'mpmath')
print('-- Phi(0.1, 0.6) =', mp.nstr(fPhi(mp.mpf('0.1'), mp.mpf('0.6')), 25),
      '(crossed_Phi: 0.0581976045104991063881841855417)', file=sys.stderr)


def KX(y):
    """K_X of eq. (4.7) (QED.TwoLoop.Units.crossedKernel)."""
    L2, z2 = mp.polylog(2, y), mp.pi**2/6
    D = mp.polylog(2, 1 - 2*y) - mp.polylog(2, 2*y - 1)
    a_, b_ = mp.log(y), mp.log(1 - y)
    rho = 5/(6*(y-1)) - mp.mpf(3)/(4*(y-1)**2) - mp.mpf(8)/(3*(y-1)**3) - 1/(y-1)**4
    return ((-mp.mpf(5)/2*y - mp.mpf(5)/4 + 2*rho + 5/(6*y) - 7/(12*y**2))*L2
            + (-mp.mpf(7)/6*y - mp.mpf(11)/12 + rho + 5/(6*y) - 1/(12*y**2))*D
            + (y/12 - mp.mpf(7)/24 + rho/2)*a_**2
            + (-mp.mpf(4)/3*y - mp.mpf(1)/3 + 5/(6*y) - 7/(12*y**2))*a_*b_
            + (-mp.mpf(11)/12*y - mp.mpf(5)/4 - 1/(8*(2*y-1)) + 11/(12*(y-1)) - 2/(3*(y-1)**2)
               - 1/(y-1)**3 - 5/(12*y))*a_
            + (mp.mpf(11)/12*y - mp.mpf(13)/12 + 1/(8*(2*y-1)) - 2/(3*(y-1)) - 1/(y-1)**2
               + 7/(6*y) - 1/(24*y**2))*b_
            + (mp.mpf(23)/12*y + mp.mpf(19)/24 - rho/2 - 5/(4*y) + 1/(8*y**2))*z2
            + (-mp.mpf(17)/12*y + mp.mpf(1)/24 + 2/(3*(y-1)) + 1/(y-1)**2 + 3/(8*y)))


for yv in ('0.3', '0.7'):
    y = mp.mpf(yv)
    def fx(x):   # Phi_X has cancelling poles at xi = 0, 1/2, 1: raise the precision there
        d = int(-mp.log10(min(x, 1 - x, abs(x - mp.mpf(1)/2)))) + 1
        with mp.workdps(50 + 6*max(d, 0)):
            return y*fPhi(y*x, y*(1 - x))
    v = mp.quad(fx, [0, 0.25, 0.5, 0.75, 1])
    print(f'-- Y = {yv}: int_0^1 Y Phi_X(Y xi, Y(1 - xi)) dxi = {mp.nstr(v, 25)},  K_X(Y) = {mp.nstr(KX(y), 25)},'
          f'  difference {mp.nstr(v - KX(y), 3)}', file=sys.stderr)
