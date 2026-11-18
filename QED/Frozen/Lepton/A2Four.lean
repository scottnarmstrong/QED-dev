/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace QED.Lepton

/-- (U₃) **The mass-dependent fourth-order coefficient** of the electron's anomalous magnetic
moment from one heavy lepton (decision D-49.1, D-49.3; plan section 3(c), O3-M3): the
coefficient `A₂⁽⁴⁾(y)` of `(α/π)²`, `α = e²/(4π)`, in `F₂(0)` from the vacuum-polarization
insertion of a lepton of mass `m_ℓ` in the one-loop vertex of the electron, as a function of the
mass ratio `y = m_e/m_ℓ` (AKN Table 1 convention), source-facing for `0 < y < 1`:

`A₂⁽⁴⁾(y) = -25/36 + (ln y)/3 + (4 - 3 ln y)/y²`
`  + (y² - 5)/(2y³) · [ln y · ln((1 - y)/(1 + y)) + Li₂(y) - Li₂(-y)]`
`  + [2 ln y · ln(1 - y²) + Li₂(y²)]/y⁴`,

with `Li₂(z) = ∑_{n ≥ 1} zⁿ/n²` (the series of `QED.Polylog.Li₂`, convergent for `|z| ≤ 1`; all
three arguments lie in `(-1, 1)`). This is Passera (2007) eq. (10), p. 2 (exact result after
Elend 1966), `A₂⁽⁴⁾(1/x)` at `x = m_ℓ/m_e = 1/y > 1` with real parts taken, rewritten term by
term: `ln x = -ln y`; `Re ln((1 - x)/(1 + x)) = ln((1 - y)/(1 + y))`;
`Re ln(1/x - x) = ln(1 - y²) - ln y`; and the inversion formulas
`Re Li₂(z) = π²/3 - ½ ln² z - Li₂(1/z)` for `z > 1` (applied at `z = x`, `x²`) and
`Li₂(-z) = -π²/6 - ½ ln² z - Li₂(-1/z)` for `z > 0` (at `z = x`); the constants `π²` cancel.
The three groups are Passera's three groups: `-25/36 - (ln x)/3 + x²(4 + 3 ln x)`,
`(x/2)(1 - 5x²)[⋯]` and `x⁴[⋯]`. Numerically (evidence, `scripts/numerics/phase5_chains.py`,
section B): at `y = 4.83633167 × 10⁻³` (Passera (3)) the value is `5.197 386 697 × 10⁻⁷`, Passera
(11) `5.197 386 70(28) × 10⁻⁷`; at `y = 2.87564 × 10⁻⁴` (Passera (4)) `1.837 622 6 × 10⁻⁹`,
Passera (12) `1.837 62(60) × 10⁻⁹`; also AHKN (2.6)–(2.7) and AKN Table 1 at their own ratios;
it agrees with the direct evaluation of (10) to `10⁻⁴⁵` relative and with the spectral integral to
`10⁻²⁹`. As `y → 1⁻` it tends to `119/36 - π²/3`, the electron's own vacuum-polarization part of
`A₁⁽⁴⁾` (Passera p. 2, after (10); theorem (U₃′)). Outside `(0, 1)` the expression is not
source-facing. -/
noncomputable def a2Four (y : ℝ) : ℝ :=
  -25 / 36 + Real.log y / 3 + (4 - 3 * Real.log y) / y ^ 2 +
    (y ^ 2 - 5) / (2 * y ^ 3) *
      (Real.log y * Real.log ((1 - y) / (1 + y)) +
        ∑' n : ℕ, y ^ (n + 1) / ((n : ℝ) + 1) ^ 2 -
        ∑' n : ℕ, (-y) ^ (n + 1) / ((n : ℝ) + 1) ^ 2) +
    (2 * Real.log y * Real.log (1 - y ^ 2) +
      ∑' n : ℕ, (y ^ 2) ^ (n + 1) / ((n : ℝ) + 1) ^ 2) / y ^ 4

end QED.Lepton

end
