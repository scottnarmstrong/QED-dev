/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersGamma
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Set (d) of `A₁⁽⁶⁾`: the master `I₁₃`, defined through a representation analytic at `ε = 0`

**The integral.** LR96's `I₁₃ = ∫ 1 / (D₁ D₂ D₄ D₅)` (Kira master `lbl[0,0,0,1,1,0,1,1,0]`;
normalization as in `QED.DimReg.LR96Family`) is the three-loop equal-mass vacuum banana with four
unit-mass lines. Pairing the lines into two one-loop bubbles with the same total momentum `q`,
each bubble is `Γ(ε) b_ε(q²)` (`QED.DimReg.integral_massiveBubbleFamily_one`), with

  `b_ε(t) = ∫₀¹ (1 + x(1 - x) t) ^ (-ε) dx` (`QED.ThreeLoopD.i13Bub`),

and the last loop is the radial integral `∫ dᵈq / π ^ (d/2) f(q²) = Γ(d/2)⁻¹ ∫₀^∞ t ^ (d/2 - 1)
f(t) dt`. Per loop measure `dᵈk / π ^ (d/2)`, `d = 4 - 2ε`,

  `I₁₃ = π ^ (3ε) Γ(ε)² / Γ(2 - ε) · T(ε)`,  `T(ε) = ∫₀^∞ t ^ (1 - ε) b_ε(t)² dt`.

This factorization is a convention recorded here, as for `I₉`, `I₁₄` and `I₁₆`.

**Why not the integral itself.** `T(ε)` converges only for `2/3 < re ε < 2`: at large `t`,
`b_ε(t) ~ B(1 - ε, 1 - ε) t ^ (-ε)`. A Bochner integral would silently be `0` near `ε = 0`. The
master is therefore defined through a subtracted representation (`QED.ThreeLoopD.i13T`).

**The subtraction.** For `t > 4`, closing the Mellin–Barnes contour of `b_ε` gives the convergent
expansion `b_ε(t) = ∑ₙ αₙ t ^ (-ε - n) + ∑ₘ βₘ t ^ (-1 - m)`, with
`αₙ = (-1)ⁿ (ε)ₙ / n! · B(1 - ε - n, 1 - ε - n)` and `βₘ = 2 (2m)! / m! · Γ(ε - 1 - m) / Γ(ε)`.
With `G = Γ(1 - ε)² / Γ(1 - 2ε)` (`QED.ThreeLoopD.i13G`) the first ones are

  `α₀ = G / (1 - 2ε)`, `α₁ = 2G`, `α₂ = -2(1 + 2ε) G`, `β₀ = 2 / (ε - 1)`,
  `β₁ = 4 / ((ε - 1)(ε - 2))`.

Squaring `α₀ u + (α₁ u + β₀)/t + (α₂ u + β₁)/t²` (`u = t ^ (-ε)`) and keeping the powers
`t ^ a` of `t ^ (1 - ε) b_ε(t)²` with `re a ≥ -1` near `ε = 0` gives six terms `cᵢ t ^ aᵢ`
(`QED.ThreeLoopD.i13Asym`). We subtract them on `t > 1`, where `∫₁^∞ t ^ a dt = -1/(a + 1)`
(`QED.ThreeLoopD.i13Tail`); the rest (`QED.ThreeLoopD.i13Rem`) is
`∫₀¹ t ^ (1 - ε) b² + ∫₁^∞ (t ^ (1 - ε) b² - ∑ cᵢ t ^ aᵢ)`, whose integrand is `O(t ^ (-2 + 3|ε|))`
at infinity, so it converges for `-1/3 < re ε < 2`. On `2/3 < re ε < 2` the two sides agree, and
the right side `QED.ThreeLoopD.i13T = i13Tail + i13Rem` is the continuation that defines
`QED.ThreeLoopD.lr96I13`. Numerically (`setDI13/i13num.py`) it agrees with `T(ε)` to nine digits
at `ε = 0.8`, and its expansion reproduces the LR96 table.

## Main definitions

* `QED.ThreeLoopD.i13Bub`, `QED.ThreeLoopD.i13G`, the coefficients `QED.ThreeLoopD.i13Al0`, ….
* `QED.ThreeLoopD.i13Asym`, `QED.ThreeLoopD.i13Tail`, `QED.ThreeLoopD.i13Rem`,
  `QED.ThreeLoopD.i13T`.
* `QED.ThreeLoopD.lr96I13`, `QED.ThreeLoopD.setDMasterI13`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.ThreeLoopD

/-- The equal-mass one-loop bubble function `b_ε(t) = ∫₀¹ (1 + x(1 - x) t) ^ (-ε) dx`. -/
noncomputable def i13Bub (ε : ℂ) (t : ℝ) : ℂ :=
  ∫ x in Ioo (0 : ℝ) 1, ((1 + x * (1 - x) * t : ℝ) : ℂ) ^ (-ε)

/-- `G(ε) = Γ(1 - ε)² / Γ(1 - 2ε)`. -/
noncomputable def i13G (ε : ℂ) : ℂ := Gamma (1 - ε) ^ 2 / Gamma (1 - 2 * ε)

/-- `α₀ = B(1 - ε, 1 - ε) = G / (1 - 2ε)`. -/
noncomputable def i13Al0 (ε : ℂ) : ℂ := i13G ε / (1 - 2 * ε)

/-- `α₁ = -ε B(-ε, -ε) = 2G`. -/
noncomputable def i13Al1 (ε : ℂ) : ℂ := 2 * i13G ε

/-- `α₂ = ε(1 + ε)/2 · B(-1 - ε, -1 - ε) = -2(1 + 2ε) G`. -/
noncomputable def i13Al2 (ε : ℂ) : ℂ := -2 * (1 + 2 * ε) * i13G ε

/-- `β₀ = 2 Γ(ε - 1) / Γ(ε) = 2 / (ε - 1)`. -/
noncomputable def i13Be0 (ε : ℂ) : ℂ := 2 / (ε - 1)

/-- `β₁ = 4 Γ(ε - 2) / Γ(ε) = 4 / ((ε - 1)(ε - 2))`. -/
noncomputable def i13Be1 (ε : ℂ) : ℂ := 4 / ((ε - 1) * (ε - 2))

/-- The six large-`t` terms of `t ^ (1 - ε) b_ε(t)²` that are not integrable at infinity near
`ε = 0`. -/
noncomputable def i13Asym (ε : ℂ) (t : ℝ) : ℂ :=
  i13Al0 ε ^ 2 * (t : ℂ) ^ (1 - 3 * ε) + 2 * i13Al0 ε * i13Al1 ε * (t : ℂ) ^ (-3 * ε) +
    2 * i13Al0 ε * i13Be0 ε * (t : ℂ) ^ (-2 * ε) +
    (i13Al1 ε ^ 2 + 2 * i13Al0 ε * i13Al2 ε) * (t : ℂ) ^ (-1 - 3 * ε) +
    2 * (i13Al1 ε * i13Be0 ε + i13Al0 ε * i13Be1 ε) * (t : ℂ) ^ (-1 - 2 * ε) +
    i13Be0 ε ^ 2 * (t : ℂ) ^ (-1 - ε)

/-- The continued integrals `∫₁^∞` of the six terms of `QED.ThreeLoopD.i13Asym`,
`∫₁^∞ t ^ a dt = -1/(a + 1)`. -/
noncomputable def i13Tail (ε : ℂ) : ℂ :=
  i13Al0 ε ^ 2 / (3 * ε - 2) - 2 * i13Al0 ε * i13Al1 ε / (1 - 3 * ε) -
    2 * i13Al0 ε * i13Be0 ε / (1 - 2 * ε) + (i13Al1 ε ^ 2 + 2 * i13Al0 ε * i13Al2 ε) / (3 * ε) +
    2 * (i13Al1 ε * i13Be0 ε + i13Al0 ε * i13Be1 ε) / (2 * ε) + i13Be0 ε ^ 2 / ε

/-- The subtracted radial integral, convergent for `-1/3 < re ε < 2`. -/
noncomputable def i13Rem (ε : ℂ) : ℂ :=
  (∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (1 - ε) * i13Bub ε t ^ 2) +
    ∫ t in Ioi (1 : ℝ), ((t : ℂ) ^ (1 - ε) * i13Bub ε t ^ 2 - i13Asym ε t)

/-- **The continued radial integral** `T(ε) = ∫₀^∞ t ^ (1 - ε) b_ε(t)² dt`. -/
noncomputable def i13T (ε : ℂ) : ℂ := i13Tail ε + i13Rem ε

/-- `I₁₃` in LR96's normalization, `1 / (D₁ D₂ D₄ D₅)`: `π ^ (3ε) Γ(ε)² / Γ(2 - ε) T(ε)`, with
`T` continued by `QED.ThreeLoopD.i13T`. Each loop carries `QED.DimReg.lr96LoopFactor`. -/
noncomputable def lr96I13 (ω : ℂ) : ℂ :=
  QED.DimReg.lr96LoopFactor (4 - 2 * ω) ^ 3 * (Gamma ω ^ 2 / Gamma (2 - ω) * i13T ω)

/-- The master `I₁₃ C⁻¹`. -/
noncomputable def setDMasterI13 (ε : ℂ) : ℂ := lr96I13 ε / lr96C ε

end QED.ThreeLoopD
