/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCornerZero
public import QED.TwoLoop.UnitSCLimitCt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The corner part: reduction of `CornerPartLimit` to the regulator limits

Sections 2.3, 6.3 and 6.4 of `docs/TWO-LOOP-UNITS.md`. With the exact evaluation at `λ = 0`
(`QED.TwoLoop.UnitSCCorner.integral_cornerZero`), the joint limit `CornerPartLimit` of
`QED.TwoLoop.UnitSCLimitTotal` follows from two analytic statements (`cornerPartLimit_of`):

* `CornerMainLimit`: the `x`-integral of `G_C = cornerGm 0 0` is integrable on the triangle, and
  `∫_{y₃,y₄} ∫₀¹ G(λ, λ) dx → ∫_{y₃,y₄} ∫₀¹ G_C dx` as `λ → 0⁺` (dominated convergence; stage 3);
* `CornerErrLimit`: the rest of the corner part,
  `C(λ, Λ) - 2 ∫_{y₃,y₄} ∫₀¹ G(λ, λ) = -2 ∫∫ [G(λ, Λ) + O(Λ; λ, Λ)] - F₂⁽²⁾(λ) ∫₀¹ Y log M_Λ`,
  tends to `0` jointly (the inner subdivergence `G(λ, Λ) ≈ -ℓ_C log M_Λ` cancels against the
  counterterm term at each inner point, and the outer pair `O` is `O(polylog Λ/Λ²)`; stage 2).

It also proves the pointwise identity behind the cancellation of section 2.3 for the corner:
the coefficient `ℓ_C = c₀/h = x(1-x)/(2h)` of `-log M` integrates to `F₂⁽²⁾(λ)/2`
(`integral_cornerEll`).

Neither `CornerMainLimit` nor `CornerErrLimit` is proved here.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog

namespace QED.TwoLoop.UnitSCCorner

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink QED.TwoLoop.UnitXGraph

/-! ### The coefficient of the inner subdivergence -/

/-- **`∫₀¹ ℓ_C dx = F₂⁽²⁾(λ)/2`**, with `ℓ_C = c₀/h`, `h = (x² + (1-x) λ²)/x`: the coefficient of
`-log M_Λ` in `G(λ, Λ)` integrates to the coefficient of the counterterm at the same inner point. -/
theorem integral_cornerEll {lam : ℝ} (hlam : 0 < lam) :
    ∫ x in (0 : ℝ)..1, cornerC0 x / (ladderInnerMass 1 lam x / x) = oneLoopF2 1 lam / 2 := by
  rw [oneLoopF2, ← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le zero_le_one] at hx
  have hm := (ladderInnerMass_pos one_pos hlam hx).ne'
  rcases eq_or_lt_of_le hx.1 with h | h
  · subst h
    simp [cornerC0]
  · have := h.ne'
    unfold cornerC0
    field_simp

/-! ### The reduction -/

/-- **The main term** (stage 3 for `C`): `∫₀¹ G_C dx` is integrable on the triangle, and
`∫_{y₃,y₄} ∫₀¹ G(λ, λ) dx → ∫_{y₃,y₄} ∫₀¹ G_C dx` as `λ → 0⁺`. -/
def CornerMainLimit : Prop :=
  IntegrableOn cornerZeroInt innerTriangle ∧
    Tendsto (fun lam : ℝ => ∫ p in innerTriangle, ∫ x in Ioo (0 : ℝ) 1, cornerGm lam lam p.1 p.2 x)
      (𝓝[>] 0) (𝓝 (∫ p in innerTriangle, cornerZeroInt p))

/-- **The error terms** (stage 2 and the outer pair for `C`): the corner part minus its main term
tends to `0` jointly. -/
def CornerErrLimit : Prop :=
  Tendsto (fun p : ℝ × ℝ => cornerPart p.1 p.2 -
      2 * ∫ q in innerTriangle, ∫ x in Ioo (0 : ℝ) 1, cornerGm p.1 p.1 q.1 q.2 x)
    (𝓝[>] 0 ×ˢ atTop) (𝓝 0)

/-- **`CornerPartLimit` from the main term and the error terms.** -/
theorem cornerPartLimit_of (hM : CornerMainLimit) (hE : CornerErrLimit) : CornerPartLimit := by
  have hmain : Tendsto (fun p : ℝ × ℝ =>
      2 * ∫ q in innerTriangle, ∫ x in Ioo (0 : ℝ) 1, cornerGm p.1 p.1 q.1 q.2 x)
      (𝓝[>] 0 ×ˢ atTop) (𝓝 (2 * (-(31 / 48) + π ^ 2 / 36 + π ^ 2 / 6 * log 2 - zeta3 / 4))) := by
    rw [← integral_cornerZero hM.1]
    exact (hM.2.comp tendsto_fst).const_mul 2
  have h := hE.add hmain
  have e : 0 + 2 * (-(31 / 48) + π ^ 2 / 36 + π ^ 2 / 6 * log 2 - zeta3 / 4) =
      -(31 / 24) + 2 * (π ^ 2 / 6) * Real.log 2 + π ^ 2 / 6 / 3 - zeta3 / 2 := by ring
  rw [e] at h
  unfold CornerPartLimit
  refine h.congr fun p => ?_
  ring

/-- **The `S + C` link at `m = 1`, given the two analytic statements for the corner graph.** -/
theorem scUnitLimitOne_of_corner (hM : CornerMainLimit) (hE : CornerErrLimit) :
    QED.TwoLoop.HeadlineAssembly.SCUnitLimitOne :=
  scUnitLimitOne_of_cornerPart (cornerPartLimit_of hM hE)

end QED.TwoLoop.UnitSCCorner

end
