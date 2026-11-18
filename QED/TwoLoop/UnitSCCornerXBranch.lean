/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCornerXDefs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The corner integrand at `λ = 0` on the two branches of `β`

Section 6.6.1 of `docs/TWO-LOOP-UNITS.md`. At `λ = 0` (`M = Y²`, `h = x`), with `y₃ = Y ξ`,
`y₄ = Y (1 - ξ)`, `g = Y ξ (1 - Y)`, `e = Y² ξ (1 - ξ)` and `x* = (1 - Y)/(1 - Y ξ)`:

* `cornerGm_zero_branch1`: for `0 < x ≤ x*` (where `β = g`),
  `G_C = R₁ - (1-x)/2 log Y - x K (log ξ + log(1-Y)) - K (x log x) + (x K - (1-x)/2) log W`,
  `W = Y + ξ(1-Y) x`;
* `cornerGm_zero_branch2`: for `x* ≤ x < 1` (where `β = e x/(1-x)`),
  `G_C = R₂ - (1-x) log Y + ((1-x) log(1-x))/2 + (x K - (1-x)/2)(log(1-ξx) + log(1-(1-ξ)x))
    - x K (log ξ + log(1-ξ) + 2 log x)`,

with `K = cKx`, `R₁ = cR1` (a polynomial in `x`) and `R₂ = cR2` (simple poles at `x = 1/ξ`,
`1/(1-ξ)`). The proofs use `cornerGm_eq_split` and the factorization (6.6).
-/

@[expose] public section

open Real Set Filter Topology

namespace QED.TwoLoop.UnitSCCorner

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The branch point `x* = (1 - Y)/(1 - Y ξ)`. -/
noncomputable def xStar (Y ξ : ℝ) : ℝ := (1 - Y) / (1 - Y * ξ)

/-- **`G_C` on the branch `x < x*`**, in the letters `Y, ξ, 1 - Y, x, W = Y + ξ (1 - Y) x`. -/
noncomputable def cornerG1 (Y ξ x : ℝ) : ℝ :=
  cR1 Y ξ x - (1 - x) / 2 * log Y - x * cKx Y ξ x * (log ξ + log (1 - Y)) -
    cKx Y ξ x * (x * log x) + (x * cKx Y ξ x - (1 - x) / 2) * log (Y + ξ * (1 - Y) * x)

/-- **`G_C` on the branch `x > x*`**, in the letters
`Y, ξ, 1 - ξ, x, 1 - x, 1 - ξ x, 1 - (1 - ξ) x`. -/
noncomputable def cornerG2 (Y ξ x : ℝ) : ℝ :=
  cR2 Y ξ x - (1 - x) * log Y + 1 / 2 * ((1 - x) * log (1 - x)) +
    (x * cKx Y ξ x - (1 - x) / 2) * (log (1 - ξ * x) + log (1 - (1 - ξ) * x)) -
    x * cKx Y ξ x * (log ξ + log (1 - ξ) + 2 * log x)

section Branch

variable {Y ξ x : ℝ}

theorem ladderInnerMass_zero_div {x : ℝ} (hx : x ≠ 0) : ladderInnerMass 1 0 x / x = x := by
  unfold ladderInnerMass
  field_simp
  ring

theorem cornerMass_zero_yxi (Y ξ : ℝ) : cornerMass 0 0 (Y * ξ) (Y * (1 - ξ)) = Y ^ 2 := by
  unfold cornerMass
  ring

theorem cornerG_yxi (Y ξ : ℝ) : cornerG (Y * ξ) (Y * (1 - ξ)) = Y * ξ * (1 - Y) := by
  unfold cornerG
  ring

theorem cFormKL_zero_yxi (hY : Y ≠ 0) :
    cFormKL (cornerA1 x (Y * ξ) (Y * (1 - ξ))) (cornerA2 x (Y * ξ) (Y * (1 - ξ)))
      (cornerC1 x (Y * ξ) (Y * (1 - ξ))) (cornerC2 x (Y * ξ) (Y * (1 - ξ)))
      (cornerC3 x (Y * ξ) (Y * (1 - ξ))) x (Y ^ 2) = x * cKx Y ξ x := by
  unfold cFormKL cornerA1 cornerA2 cornerC1 cornerC2 cornerC3 cornerG cornerQ cornerR
    UnitSCReduce.cornerP1
    UnitSCReduce.cornerP2 cKx
  field_simp
  ring

theorem cFormR_zero_branch1 (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) :
    cFormR (cornerA0 x (Y * ξ) (Y * (1 - ξ))) (cornerA1 x (Y * ξ) (Y * (1 - ξ)))
      (cornerA2 x (Y * ξ) (Y * (1 - ξ))) (cornerC2 x (Y * ξ) (Y * (1 - ξ)))
      (cornerC3 x (Y * ξ) (Y * (1 - ξ))) (Y * ξ * (1 - Y)) x (Y ^ 2) = cR1 Y ξ x := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have h1Y : 1 - Y ≠ 0 := by linarith
  have hW : Y + ξ * (1 - Y) * x ≠ 0 := by
    have : 0 < 1 - Y := by linarith
    positivity
  have hD : Y ^ 2 + Y * ξ * (1 - Y) * x ≠ 0 := by
    have : 0 < 1 - Y := by linarith
    positivity
  have hξ0' := hξ0.ne'
  have hY0' := hY0.ne'
  have hx0 := hx.ne'
  unfold cFormR cornerA0 cornerA1 cornerA2 cornerC2 cornerC3 cornerG cornerQ cornerR
    UnitSCReduce.cornerP1
    UnitSCReduce.cornerP2 cR1
  field_simp
  ring

theorem cFormR_branch2_term1 {Y ξ x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    cornerA0 x (Y * ξ) (Y * (1 - ξ)) / (x * (Y ^ 2 + (Y * ξ * (Y * (1 - ξ)) * x / (1 - x)) * x)) *
        ((1 - ξ * x) * (1 - (1 - ξ) * x)) = cR2q1 Y ξ x := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  obtain ⟨hx0, hx1⟩ := hx
  have h1x : 1 - x ≠ 0 := by linarith
  have h1ξ : 1 - ξ ≠ 0 := by linarith
  have hξ1' : ξ - 1 ≠ 0 := by linarith
  have hD : Y ^ 2 + Y * ξ * (Y * (1 - ξ)) * x / (1 - x) * x ≠ 0 := by
    have : 0 < 1 - x := by linarith
    have : 0 < 1 - ξ := by linarith
    positivity
  have hY0' := hY0.ne'
  have hξ0' := hξ0.ne'
  have hx0' := hx0.ne'
  simp only [cornerA0, UnitSCReduce.cornerP1, cR2q1, px]
  field_simp
  ring

theorem cFormR_branch2_term2 {Y ξ x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    cornerA1 x (Y * ξ) (Y * (1 - ξ)) / (Y ^ 2 * (Y ^ 2 + (Y * ξ * (Y * (1 - ξ)) * x / (1 - x)) *
        x)) * ((1 - ξ * x) * (1 - (1 - ξ) * x)) = -cR2q2 Y ξ x := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  obtain ⟨hx0, hx1⟩ := hx
  have h1x : 1 - x ≠ 0 := by linarith
  have h1ξ : 1 - ξ ≠ 0 := by linarith
  have hξ1' : ξ - 1 ≠ 0 := by linarith
  have hD : Y ^ 2 + Y * ξ * (Y * (1 - ξ)) * x / (1 - x) * x ≠ 0 := by
    have : 0 < 1 - x := by linarith
    have : 0 < 1 - ξ := by linarith
    positivity
  have hY0' := hY0.ne'
  have hξ0' := hξ0.ne'
  have hx0' := hx0.ne'
  simp only [cornerA1, cornerG, cornerQ, UnitSCReduce.cornerP1, cR2q2, px]
  field_simp
  ring

theorem cFormR_branch2_term3 {Y ξ x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    cornerA2 x (Y * ξ) (Y * (1 - ξ)) * (1 / ((Y ^ 2) ^ 2 * (Y * ξ * (Y * (1 - ξ)) * x / (1 - x))) +
        x / ((Y ^ 2) ^ 2 * (Y ^ 2 + (Y * ξ * (Y * (1 - ξ)) * x / (1 - x)) * x))) * ((1 - ξ * x) *
        (1 - (1 - ξ) * x)) = cR2q3 Y ξ x := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  obtain ⟨hx0, hx1⟩ := hx
  have h1x : 1 - x ≠ 0 := by linarith
  have h1ξ : 1 - ξ ≠ 0 := by linarith
  have hξ1' : ξ - 1 ≠ 0 := by linarith
  have hD : Y ^ 2 + Y * ξ * (Y * (1 - ξ)) * x / (1 - x) * x ≠ 0 := by
    have : 0 < 1 - x := by linarith
    have : 0 < 1 - ξ := by linarith
    positivity
  have hY0' := hY0.ne'
  have hξ0' := hξ0.ne'
  have hx0' := hx0.ne'
  simp only [cornerA2, cornerG, cornerQ, cR2q3, px]
  field_simp
  ring

theorem cFormR_branch2_term4 {Y ξ x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    cornerC2 x (Y * ξ) (Y * (1 - ξ)) / (Y ^ 2 * (Y * ξ * (Y * (1 - ξ)) * x / (1 - x))) * ((1 - ξ *
        x) * (1 - (1 - ξ) * x)) = cR2q4 Y ξ x := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  obtain ⟨hx0, hx1⟩ := hx
  have h1x : 1 - x ≠ 0 := by linarith
  have h1ξ : 1 - ξ ≠ 0 := by linarith
  have hξ1' : ξ - 1 ≠ 0 := by linarith
  have hD : Y ^ 2 + Y * ξ * (Y * (1 - ξ)) * x / (1 - x) * x ≠ 0 := by
    have : 0 < 1 - x := by linarith
    have : 0 < 1 - ξ := by linarith
    positivity
  have hY0' := hY0.ne'
  have hξ0' := hξ0.ne'
  have hx0' := hx0.ne'
  simp only [cornerC2, cornerG, cornerR, UnitSCReduce.cornerP2, cR2q4, px]
  field_simp
  ring

theorem cFormR_branch2_term5 {Y ξ x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    cornerC3 x (Y * ξ) (Y * (1 - ξ)) * (1 / (2 * Y ^ 2 * (Y * ξ * (Y * (1 - ξ)) * x / (1 -
        x)) ^ 2) - x / ((Y ^ 2) ^ 2 * (Y * ξ * (Y * (1 - ξ)) * x / (1 - x)))) * ((1 - ξ * x) * (1 -
        (1 - ξ) * x)) = cR2q5 Y ξ x := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  obtain ⟨hx0, hx1⟩ := hx
  have h1x : 1 - x ≠ 0 := by linarith
  have h1ξ : 1 - ξ ≠ 0 := by linarith
  have hξ1' : ξ - 1 ≠ 0 := by linarith
  have hD : Y ^ 2 + Y * ξ * (Y * (1 - ξ)) * x / (1 - x) * x ≠ 0 := by
    have : 0 < 1 - x := by linarith
    have : 0 < 1 - ξ := by linarith
    positivity
  have hY0' := hY0.ne'
  have hξ0' := hξ0.ne'
  have hx0' := hx0.ne'
  simp only [cornerC3, cornerG, cornerR, cR2q5, px]
  field_simp
  ring

theorem cFormR_zero_branch2 (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    cFormR (cornerA0 x (Y * ξ) (Y * (1 - ξ))) (cornerA1 x (Y * ξ) (Y * (1 - ξ)))
      (cornerA2 x (Y * ξ) (Y * (1 - ξ))) (cornerC2 x (Y * ξ) (Y * (1 - ξ)))
      (cornerC3 x (Y * ξ) (Y * (1 - ξ))) (Y * ξ * (Y * (1 - ξ)) * x / (1 - x)) x (Y ^ 2) =
      cR2 Y ξ x := by
  have hK : ((1 - ξ * x) * (1 - (1 - ξ) * x)) ≠ 0 := by
    have := hξ.1; have := hξ.2; have := hx.1; have := hx.2
    exact mul_ne_zero (by nlinarith) (by nlinarith)
  have e : ∀ t₁ t₂ t₃ t₄ t₅ k : ℝ, (t₁ - t₂ + t₃ + t₄ + t₅) * k =
      t₁ * k - t₂ * k + t₃ * k + t₄ * k + t₅ * k := fun _ _ _ _ _ _ => by ring
  rw [cR2, eq_div_iff hK]
  unfold cFormR
  rw [e, cFormR_branch2_term1 hY hξ hx, cFormR_branch2_term2 hY hξ hx,
    cFormR_branch2_term3 hY hξ hx, cFormR_branch2_term4 hY hξ hx, cFormR_branch2_term5 hY hξ hx]
  have hY0 := hY.1.ne'
  have hξ0 := hξ.1.ne'
  have hξ1 : ξ - 1 ≠ 0 := by linarith [hξ.2]
  unfold cR2N cR2q1 cR2q2 cR2q3 cR2q4 cR2q5 px
  field_simp
  ring

theorem betaG_branch1 (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1)
    (hxs : x ≤ xStar Y ξ) :
    betaG (cornerG (Y * ξ) (Y * (1 - ξ))) (Y * ξ * (Y * (1 - ξ))) x = Y * ξ * (1 - Y) := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hA : 0 < 1 - Y * ξ := by nlinarith
  have hxs' : x * (1 - Y * ξ) ≤ 1 - Y := by
    unfold xStar at hxs; rwa [le_div_iff₀ hA] at hxs
  have hx1 : x < 1 := by nlinarith
  rw [betaG, cornerG_yxi, max_eq_left]
  rw [div_le_iff₀ (by linarith)]
  have : 0 < Y * ξ := by positivity
  nlinarith

theorem betaG_branch2 (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hxs : xStar Y ξ ≤ x) :
    betaG (cornerG (Y * ξ) (Y * (1 - ξ))) (Y * ξ * (Y * (1 - ξ))) x =
      Y * ξ * (Y * (1 - ξ)) * x / (1 - x) := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  obtain ⟨hx0, hx1⟩ := hx
  have hA : 0 < 1 - Y * ξ := by nlinarith
  have hxs' : 1 - Y ≤ x * (1 - Y * ξ) := by
    unfold xStar at hxs; rwa [div_le_iff₀ hA] at hxs
  rw [betaG, cornerG_yxi, max_eq_right]
  rw [le_div_iff₀ (by linarith)]
  have : 0 < Y * ξ := by positivity
  nlinarith

/-- **`G_C` on the branch `x ≤ x*`.** -/
theorem cornerGm_zero_branch1 (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x)
    (hxs : x ≤ xStar Y ξ) :
    cornerGm 0 0 (Y * ξ) (Y * (1 - ξ)) x = cornerG1 Y ξ x := by
  have hβ := betaG_branch1 hY hξ hxs
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have h1Y : 0 < 1 - Y := by linarith
  have hM : 0 < cornerMass 0 0 (Y * ξ) (Y * (1 - ξ)) := by
    rw [cornerMass_zero_yxi]; positivity
  have hβh : 0 < betaG (cornerG (Y * ξ) (Y * (1 - ξ))) (Y * ξ * (Y * (1 - ξ))) x *
      (ladderInnerMass 1 0 x / x) := by
    rw [hβ, ladderInnerMass_zero_div hx.ne']; positivity
  rw [cornerGm_eq_split hM hβh, hβ, ladderInnerMass_zero_div hx.ne', cornerMass_zero_yxi,
    cFormR_zero_branch1 ⟨hY0, hY1⟩ ⟨hξ0, hξ1⟩ hx, cFormKL_zero_yxi hY0.ne']
  have e1 : Y ^ 2 + Y * ξ * (1 - Y) * x = Y * (Y + ξ * (1 - Y) * x) := by ring
  have hW : 0 < Y + ξ * (1 - Y) * x := by positivity
  rw [e1, log_mul hY0.ne' hW.ne', log_mul (by positivity) hx.ne', log_mul (by positivity) h1Y.ne',
    log_mul hY0.ne' hξ0.ne']
  unfold cornerG1 cornerC0
  have hx0 := hx.ne'
  field_simp
  ring

/-- **`G_C` on the branch `x ≥ x*`.** -/
theorem cornerGm_zero_branch2 (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hxs : xStar Y ξ ≤ x) :
    cornerGm 0 0 (Y * ξ) (Y * (1 - ξ)) x = cornerG2 Y ξ x := by
  have hβ := betaG_branch2 hY hξ hx hxs
  have hR := cFormR_zero_branch2 hY hξ hx
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  obtain ⟨hx0, hx1⟩ := hx
  have h1ξ : 0 < 1 - ξ := by linarith
  have h1x : 0 < 1 - x := by linarith
  have hA : 0 < 1 - ξ * x := by nlinarith
  have hB : 0 < 1 - (1 - ξ) * x := by nlinarith
  have hM : 0 < cornerMass 0 0 (Y * ξ) (Y * (1 - ξ)) := by
    rw [cornerMass_zero_yxi]; positivity
  have hβh : 0 < betaG (cornerG (Y * ξ) (Y * (1 - ξ))) (Y * ξ * (Y * (1 - ξ))) x *
      (ladderInnerMass 1 0 x / x) := by
    rw [hβ, ladderInnerMass_zero_div hx0.ne']; positivity
  rw [cornerGm_eq_split hM hβh, hβ, ladderInnerMass_zero_div hx0.ne', cornerMass_zero_yxi, hR,
    cFormKL_zero_yxi hY0.ne']
  have e1 : Y ^ 2 + Y * ξ * (Y * (1 - ξ)) * x / (1 - x) * x =
      Y ^ 2 * ((1 - ξ * x) * (1 - (1 - ξ) * x)) / (1 - x) := by
    field_simp
    ring
  have e2 : Y * ξ * (Y * (1 - ξ)) * x / (1 - x) * x =
      Y ^ 2 * (ξ * ((1 - ξ) * x ^ 2)) / (1 - x) := by
    field_simp
  have l1 : log (Y ^ 2 * ((1 - ξ * x) * (1 - (1 - ξ) * x))) =
      2 * log Y + (log (1 - ξ * x) + log (1 - (1 - ξ) * x)) := by
    rw [log_mul (by positivity) (by positivity), log_mul hA.ne' hB.ne', log_pow]
    ring
  have l2 : log (Y ^ 2 * (ξ * ((1 - ξ) * x ^ 2))) =
      2 * log Y + log ξ + log (1 - ξ) + 2 * log x := by
    rw [log_mul (by positivity) (by positivity), log_mul hξ0.ne' (by positivity),
      log_mul h1ξ.ne' (by positivity), log_pow, log_pow]
    push_cast
    ring
  rw [e1, e2, log_div (by positivity) h1x.ne', log_div (by positivity) h1x.ne', l1, l2]
  unfold cornerG2 cornerC0
  have hx0' := hx0.ne'
  field_simp
  ring

end Branch

end QED.TwoLoop.UnitSCCorner

end
