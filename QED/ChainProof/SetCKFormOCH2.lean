/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCH1
import QED.Polylog.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Set (c), Stage K, closed forms: the `a`-antiderivative `𝒢` of `G`

Helper level (no frozen statement). Item 5 of the `ρ_oC` route (Stage K notes). **`formOCH`**
is the antiderivative `𝒢(a, X)` in `a` of `G = formOCG`, with the dilogarithms `Li₂(aX)`,
`Li₂((1 - X + aX)/(2 - X))` and `Li₂((1 - aX)/(2 - X))` (all arguments in `(0, 1)`), and
**`hasDerivAt_formOCH`**: for `a, X ∈ (0, 1)`, `∂_a 𝒢(a, X) = G(a, X)`.
-/

@[expose] public section

open Real Set QED.Polylog

namespace QED.ChainProof.SetCK

/-- **The `a`-antiderivative `𝒢` of `G`.** -/
noncomputable def formOCH (a X : ℝ) : ℝ :=
  formOCHc0 a X + formOCHcl a X * log a + formOCHcL a X * log (1 - a * X) +
    formOCHK X * (log a + log X) * log (1 - a * X) + formOCHcM a X * log (1 - X + a * X) +
    formOCHcx a X * log X + a * X ^ 2 / 4 * log (1 - X) + formOCHcT a X * log (2 - X) +
    formOCHK X * (2 * Li₂ (a * X) - Li₂ ((1 - X + a * X) / (2 - X)) +
      Li₂ ((1 - a * X) / (2 - X)))

section

variable {a X : ℝ}

theorem formOCH_abs_lt_one {y : ℝ} (h0 : 0 < y) (h1 : y < 1) : |y| < 1 := by
  rw [abs_lt]; constructor <;> linarith

theorem formOCH_hasDerivAt_Li1 (ha : a ∈ Ioo (0 : ℝ) 1) (hX : X ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun b => Li₂ (b * X)) (-log (1 - a * X) / a) a := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hX0, hX1⟩ := hX
  have hp : 0 < a * X := mul_pos ha0 hX0
  have h1 : a * X < 1 := by nlinarith
  refine ((hasDerivAt_Li₂ (formOCH_abs_lt_one hp h1) hp.ne').comp a
    ((hasDerivAt_id' a).mul_const X)).congr_deriv ?_
  field_simp

theorem formOCH_hasDerivAt_Li2 (ha : a ∈ Ioo (0 : ℝ) 1) (hX : X ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun b => Li₂ ((1 - X + b * X) / (2 - X)))
      (-(log (1 - a * X) - log (2 - X)) * X / (1 - X + a * X)) a := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hX0, hX1⟩ := hX
  have h2 : 0 < 2 - X := by linarith
  have hM : 0 < 1 - X + a * X := by nlinarith
  have hL : 0 < 1 - a * X := by nlinarith
  have hp : 0 < (1 - X + a * X) / (2 - X) := by positivity
  have h1 : (1 - X + a * X) / (2 - X) < 1 := by rw [div_lt_one h2]; nlinarith
  refine ((hasDerivAt_Li₂ (formOCH_abs_lt_one hp h1) hp.ne').comp a
    ((formOCH_hasDerivAt_M X a).div_const (2 - X))).congr_deriv ?_
  have e : 1 - (1 - X + a * X) / (2 - X) = (1 - a * X) / (2 - X) := by field_simp; ring
  rw [e, log_div hL.ne' h2.ne']
  field_simp

theorem formOCH_hasDerivAt_Li3 (ha : a ∈ Ioo (0 : ℝ) 1) (hX : X ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun b => Li₂ ((1 - b * X) / (2 - X)))
      ((log (1 - X + a * X) - log (2 - X)) * X / (1 - a * X)) a := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hX0, hX1⟩ := hX
  have h2 : 0 < 2 - X := by linarith
  have hM : 0 < 1 - X + a * X := by nlinarith
  have hL : 0 < 1 - a * X := by nlinarith
  have hp : 0 < (1 - a * X) / (2 - X) := by positivity
  have h1 : (1 - a * X) / (2 - X) < 1 := by rw [div_lt_one h2]; nlinarith
  refine ((hasDerivAt_Li₂ (formOCH_abs_lt_one hp h1) hp.ne').comp a
    ((formOCH_hasDerivAt_L X a).div_const (2 - X))).congr_deriv ?_
  have e : 1 - (1 - a * X) / (2 - X) = (1 - X + a * X) / (2 - X) := by field_simp; ring
  rw [e, log_div hM.ne' h2.ne']
  field_simp

/-- **`∂_a 𝒢 = G`** on `(0, 1)²`. -/
theorem hasDerivAt_formOCH (ha : a ∈ Ioo (0 : ℝ) 1) (hX : X ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun b => formOCH b X) (formOCG a X) a := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hX0, hX1⟩ := hX
  have hL : 0 < 1 - a * X := by nlinarith
  have hM : 0 < 1 - X + a * X := by nlinarith
  have hXm : X - 1 ≠ 0 := by linarith
  have hXt : X - 2 ≠ 0 := by linarith
  have dL := formOCH_hasDerivAt_L X a
  have dM := formOCH_hasDerivAt_M X a
  have dD : HasDerivAt (fun b : ℝ => b ^ 2 * (1 - X + b * X))
      (2 * a * (1 - X + a * X) + a ^ 2 * X) a := by
    refine ((hasDerivAt_pow 2 a).mul dM).congr_deriv ?_
    push_cast
    ring
  have h0 : HasDerivAt (fun b => formOCHc0 b X) _ a :=
    (formOCH_hasDerivAt_div (hasDerivAt_id' a) ha0.ne').differentiableAt.hasDerivAt
  have hl : HasDerivAt (fun b => formOCHcl b X) _ a :=
    (formOCH_hasDerivAt_div dL hL.ne').differentiableAt.hasDerivAt
  have hcL : HasDerivAt (fun b => formOCHcL b X) _ a :=
    (formOCH_hasDerivAt_div dD (mul_ne_zero (pow_ne_zero 2 ha0.ne') hM.ne')).differentiableAt
      |>.hasDerivAt
  have hcM : HasDerivAt (fun b => formOCHcM b X) _ a :=
    (formOCH_hasDerivAt_div dL hL.ne').differentiableAt.hasDerivAt
  have hx : HasDerivAt (fun b => formOCHcx b X) _ a :=
    (formOCH_hasDerivAt_div dL hL.ne').differentiableAt.hasDerivAt
  have hT : HasDerivAt (fun b => formOCHcT b X) _ a :=
    (formOCH_hasDerivAt_div (dL.mul dM) (mul_ne_zero hL.ne' hM.ne')).differentiableAt.hasDerivAt
  have e1 := formOCH_letter_one ha0.ne' hXm hXt hL.ne' hM.ne' h0
  have e2 := formOCH_letter_log hXm hL.ne' hl
  have e3 := formOCH_letter_L ha0.ne' hXm hXt hM.ne' hcL
  have e4 := formOCH_letter_M hXm hXt hL.ne' hcM
  have e5 := formOCH_letter_X hXm hL.ne' hx
  have e6 := formOCH_letter_T hXm hL.ne' hM.ne' hT
  have la := Real.hasDerivAt_log ha0.ne'
  have lL := dL.log hL.ne'
  have lM := dM.log hM.ne'
  have i1 := formOCH_hasDerivAt_Li1 ⟨ha0, ha1⟩ ⟨hX0, hX1⟩
  have i2 := formOCH_hasDerivAt_Li2 ⟨ha0, ha1⟩ ⟨hX0, hX1⟩
  have i3 := formOCH_hasDerivAt_Li3 ⟨ha0, ha1⟩ ⟨hX0, hX1⟩
  have hco : HasDerivAt (fun b : ℝ => b * X ^ 2 / 4 * log (1 - X))
      (1 * X ^ 2 / 4 * log (1 - X)) a :=
    (((hasDerivAt_id' a).mul_const (X ^ 2)).div_const 4).mul_const _
  have big := (((((((h0.add (hl.mul la)).add (hcL.mul lL)).add
    (((la.add_const (log X)).const_mul (formOCHK X)).mul lL)).add (hcM.mul lM)).add
    (hx.mul_const (log X))).add hco).add (hT.mul_const (log (2 - X)))).add
    ((((i1.const_mul 2).sub i2).add i3).const_mul (formOCHK X))
  refine HasDerivAt.congr_deriv (f := fun b => formOCH b X) big ?_
  simp only [formOCG]
  linear_combination e1 + log a * e2 + log X * e5 + log (1 - a * X) * e3 +
    log (1 - X + a * X) * e4 + log (2 - X) * e6

end

end QED.ChainProof.SetCK

end
