/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import QED.Polylog.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A logarithmic integral evaluated by the trilogarithm

## Main results

* `QED.Polylog.abs_Li₂_le`: `|Li₂ y| ≤ (π ^ 2 / 6) |y|` for `|y| ≤ 1`.
* `QED.Polylog.integral_log_mul_log_one_add_div`:
  `∫ x in 0..1, log x log (1 + x) / x = -(3 / 4) ζ(3)`.

The integrand is the derivative of `Li₃ (-x) - log x Li₂ (-x)` on `(0, 1)`; this antiderivative
is continuous on `[0, 1]`, and the integrand has constant sign, so it is integrable.
-/

public section

open Real Set Filter Topology

namespace QED.Polylog

/-- The dilogarithm is bounded by `ζ(2)` times its argument: `|Li₂ y| ≤ (π ^ 2 / 6) |y|` for
`|y| ≤ 1`. -/
theorem abs_Li₂_le {y : ℝ} (hy : |y| ≤ 1) : |Li₂ y| ≤ π ^ 2 / 6 * |y| := by
  rw [← mul_tsum_pow_div_sq_eq_Li₂, abs_mul, mul_comm]
  gcongr
  have hs : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    simpa [Li₂_one] using hasSum_Li₂ (x := 1) (by norm_num)
  rw [← Real.norm_eq_abs]
  refine tsum_of_norm_bounded hs fun n => ?_
  rw [Real.norm_eq_abs, abs_div, abs_pow y, abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ 2)]
  exact div_le_div_of_nonneg_right (pow_le_one₀ (abs_nonneg y) hy) (by positivity)

/-- The antiderivative `Li₃ (-x) - log x Li₂ (-x)` of `log x log (1 + x) / x` is continuous on
`[0, 1]`. -/
private lemma continuousOn_antideriv :
    ContinuousOn (fun x => Li₃ (-x) - log x * Li₂ (-x)) (Icc 0 1) := by
  have hmaps : MapsTo (fun y : ℝ => -y) (Icc 0 1) (Icc (-1) 1) :=
    fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have c3 : ContinuousOn (fun y => Li₃ (-y)) (Icc 0 1) :=
    continuousOn_Li₃.comp continuous_neg.continuousOn hmaps
  have c2 : ContinuousOn (fun y => Li₂ (-y)) (Icc 0 1) :=
    continuousOn_Li₂.comp continuous_neg.continuousOn hmaps
  refine c3.sub fun x hx => ?_
  rcases hx.1.eq_or_lt with rfl | hx0
  · rw [ContinuousWithinAt, log_zero, zero_mul]
    refine squeeze_zero_norm' (eventually_nhdsWithin_of_forall fun y hy => ?_) ?_
      (a := fun y => π ^ 2 / 6 * |y * log y|)
    · have hy' : |-y| ≤ 1 := by rw [abs_neg, abs_of_nonneg hy.1]; exact hy.2
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |log y| * |Li₂ (-y)| ≤ |log y| * (π ^ 2 / 6 * |-y|) :=
            mul_le_mul_of_nonneg_left (abs_Li₂_le hy') (abs_nonneg _)
        _ = π ^ 2 / 6 * (|y| * |log y|) := by rw [abs_neg]; ring
    · have hc : Continuous fun y : ℝ => π ^ 2 / 6 * |y * log y| :=
        continuous_const.mul continuous_mul_log.abs
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  · exact ((continuousAt_log hx0.ne').continuousWithinAt).mul (c2 x hx)

/-- On `(0, 1)` the derivative of `Li₃ (-x) - log x Li₂ (-x)` is `log x log (1 + x) / x`. -/
private lemma hasDerivAt_antideriv {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => Li₃ (-x) - log x * Li₂ (-x)) (log x * log (1 + x) / x) x := by
  have habs : |-x| < 1 := by rw [abs_neg]; exact abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩
  have hne : -x ≠ 0 := neg_ne_zero.mpr hx.1.ne'
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) x := (hasDerivAt_id' x).neg
  have h1 : HasDerivAt (fun y => Li₃ (-y)) (Li₂ (-x) / (-x) * (-1)) x :=
    (hasDerivAt_Li₃ habs hne).comp x hneg
  have h2 : HasDerivAt (fun y => Li₂ (-y)) (-log (1 - -x) / (-x) * (-1)) x :=
    (hasDerivAt_Li₂ habs hne).comp x hneg
  have h3 : HasDerivAt (fun y => log y) x⁻¹ x := Real.hasDerivAt_log hx.1.ne'
  convert h1.sub (h3.mul h2) using 1
  have : x ≠ 0 := hx.1.ne'
  rw [sub_neg_eq_add]
  field_simp
  ring

/-- `∫ x in 0..1, log x log (1 + x) / x = -(3 / 4) ζ(3)`. -/
theorem integral_log_mul_log_one_add_div :
    ∫ x in (0 : ℝ)..1, log x * log (1 + x) / x = -(3 / 4) * zeta3 := by
  have hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ -(log x * log (1 + x) / x) := by
    intro x hx
    have h1 : log x < 0 := log_neg hx.1 hx.2
    have h2 : 0 < log (1 + x) := log_pos (by linarith [hx.1])
    have : log x * log (1 + x) / x < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos h1 h2) hx.1
    linarith
  have hI : MeasureTheory.IntegrableOn (fun x => -(log x * log (1 + x) / x)) (Ioc 0 1) :=
    intervalIntegral.integrableOn_deriv_of_nonneg continuousOn_antideriv.neg
      (fun x hx => (hasDerivAt_antideriv hx).neg) hpos
  have hint : IntervalIntegrable (fun x => log x * log (1 + x) / x) MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    simpa using hI.neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one continuousOn_antideriv
    (fun x hx => hasDerivAt_antideriv hx) hint]
  simp [Li₃_neg_one]

end QED.Polylog
