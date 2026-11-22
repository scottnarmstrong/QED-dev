/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1Inn

/-!
# Set (d), master `I₅`: integrability of the integrand `I(x)` of `t K₁(t)`

The substitutions `a = c (u - c)/t`, the swap to `c ∈ (0, u)` and `u = u(v)` behind
`QED.ThreeLoopD.i5KerC_one_eq_rep` preserve integrability: the swapped integrand is integrable on
the product (`QED.ThreeLoopD.integrable_i5SubG`), so its partial integral in `c` is integrable in
`u`, and by the one-dimensional change of variables in `v`. Hence `v ↦ i5K1G ξ v` is integrable
on `(0, 1)` (`QED.ThreeLoopD.integrableOn_i5K1G`) and, rescaling `x = v (1 - ξ)`, the integrand
`I(x)` is interval integrable on `[0, 1 - ξ]` (`QED.ThreeLoopD.intervalIntegrable_i5K1I`).

## Main results

* `QED.ThreeLoopD.integrableOn_i5K1G`, `QED.ThreeLoopD.intervalIntegrable_i5K1I`.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.ThreeLoopD

/-- **`v ↦ i5K1G ξ v` is integrable on `(0, 1)`.** -/
theorem integrableOn_i5K1G {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (i5K1G ξ) (Ioo 0 1) := by
  have ht : 0 < (1 - ξ) ^ 2 / ξ := by
    have := hξ.1; have : 0 < 1 - ξ := by linarith [hξ.2]
    positivity
  set t := (1 - ξ) ^ 2 / ξ with ht_def
  have hm : Measurable (i5G1q t) := by
    unfold i5G1q
    exact measurable_const.mul ((measurable_const.mul (measurable_i5Phi0 _)).add
      (measurable_const.mul (measurable_i5PhiQ1 _)))
  have hi : IntegrableOn (i5G1q t) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    (((integrableOn_i5Phi0 ht).const_mul _).add ((integrableOn_i5PhiQ1 ht).const_mul _)).const_mul _
  have h1 := (integrable_i5SubG ht hm hi).integral_prod_right
  have h2 : IntegrableOn (fun u => ∫ c in Ioo 0 u, |c / t| * i5G1q t (c * (u - c) / t, c))
      (Ioi 0) := by
    refine h1.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => ?_)
    have : (fun c => i5SubG t (i5G1q t) (c, u)) =
        (Iio u).indicator (fun c => |c / t| * i5G1q t (c * (u - c) / t, c)) := by
      funext c; simp only [i5SubG, indicator, mem_Iio]
    simp only
    rw [this, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      Iio_inter_Ioi]
  rw [← i5U_image hξ, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun v hv => (hasDerivAt_i5U hξ hv.1).hasDerivWithinAt) (i5U_injOn hξ)] at h2
  refine h2.congr_fun (fun v hv => ?_) measurableSet_Ioo
  simp only [smul_eq_mul]
  rw [← i5_integral_i5K1F hξ hv, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioo fun c hc => i5K1F_eq hξ hv hc

/-- **The integrand `I(x)` is interval integrable on `[0, 1 - ξ]`.** -/
theorem intervalIntegrable_i5K1I {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (i5K1I ξ) volume 0 (1 - ξ) := by
  have hy : 0 < 1 - ξ := by linarith [hξ.2]
  have h : IntegrableOn (fun v => i5K1I ξ (v * (1 - ξ))) (Ioo 0 1) := by
    have := ((integrableOn_i5K1G hξ).congr_fun (fun v hv => i5K1G_eq hξ hv)
      measurableSet_Ioo).const_mul (1 - ξ)⁻¹
    refine IntegrableOn.congr_fun this (fun v _ => ?_) measurableSet_Ioo
    field_simp
  have h' : IntervalIntegrable (fun v => i5K1I ξ (v * (1 - ξ))) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    exact h
  have h'' := h'.comp_mul_right (c := (1 - ξ)⁻¹)
  have e : (fun x => (fun v => i5K1I ξ (v * (1 - ξ))) (x * (1 - ξ)⁻¹)) = i5K1I ξ := by
    funext x
    simp only
    rw [inv_mul_cancel_right₀ hy.ne']
  rw [e, zero_div, one_div, inv_inv] at h''
  exact h''

end QED.ThreeLoopD
