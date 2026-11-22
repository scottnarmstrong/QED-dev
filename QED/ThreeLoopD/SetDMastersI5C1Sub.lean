/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1Fub

/-!
# Set (d), master `I₅`: the substitutions for signed integrands

The substitutions of `QED.ThreeLoopD.lintegral_i5Phi0` (`a = c (u - c)/t` at fixed `c`, the swap
to `c ∈ (0, u)`, and `u = u(v)`, `QED.ThreeLoopD.i5U`), for a measurable integrable `f` of either
sign (`QED.ThreeLoopD.i5_integral_sub_ac`): with `t = (1 - ξ)²/ξ`,

  `∫∫_{a, c > 0} f = ∫₀¹ |u'(v)| ∫₀^{u(v)} |c/t| f (c (u(v) - c)/t, c) dc dv`.

The swap uses Fubini; the integrability of the transformed integrand on the product comes from
the same substitution applied to `‖f‖ₑ` (`QED.ThreeLoopD.integrable_i5SubG`).

## Main results

* `QED.ThreeLoopD.i5_integral_sub_ac`.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.ThreeLoopD

/-- The integrand after `a = c (u - c)/t`, on `{c < u}`, extended by zero; `p = (c, u)`. -/
noncomputable def i5SubG (t : ℝ) (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 < p.2 then |p.1 / t| * f (p.1 * (p.2 - p.1) / t, p.1) else 0

theorem measurable_i5SubG (t : ℝ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    Measurable (i5SubG t f) := by
  unfold i5SubG
  refine Measurable.ite (measurableSet_lt measurable_fst measurable_snd) ?_ measurable_const
  exact (by fun_prop : Measurable fun p : ℝ × ℝ => |p.1 / t|).mul
    (hf.comp (by fun_prop))

theorem i5_hasDerivWithinAt_affine (t c : ℝ) (u : ℝ) :
    HasDerivWithinAt (fun u => c * (u - c) / t) (c / t) (Ioi c) u := by
  have h := ((hasDerivAt_id u).sub_const c).const_mul c |>.div_const t
  simp only [id, mul_one] at h
  exact h.hasDerivWithinAt

theorem i5_injOn_affine {t c : ℝ} (ht : 0 < t) (hc : 0 < c) :
    InjOn (fun u => c * (u - c) / t) (Ioi c) := fun u _ v _ h => by
  field_simp at h; linarith

/-- The substitution `a = c (u - c)/t` at fixed `c`, for the lower integral of `‖f‖ₑ`. -/
theorem i5_lintegral_affine {t c : ℝ} (ht : 0 < t) (hc : 0 < c) (f : ℝ × ℝ → ℝ) :
    ∫⁻ a in Ioi (0 : ℝ), ‖f (a, c)‖ₑ = ∫⁻ u in Ioi (0 : ℝ), ‖i5SubG t f (c, u)‖ₑ := by
  conv_lhs => rw [← i5_image_affine ht hc]
  rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun u _ => i5_hasDerivWithinAt_affine t c u) (i5_injOn_affine ht hc)]
  have : (fun u => ‖i5SubG t f (c, u)‖ₑ) =
      (Ioi c).indicator (fun u => ENNReal.ofReal |c / t| * ‖f (c * (u - c) / t, c)‖ₑ) := by
    funext u
    simp only [i5SubG, indicator, mem_Ioi]
    split_ifs
    · rw [enorm_mul, Real.enorm_eq_ofReal_abs, abs_abs]
    · simp
  rw [this, lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Ioi_inter_Ioi, max_eq_left hc.le]

/-- The substitution `a = c (u - c)/t` at fixed `c`, for the integral of `f`. -/
theorem i5_integral_affine {t c : ℝ} (ht : 0 < t) (hc : 0 < c) (f : ℝ × ℝ → ℝ) :
    ∫ a in Ioi (0 : ℝ), f (a, c) = ∫ u in Ioi (0 : ℝ), i5SubG t f (c, u) := by
  conv_lhs => rw [← i5_image_affine ht hc]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u _ => i5_hasDerivWithinAt_affine t c u) (i5_injOn_affine ht hc)]
  have : (fun u => i5SubG t f (c, u)) =
      (Ioi c).indicator (fun u => |c / t| * f (c * (u - c) / t, c)) := by
    funext u
    simp only [i5SubG, indicator, mem_Ioi]
  rw [this, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Ioi_inter_Ioi, max_eq_left hc.le]
  simp only [smul_eq_mul]

theorem integrable_i5SubG {t : ℝ} (ht : 0 < t) {f : ℝ × ℝ → ℝ} (hfm : Measurable f)
    (hf : IntegrableOn f (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))) :
    Integrable (i5SubG t f) ((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))) := by
  refine ⟨(measurable_i5SubG t hfm).aestronglyMeasurable, ?_⟩
  have hf' : Integrable f ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi 0))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hf
  unfold HasFiniteIntegral
  rw [lintegral_prod _ (measurable_i5SubG t hfm).enorm.aemeasurable,
    setLIntegral_congr_fun measurableSet_Ioi fun c hc => (i5_lintegral_affine ht hc f).symm,
    ← lintegral_prod_symm _ hfm.enorm.aemeasurable]
  exact hf'.hasFiniteIntegral

/-- The swap to `c ∈ (0, u)`. -/
theorem i5_integral_swap_affine {t : ℝ} (ht : 0 < t) {f : ℝ × ℝ → ℝ} (hfm : Measurable f)
    (hf : IntegrableOn f (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))) :
    ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), f q =
      ∫ u in Ioi (0 : ℝ), ∫ c in Ioo 0 u, |c / t| * f (c * (u - c) / t, c) := by
  have hf' : Integrable f ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi 0))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hf
  have h2 : ∀ u ∈ Ioi (0 : ℝ), ∫ c in Ioi (0 : ℝ), i5SubG t f (c, u) =
      ∫ c in Ioo 0 u, |c / t| * f (c * (u - c) / t, c) := fun u _ => by
    have : (fun c => i5SubG t f (c, u)) =
        (Iio u).indicator (fun c => |c / t| * f (c * (u - c) / t, c)) := by
      funext c; simp only [i5SubG, indicator, mem_Iio]
    rw [this, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      Iio_inter_Ioi]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ hf',
    setIntegral_congr_fun measurableSet_Ioi fun c hc => i5_integral_affine ht hc f,
    integral_integral_swap (f := fun c u => i5SubG t f (c, u)) (integrable_i5SubG ht hfm hf)]
  exact setIntegral_congr_fun measurableSet_Ioi h2

/-- **The substitutions** `a = c (u - c)/t`, swap, `u = u(v)`, for signed integrands. -/
theorem i5_integral_sub_ac {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) {f : ℝ × ℝ → ℝ}
    (hfm : Measurable f) (hf : IntegrableOn f (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))) :
    ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), f q =
      ∫ v in Ioo (0 : ℝ) 1, |-((1 - ξ) / ξ * (1 / v ^ 2 + ξ))| *
        ∫ c in Ioo 0 (i5U ξ v), |c / ((1 - ξ) ^ 2 / ξ)| *
          f (c * (i5U ξ v - c) / ((1 - ξ) ^ 2 / ξ), c) := by
  have ht : 0 < (1 - ξ) ^ 2 / ξ := by
    have := hξ.1; have : 0 < 1 - ξ := by linarith [hξ.2]
    positivity
  rw [i5_integral_swap_affine ht hfm hf, ← i5U_image hξ,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun v hv => (hasDerivAt_i5U hξ hv.1).hasDerivWithinAt) (i5U_injOn hξ)]
  simp only [smul_eq_mul]

end QED.ThreeLoopD
