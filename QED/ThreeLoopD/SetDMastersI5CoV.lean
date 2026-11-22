/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5Fib

/-!
# Set (d), master `I₅`: the triangle at `w = t` as an average of fibres

With `a = c r` (at fixed `c`), Fubini, and `c = s / (1 + r)` (at fixed `r`),

  `i5Tri ε t t = ∫₀^∞ (1 + r)⁻² Φ(t, (1 + r)⁻²) dr`
  (`QED.ThreeLoopD.i5Tri_eq_integral_fib`),

where `Φ = QED.ThreeLoopD.i5Fib`: at `b = (1 + r)⁻¹`, `a + c = s`, `1 + a + c = 1 + s` and
`c² + a t + c t = s (t + b² s)`, and the Jacobian is `c · b = b² s`. The function of `r` is
integrable (`QED.ThreeLoopD.integrableOn_i5_fib`).

## Main results

* `QED.ThreeLoopD.i5Tri_eq_integral_fib`, `QED.ThreeLoopD.integrableOn_i5_fib`.
-/

@[expose] public section

open MeasureTheory Set Complex Function

namespace QED.ThreeLoopD

/-- The integrand of the triangle at `w = t` after `a = c r`, in the variables `(c, r)`. -/
noncomputable def i5G (ε : ℂ) (t : ℝ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) * i5TriF ε t (t : ℂ) (p.1 * p.2, p.1)

/-- The weight and the fibre parameter, `b² = (1 + r)⁻²`. -/
noncomputable def i5Bm (r : ℝ) : ℝ := ((1 + r)⁻¹) ^ 2

theorem integrable_i5TriF_prod {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 4) {t : ℝ} (ht : 0 < t) :
    Integrable (i5TriF ε t (t : ℂ))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  have h : IntegrableOn (i5TriF ε t (t : ℂ)) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    ((integrableOn_i5TriDom ht).const_mul (Real.exp (Real.pi / 8))).mono'
      (measurable_i5TriF ε t (t : ℂ)).aestronglyMeasurable.restrict
      (ae_restrict_of_forall_mem hS fun q hq => norm_i5TriF_le_dom hε ht (ofReal_re t) hq)
  rwa [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h

theorem measurable_i5G (ε : ℂ) (t : ℝ) : Measurable (i5G ε t) := by
  have hf := measurable_i5TriF ε t (t : ℂ)
  unfold i5G
  exact (measurable_ofReal.comp measurable_fst).mul
    (hf.comp ((measurable_fst.mul measurable_snd).prodMk measurable_fst))

/-- `∫₀^∞ f(a, c) da = ∫₀^∞ c f(c r, c) dr`. -/
theorem i5_integral_scale {g : ℝ → ℂ} {c : ℝ} (hc : 0 < c) :
    ∫ a in Ioi (0 : ℝ), g a = ∫ r in Ioi (0 : ℝ), (c : ℂ) * g (c * r) := by
  rw [integral_const_mul, integral_comp_mul_left_Ioi g 0 hc, mul_zero, Complex.real_smul,
    ← mul_assoc, ← ofReal_mul, mul_inv_cancel₀ hc.ne', ofReal_one, one_mul]

theorem integrable_i5G {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 4) {t : ℝ} (ht : 0 < t) :
    Integrable (i5G ε t)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hf := integrable_i5TriF_prod hε ht
  rw [integrable_prod_iff (measurable_i5G ε t).aestronglyMeasurable]
  constructor
  · filter_upwards [hf.prod_left_ae, ae_restrict_mem measurableSet_Ioi] with c hc hc0
    have hc0 : (0 : ℝ) < c := hc0
    have h1 : IntegrableOn (fun r => i5TriF ε t (t : ℂ) (c * r, c)) (Ioi 0) :=
      (integrableOn_Ioi_comp_mul_left_iff (fun a => i5TriF ε t (t : ℂ) (a, c)) 0 hc0).mpr
        (by rw [mul_zero]; exact hc)
    exact h1.const_mul (c : ℂ)
  · refine hf.integral_norm_prod_right.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with c hc0
    have hc0 : (0 : ℝ) < c := hc0
    have e := integral_comp_mul_left_Ioi (fun a => ‖i5TriF ε t (t : ℂ) (a, c)‖) 0 hc0
    rw [mul_zero] at e
    simp only [i5G, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    rw [integral_const_mul, e, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul]

/-- The pointwise identity behind the second substitution. -/
theorem i5G_scale_eq (ε : ℂ) {t r s : ℝ} (ht : 0 < t) (hr : 0 < r) (hs : 0 < s) :
    (((1 + r)⁻¹ : ℝ) : ℂ) * i5G ε t ((1 + r)⁻¹ * s, r) =
      (i5Bm r : ℂ) * (i5h ε s * i5P ε t (i5Bm r) s) := by
  set b := (1 + r)⁻¹ with hb
  have hb0 : 0 < b := by positivity
  have hsum : b * s * r + b * s = s := by
    rw [show b * s * r + b * s = b * (1 + r) * s by ring, hb,
      inv_mul_cancel₀ (by positivity : (1 + r : ℝ) ≠ 0), one_mul]
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hd : 0 < t + b ^ 2 * s := by positivity
  have e1 : ((1 + b * s * r + b * s : ℝ) : ℂ) = ((1 + s : ℝ) : ℂ) := by
    congr 1; linarith
  have e2 : i5X t (t : ℂ) (b * s * r, b * s) = ((s : ℝ) : ℂ) * ((t + b ^ 2 * s : ℝ) : ℂ) := by
    have hsc : (b : ℂ) * s * r + b * s = s := by exact_mod_cast hsum
    unfold i5X
    push_cast
    linear_combination (t : ℂ) * hsc
  have e3 : (s : ℂ) * (s : ℂ) ^ (-1 - ε) = (s : ℂ) ^ (-ε) := by
    rw [mul_comm, ← i5_cpow_add_one hs0]; ring_nf
  unfold i5G i5TriF i5h i5P i5Bm
  rw [← hb, e2, e1, mul_cpow_ofReal_nonneg hs.le hd.le]
  push_cast
  linear_combination (b : ℂ) ^ 2 * ((1 + (s : ℂ)) ^ (-1 + 2 * ε) *
    ((t : ℂ) + (b : ℂ) ^ 2 * s) ^ (-1 - ε)) * e3

/-- The fibre form of the inner integral. -/
theorem i5_integral_G_eq (ε : ℂ) {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    ∫ c in Ioi (0 : ℝ), i5G ε t (c, r) = (i5Bm r : ℂ) * i5Fib ε t (i5Bm r) := by
  have hb0 : 0 < (1 + r)⁻¹ := by positivity
  rw [i5_integral_scale hb0, i5Fib, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun s hs => i5G_scale_eq ε ht hr hs

/-- **The triangle at `w = t` as an average of fibres.** -/
theorem i5Tri_eq_integral_fib {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 4) {t : ℝ} (ht : 0 < t) :
    i5Tri ε t (t : ℂ) = ∫ r in Ioi (0 : ℝ), (i5Bm r : ℂ) * i5Fib ε t (i5Bm r) := by
  have hf := integrable_i5TriF_prod hε ht
  have hG := integrable_i5G hε ht
  rw [i5Tri_eq, Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ hf]
  have e1 : ∫ c in Ioi (0 : ℝ), ∫ a in Ioi (0 : ℝ), i5TriF ε t (t : ℂ) (a, c) =
      ∫ c in Ioi (0 : ℝ), ∫ r in Ioi (0 : ℝ), i5G ε t (c, r) :=
    setIntegral_congr_fun measurableSet_Ioi fun c hc => i5_integral_scale hc
  rw [e1, integral_integral_swap (f := fun c r => i5G ε t (c, r)) hG]
  exact setIntegral_congr_fun measurableSet_Ioi fun r hr => i5_integral_G_eq ε ht hr

theorem integrableOn_i5_fib {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 4) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun r => (i5Bm r : ℂ) * i5Fib ε t (i5Bm r)) (Ioi 0) :=
  (integrable_i5G hε ht).integral_prod_right.congr
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact i5_integral_G_eq ε ht hr)

end QED.ThreeLoopD
