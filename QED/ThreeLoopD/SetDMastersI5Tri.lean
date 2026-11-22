/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5Def
public import QED.ThreeLoopD.SetDMastersI8Ang

/-!
# Set (d), master `I₅`: the triangle is holomorphic in `ε`

The integrand of `QED.ThreeLoopD.i5Tri` is `U ^ (-1 + 2ε) X ^ (-1 - ε)` with `U = 1 + a + c` and
`X = c² + a t + c w` (`QED.ThreeLoopD.i5X`). When `re w = t > 0`,
`re X = X₀ = c² + a t + c t > 0` (`QED.ThreeLoopD.i5X0`), so `|arg X| ≤ π/2` and

  `‖U ^ (-1 + 2ε) X ^ (-1 - ε)‖ ≤ e ^ (π ‖ε‖ / 2) U ^ (-1 + 2σ) X₀ ^ (-1 - σ)`,  `σ = re ε`

(`QED.ThreeLoopD.norm_i5TriF_le`). For `|σ| ≤ 1/4` the right side is at most
`U ^ (-1/2) X₀ ^ (-5/4) + U ^ (-3/2) X₀ ^ (-3/4)` (`QED.ThreeLoopD.i5_rpow_pair_le`), the exponent
being linear in `σ`. With `X₀ ≥ √(a t · c (c + t))` and `U ≥ max(1, a, c)` both terms are bounded
by products `f(a) g(c)` of integrable functions of the form `min(eᵏ xᵅ, xᵝ)`, `α > -1 > β`
(`QED.ThreeLoopD.i5Dom`), so the dominating function `QED.ThreeLoopD.i5TriDom` is integrable
(`QED.ThreeLoopD.integrableOn_i5TriDom`). Hence `ε ↦ i5Tri ε t w` is holomorphic on
`‖ε‖ < 1/4` (`QED.ThreeLoopD.differentiableOn_i5Tri`) and bounded there by
`e ^ (π/8) ∫ i5TriDom` uniformly in `w` (`QED.ThreeLoopD.norm_i5Tri_le`).

## Main results

* `QED.ThreeLoopD.norm_i5TriF_le`, `QED.ThreeLoopD.integrableOn_i5TriDom`.
* `QED.ThreeLoopD.differentiableOn_i5Tri`, `QED.ThreeLoopD.norm_i5Tri_le`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric

namespace QED.ThreeLoopD

/-- The second Symanzik polynomial of the triangle at `b = 1`, `c² + a t + c w`. -/
noncomputable def i5X (t : ℝ) (w : ℂ) (q : ℝ × ℝ) : ℂ := ((q.2 ^ 2 + q.1 * t : ℝ) : ℂ) + q.2 * w

/-- The integrand of `QED.ThreeLoopD.i5Tri`. -/
noncomputable def i5TriF (ε : ℂ) (t : ℝ) (w : ℂ) (q : ℝ × ℝ) : ℂ :=
  ((1 + q.1 + q.2 : ℝ) : ℂ) ^ (-1 + 2 * ε) * i5X t w q ^ (-1 - ε)

theorem i5Tri_eq (ε : ℂ) (t : ℝ) (w : ℂ) :
    i5Tri ε t w = ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5TriF ε t w q := rfl

/-- `re (c² + a t + c w) = c² + a t + c t` when `re w = t`. -/
noncomputable def i5X0 (t : ℝ) (q : ℝ × ℝ) : ℝ := q.2 ^ 2 + q.1 * t + q.2 * t

theorem re_i5X {t : ℝ} {w : ℂ} (hw : w.re = t) (q : ℝ × ℝ) : (i5X t w q).re = i5X0 t q := by
  rw [i5X, add_re, ofReal_re, re_ofReal_mul, hw, i5X0]

theorem i5X0_pos {t : ℝ} (ht : 0 < t) {q : ℝ × ℝ} (hq : q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :
    0 < i5X0 t q := by
  obtain ⟨h1, h2⟩ := hq
  simp only [mem_Ioi] at h1 h2
  unfold i5X0
  positivity

theorem i5X_ne_zero {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : w.re = t) {q : ℝ × ℝ}
    (hq : q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) : i5X t w q ≠ 0 := fun h => by
  have := re_i5X hw q
  rw [h, zero_re] at this
  linarith [i5X0_pos ht hq]

/-- **The pointwise bound** on the integrand of the triangle. -/
theorem norm_i5TriF_le {ε : ℂ} (hσ : -1 ≤ ε.re) {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : w.re = t)
    {q : ℝ × ℝ} (hq : q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :
    ‖i5TriF ε t w q‖ ≤ Real.exp (Real.pi / 2 * ‖ε‖) *
      ((1 + q.1 + q.2) ^ (-1 + 2 * ε.re) * i5X0 t q ^ (-1 - ε.re)) := by
  have hU : 0 < 1 + q.1 + q.2 := by
    obtain ⟨h1, h2⟩ := hq
    simp only [mem_Ioi] at h1 h2
    linarith
  have hX0 := i5X0_pos ht hq
  have hre := re_i5X hw q
  unfold i5TriF
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hU, norm_cpow_of_ne_zero (i5X_ne_zero ht hw hq)]
  have e1 : (-1 + 2 * ε).re = -1 + 2 * ε.re := by simp
  have e2 : (-1 - ε).re = -1 - ε.re := by simp
  have e3 : (-1 - ε).im = -ε.im := by simp
  rw [e1, e2, e3]
  have harg : |arg (i5X t w q)| ≤ Real.pi / 2 :=
    abs_arg_le_pi_div_two_iff.mpr (by rw [hre]; exact hX0.le)
  have hexp : (Real.exp (arg (i5X t w q) * -ε.im))⁻¹ ≤ Real.exp (Real.pi / 2 * ‖ε‖) := by
    rw [← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have h1 : |arg (i5X t w q) * ε.im| ≤ Real.pi / 2 * ‖ε‖ := by
      rw [abs_mul]
      exact mul_le_mul harg (abs_im_le_norm ε) (abs_nonneg _) (by positivity)
    have h2 := le_abs_self (arg (i5X t w q) * ε.im)
    linarith
  have hnorm : ‖i5X t w q‖ ^ (-1 - ε.re) ≤ i5X0 t q ^ (-1 - ε.re) :=
    Real.rpow_le_rpow_of_nonpos hX0 (by rw [← hre]; exact re_le_norm _) (by linarith)
  rw [div_eq_mul_inv]
  calc (1 + q.1 + q.2) ^ (-1 + 2 * ε.re) *
        (‖i5X t w q‖ ^ (-1 - ε.re) * (Real.exp (arg (i5X t w q) * -ε.im))⁻¹) ≤
      (1 + q.1 + q.2) ^ (-1 + 2 * ε.re) *
        (i5X0 t q ^ (-1 - ε.re) * Real.exp (Real.pi / 2 * ‖ε‖)) := by
        gcongr
    _ = _ := by ring

/-- The exponent is linear in `σ`, so the power pair is at most its values at `σ = ± 1/4`. -/
theorem i5_rpow_pair_le {U X : ℝ} (hU : 0 < U) (hX : 0 < X) {σ : ℝ} (hσ : |σ| ≤ 1 / 4) :
    U ^ (-1 + 2 * σ) * X ^ (-1 - σ) ≤
      U ^ (-(1 : ℝ) / 2) * X ^ (-(5 : ℝ) / 4) + U ^ (-(3 : ℝ) / 2) * X ^ (-(3 : ℝ) / 4) := by
  simp only [Real.rpow_def_of_pos hU, Real.rpow_def_of_pos hX, ← Real.exp_add]
  obtain ⟨hσ1, hσ2⟩ := abs_le.mp hσ
  rcases le_total 0 (2 * Real.log U - Real.log X) with h | h
  · have : Real.log U * (-1 + 2 * σ) + Real.log X * (-1 - σ) ≤
        Real.log U * (-(1 : ℝ) / 2) + Real.log X * (-(5 : ℝ) / 4) := by nlinarith
    exact (Real.exp_le_exp.mpr this).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have : Real.log U * (-1 + 2 * σ) + Real.log X * (-1 - σ) ≤
        Real.log U * (-(3 : ℝ) / 2) + Real.log X * (-(3 : ℝ) / 4) := by nlinarith
    exact (Real.exp_le_exp.mpr this).trans (le_add_of_nonneg_left (Real.exp_pos _).le)

/-! ### The dominating function -/

/-- `exp (min (k + α log x) (β log x))`, i.e. `min (eᵏ xᵅ) (xᵝ)` for `x > 0`. -/
noncomputable def i5Dom (k α β x : ℝ) : ℝ := Real.exp (min (k + α * Real.log x) (β * Real.log x))

theorem measurable_i5Dom (k α β : ℝ) : Measurable (i5Dom k α β) := by
  unfold i5Dom
  exact Real.measurable_exp.comp
    ((measurable_const.add (measurable_const.mul Real.measurable_log)).min
      (measurable_const.mul Real.measurable_log))

theorem integrableOn_i5Dom {k α β : ℝ} (hα : -1 < α) (hβ : β < -1) :
    IntegrableOn (i5Dom k α β) (Ioi 0) := by
  have hm : AEStronglyMeasurable (i5Dom k α β) (volume : Measure ℝ) :=
    (measurable_i5Dom k α β).aestronglyMeasurable
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have hi : IntegrableOn (fun x : ℝ => Real.exp k * x ^ α) (Ioc 0 1) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' hα)).const_mul _
    refine hi.mono' hm.restrict (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => ?_)
    rw [Real.norm_eq_abs, i5Dom, abs_of_pos (Real.exp_pos _), Real.rpow_def_of_pos hx.1,
      ← Real.exp_add]
    exact Real.exp_le_exp.mpr ((min_le_left _ _).trans (by rw [mul_comm]))
  · have hi : IntegrableOn (fun x : ℝ => x ^ β) (Ioi 1) := integrableOn_Ioi_rpow_of_lt hβ one_pos
    refine hi.mono' hm.restrict (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx
    rw [Real.norm_eq_abs, i5Dom, abs_of_pos (Real.exp_pos _), Real.rpow_def_of_pos hx0]
    exact Real.exp_le_exp.mpr ((min_le_right _ _).trans (by rw [mul_comm]))

theorem i5_le_add_min_add_min {x k y z u v : ℝ} (h1 : x ≤ k + (y + u)) (h2 : x ≤ k + (y + v))
    (h3 : x ≤ k + (z + u)) (h4 : x ≤ k + (z + v)) : x ≤ k + (min y z + min u v) := by
  rcases min_choice y z with h | h <;> rcases min_choice u v with h' | h' <;>
    rw [h, h'] <;> assumption

/-- The two `σ`-independent terms bounding the integrand of the triangle for `|re ε| ≤ 1/4`. -/
noncomputable def i5TriDom (t : ℝ) (q : ℝ × ℝ) : ℝ :=
  (1 + q.1 + q.2) ^ (-(1 : ℝ) / 2) * i5X0 t q ^ (-(5 : ℝ) / 4) +
    (1 + q.1 + q.2) ^ (-(3 : ℝ) / 2) * i5X0 t q ^ (-(3 : ℝ) / 4)

/-- The logarithmic facts behind the product bounds. -/
theorem i5_log_facts {t a c : ℝ} (ht : 0 < t) (ha : 0 < a) (hc : 0 < c) :
    0 ≤ Real.log (1 + a + c) ∧ Real.log a ≤ Real.log (1 + a + c) ∧
      Real.log c ≤ Real.log (1 + a + c) ∧ Real.log t ≤ Real.log (c + t) ∧
      Real.log c ≤ Real.log (c + t) ∧
      Real.log a + Real.log t + Real.log c + Real.log (c + t) ≤
        2 * Real.log (i5X0 t (a, c)) := by
  have hX : 0 < i5X0 t (a, c) := i5X0_pos ht ⟨ha, hc⟩
  refine ⟨Real.log_nonneg (by linarith), Real.log_le_log ha (by linarith),
    Real.log_le_log hc (by linarith), Real.log_le_log ht (by linarith),
    Real.log_le_log hc (by linarith), ?_⟩
  rw [← Real.log_mul ha.ne' ht.ne', ← Real.log_mul (by positivity) hc.ne',
    ← Real.log_mul (by positivity) (by positivity), two_mul, ← Real.log_mul hX.ne' hX.ne']
  refine Real.log_le_log (by positivity) ?_
  unfold i5X0
  simp only
  nlinarith [mul_pos (mul_pos ha ht) (mul_pos hc (add_pos hc ht)), mul_pos ha ht,
    mul_pos hc (add_pos hc ht)]

theorem i5TriDom_le {t : ℝ} (ht : 0 < t) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    i5TriDom t (a, c) ≤
      Real.exp (-(5 / 8) * Real.log t) * (i5Dom 0 (-(5 / 8)) (-(9 / 8)) a *
        i5Dom (-(5 / 8) * Real.log t) (-(5 / 8)) (-(5 / 4)) c) +
      Real.exp (-(3 / 8) * Real.log t) * (i5Dom 0 (-(3 / 8)) (-(11 / 8)) a *
        i5Dom (-(3 / 8) * Real.log t) (-(3 / 8)) (-(5 / 4)) c) := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := i5_log_facts ht ha hc
  have hU : 0 < 1 + a + c := by linarith
  have hX : 0 < i5X0 t (a, c) := i5X0_pos ht ⟨ha, hc⟩
  unfold i5TriDom i5Dom
  simp only [Real.rpow_def_of_pos hU, Real.rpow_def_of_pos hX, ← Real.exp_add]
  refine add_le_add (Real.exp_le_exp.mpr ?_) (Real.exp_le_exp.mpr ?_) <;>
    apply i5_le_add_min_add_min <;> linarith

theorem integrableOn_i5Dom_prod {k₁ α₁ β₁ k₂ α₂ β₂ : ℝ} (h1 : -1 < α₁) (h2 : β₁ < -1)
    (h3 : -1 < α₂) (h4 : β₂ < -1) :
    IntegrableOn (fun q : ℝ × ℝ => i5Dom k₁ α₁ β₁ q.1 * i5Dom k₂ α₂ β₂ q.2)
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact (integrableOn_i5Dom h1 h2).mul_prod (integrableOn_i5Dom h3 h4)

theorem measurable_i5TriDom (t : ℝ) : Measurable (i5TriDom t) := by
  unfold i5TriDom i5X0
  fun_prop

theorem i5TriDom_nonneg {t : ℝ} (ht : 0 < t) {q : ℝ × ℝ} (hq : q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :
    0 ≤ i5TriDom t q := by
  have hX := (i5X0_pos ht hq).le
  have hU : 0 ≤ 1 + q.1 + q.2 := by
    obtain ⟨h1, h2⟩ := hq
    simp only [mem_Ioi] at h1 h2
    linarith
  unfold i5TriDom
  positivity

/-- **The dominating function is integrable** on `(0, ∞)²`. -/
theorem integrableOn_i5TriDom {t : ℝ} (ht : 0 < t) :
    IntegrableOn (i5TriDom t) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
  have hI := ((integrableOn_i5Dom_prod (k₁ := 0) (k₂ := -(5 / 8) * Real.log t)
    (by norm_num : -1 < -(5 / 8 : ℝ)) (by norm_num : -(9 / 8 : ℝ) < -1)
    (by norm_num : -1 < -(5 / 8 : ℝ)) (by norm_num : -(5 / 4 : ℝ) < -1)).const_mul
      (Real.exp (-(5 / 8) * Real.log t))).add
    ((integrableOn_i5Dom_prod (k₁ := 0) (k₂ := -(3 / 8) * Real.log t)
    (by norm_num : -1 < -(3 / 8 : ℝ)) (by norm_num : -(11 / 8 : ℝ) < -1)
    (by norm_num : -1 < -(3 / 8 : ℝ)) (by norm_num : -(5 / 4 : ℝ) < -1)).const_mul
      (Real.exp (-(3 / 8) * Real.log t)))
  refine hI.mono' (measurable_i5TriDom t).aestronglyMeasurable.restrict
    (ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi) fun q hq => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (i5TriDom_nonneg ht hq)]
  obtain ⟨a, c⟩ := q
  exact i5TriDom_le ht hq.1 hq.2

/-! ### Holomorphy and the uniform bound -/

theorem norm_i5TriF_le_dom {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 4) {t : ℝ} (ht : 0 < t) {w : ℂ}
    (hw : w.re = t) {q : ℝ × ℝ} (hq : q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :
    ‖i5TriF ε t w q‖ ≤ Real.exp (Real.pi / 8) * i5TriDom t q := by
  have hσ : |ε.re| ≤ 1 / 4 := (abs_re_le_norm ε).trans hε
  have hU : 0 < 1 + q.1 + q.2 := by
    obtain ⟨h1, h2⟩ := hq
    simp only [mem_Ioi] at h1 h2
    linarith
  refine (norm_i5TriF_le (by linarith [neg_abs_le ε.re]) ht hw hq).trans ?_
  have he : Real.exp (Real.pi / 2 * ‖ε‖) ≤ Real.exp (Real.pi / 8) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  exact mul_le_mul he (i5_rpow_pair_le hU (i5X0_pos ht hq) hσ)
    (mul_nonneg (Real.rpow_nonneg hU.le _) (Real.rpow_nonneg (i5X0_pos ht hq).le _))
    (Real.exp_pos _).le

theorem measurable_i5TriF (ε : ℂ) (t : ℝ) (w : ℂ) : Measurable (i5TriF ε t w) := by
  unfold i5TriF i5X
  fun_prop

/-- **The triangle is holomorphic** in `ε` on `‖ε‖ < 1/4`. -/
theorem differentiableOn_i5Tri {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : w.re = t) :
    DifferentiableOn ℂ (fun ε => i5Tri ε t w) (ball 0 (1 / 4)) := by
  intro ε₀ hε₀
  rw [mem_ball, dist_zero_right] at hε₀
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  refine (QED.DimReg.differentiableAt_integral_of_holomorphic (R := 1 / 4 - ‖ε₀‖)
    (by linarith) (b := fun q => Real.exp (Real.pi / 8) * i5TriDom t q)
    ((integrableOn_i5TriDom ht).const_mul _)
    (fun ε _ => (measurable_i5TriF ε t w).aestronglyMeasurable) ?_ ?_).differentiableWithinAt
  · refine ae_restrict_of_forall_mem hS fun q hq ε hε => norm_i5TriF_le_dom ?_ ht hw hq
    rw [mem_ball, dist_eq_norm] at hε
    have := norm_le_norm_add_norm_sub' ε ε₀
    linarith
  · refine ae_restrict_of_forall_mem hS fun q hq => ?_
    have hU : ((1 + q.1 + q.2 : ℝ) : ℂ) ≠ 0 := by
      obtain ⟨h1, h2⟩ := hq
      simp only [mem_Ioi] at h1 h2
      exact ofReal_ne_zero.mpr (by linarith)
    have hX := i5X_ne_zero ht hw hq
    intro ε _
    unfold i5TriF
    exact ((DifferentiableAt.const_cpow (by fun_prop) (Or.inl hU)).mul
      (DifferentiableAt.const_cpow (by fun_prop) (Or.inl hX))).differentiableWithinAt

/-- **The uniform bound**: `‖i5Tri ε t w‖ ≤ e ^ (π/8) ∫ i5TriDom` for `‖ε‖ ≤ 1/4`, `re w = t`. -/
theorem norm_i5Tri_le {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 4) {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : w.re = t) :
    ‖i5Tri ε t w‖ ≤
      Real.exp (Real.pi / 8) * ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5TriDom t q := by
  rw [← integral_const_mul]
  exact norm_integral_le_of_norm_le ((integrableOn_i5TriDom ht).const_mul _)
    (ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi) fun q hq =>
      norm_i5TriF_le_dom hε ht hw hq)

end QED.ThreeLoopD
