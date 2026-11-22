/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9Bounds
public import QED.DimReg.CubeMellin
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Set (d), master `I₉`: the subtracted integrals are analytic near `ε = 0`

On the disc `‖ε‖ < 1/20` the integrands of `QED.ThreeLoopD.i9K` and `QED.ThreeLoopD.i9Rem` are
dominated, uniformly in `ε`, by
`17 c ^ (-17/20) w ^ (-17/20)` and `51 c ^ (-39/40) w ^ (-39/40) (y (1 - y)) ^ (-37/40)`
(`c = x(1 - x)`), from the bounds of `QED.ThreeLoopD.SetDMastersI9Bounds` and
`‖t ^ (2ε - 1)‖ ≤ t ^ (-11/10)`, `‖t ^ (ε - 1)‖ ≤ t ^ (-21/20)` on `(0, 1]`. Both are integrable
products of one-variable powers, and the integrands are holomorphic in `ε`, so the integrals are
complex differentiable on `‖ε‖ < 1/40` (`QED.DimReg.differentiableAt_integral_of_holomorphic`),
hence analytic there.

## Main results

* `QED.ThreeLoopD.analyticOnNhd_i9K`, `QED.ThreeLoopD.analyticOnNhd_i9Rem`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric QED.DimReg

namespace QED.ThreeLoopD

/-! ### One-variable facts -/

theorem i9_eps_facts {ε : ℂ} (hε : ‖ε‖ < 1 / 20) :
    1 / 2 ≤ (1 - 3 * ε).re ∧ (1 - 3 * ε).re ≤ 3 / 2 ∧ -(1 / 20) ≤ ε.re ∧ ‖1 - 3 * ε‖ ≤ 2 ∧
      1 - 3 * ε ≠ 0 := by
  have hr := abs_le.mp ((abs_re_le_norm ε).trans hε.le)
  have hn : ‖1 - 3 * ε‖ ≤ 2 := by
    calc ‖1 - 3 * ε‖ ≤ ‖(1 : ℂ)‖ + ‖3 * ε‖ := norm_sub_le _ _
      _ = 1 + 3 * ‖ε‖ := by rw [norm_one, norm_mul]; norm_num
      _ ≤ 2 := by linarith
  have hre : (1 - 3 * ε).re = 1 - 3 * ε.re := by simp
  refine ⟨by rw [hre]; linarith, by rw [hre]; linarith, hr.1, hn, fun h => ?_⟩
  have := congrArg re h
  rw [hre, zero_re] at this
  linarith

/-- `‖t ^ z‖ ≤ t ^ a` for `0 < t ≤ 1` and `a ≤ re z`. -/
theorem norm_cpow_le_rpow_of_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) {z : ℂ} {a : ℝ}
    (ha : a ≤ z.re) : ‖(t : ℂ) ^ z‖ ≤ t ^ a := by
  rw [norm_cpow_eq_rpow_re_of_pos ht0]
  exact Real.rpow_le_rpow_of_exponent_ge ht0 ht1 ha

theorem integrableOn_rpow_Ioo {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun t : ℝ => t ^ a) (Ioo 0 1) :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
    (intervalIntegral.intervalIntegrable_rpow' ha)

theorem integrableOn_mul_one_sub_rpow_Ioo {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun t : ℝ => (t * (1 - t)) ^ a) (Ioo 0 1) := by
  have hB := betaIntegral_convergent (u := ((a + 1 : ℝ) : ℂ)) (v := ((a + 1 : ℝ) : ℂ))
    (by simp; linarith) (by simp; linarith)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at hB
  refine IntegrableOn.congr_fun hB.norm (fun t ht => ?_) measurableSet_Ioo
  have h0 : 0 < t := ht.1
  have h1 : 0 < 1 - t := by linarith [ht.2]
  have e : (1 : ℂ) - t = ((1 - t : ℝ) : ℂ) := by push_cast; ring
  rw [e, norm_mul, norm_cpow_eq_rpow_re_of_pos h0, norm_cpow_eq_rpow_re_of_pos h1,
    Real.mul_rpow h0.le h1.le]
  simp

theorem volume_restrict_prod3 (A B C : Set ℝ) :
    (volume.restrict (A ×ˢ (B ×ˢ C)) : Measure (ℝ × ℝ × ℝ)) =
      (volume.restrict A).prod ((volume.restrict B).prod (volume.restrict C)) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.volume_eq_prod,
    ← Measure.prod_restrict]

theorem volume_restrict_prod2 (A B : Set ℝ) :
    (volume.restrict (A ×ˢ B) : Measure (ℝ × ℝ)) =
      (volume.restrict A).prod (volume.restrict B) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]

/-! ### Holomorphy and measurability of the integrands -/

theorem differentiableAt_cpow_lin (r : ℝ) (a b : ℂ) {ε : ℂ} (h : (r : ℂ) ≠ 0 ∨ a * ε + b ≠ 0) :
    DifferentiableAt ℂ (fun ε : ℂ => (r : ℂ) ^ (a * ε + b)) ε :=
  ((differentiableAt_id.const_mul a).add_const b).const_cpow h

theorem differentiableAt_i9Psi (x w y : ℝ) {ε : ℂ} (h : 1 - 3 * ε ≠ 0) :
    DifferentiableAt ℂ (fun ε => i9Psi ε x w y) ε := by
  have h' : (-3 : ℂ) * ε + 1 ≠ 0 := by rwa [show (-3 : ℂ) * ε + 1 = 1 - 3 * ε by ring]
  have e : ∀ r : ℝ, (fun ε : ℂ => (r : ℂ) ^ (1 - 3 * ε)) =
      fun ε : ℂ => (r : ℂ) ^ ((-3 : ℂ) * ε + 1) := fun r => by funext ε; ring_nf
  unfold i9Psi
  refine ((?_ : DifferentiableAt ℂ _ ε).sub ?_).sub ?_ <;>
    · rw [e]; exact differentiableAt_cpow_lin _ _ _ (Or.inr h')

theorem differentiableAt_i9Wt {x w : ℝ} (hc : 0 < x * (1 - x)) (hw : 0 < w) (ε : ℂ) :
    DifferentiableAt ℂ (fun ε => i9Wt ε x w) ε := by
  have e : ∀ r : ℝ, (fun ε : ℂ => (r : ℂ) ^ (2 * ε - 1)) =
      fun ε : ℂ => (r : ℂ) ^ ((2 : ℂ) * ε + -1) := fun r => by funext ε; ring_nf
  unfold i9Wt
  refine (?_ : DifferentiableAt ℂ _ ε).mul ?_ <;> rw [e] <;>
    exact differentiableAt_cpow_lin _ _ _ (Or.inl (ofReal_ne_zero.mpr (by positivity)))

theorem differentiableAt_i9WtY {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (ε : ℂ) :
    DifferentiableAt ℂ (fun ε => i9WtY ε y) ε := by
  have e : ∀ r : ℝ, (fun ε : ℂ => (r : ℂ) ^ (ε - 1)) =
      fun ε : ℂ => (r : ℂ) ^ ((1 : ℂ) * ε + -1) := fun r => by funext ε; ring_nf
  have h1 : (0 : ℝ) < 1 - y := by linarith [hy.2]
  unfold i9WtY
  refine (?_ : DifferentiableAt ℂ _ ε).mul ?_ <;> rw [e]
  · exact differentiableAt_cpow_lin _ _ _ (Or.inl (ofReal_ne_zero.mpr hy.1.ne'))
  · exact differentiableAt_cpow_lin _ _ _ (Or.inl (ofReal_ne_zero.mpr h1.ne'))

theorem measurable_i9K_integrand (ε : ℂ) :
    Measurable fun z : ℝ × ℝ => i9Wt ε z.1 z.2 * i9Psi ε z.1 z.2 1 := by
  unfold i9Wt i9Psi i9Poly; fun_prop

theorem measurable_i9Rem_integrand (ε : ℂ) :
    Measurable fun z : ℝ × ℝ × ℝ =>
      i9Wt ε z.1 z.2.1 * i9WtY ε z.2.2 * i9PsiSub ε z.1 z.2.1 z.2.2 := by
  unfold i9Wt i9WtY i9PsiSub i9Psi i9Poly; fun_prop

/-! ### The dominating bounds -/

theorem i9_mem_Icc {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩

theorem i9_c_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < x * (1 - x) :=
  mul_pos hx.1 (by linarith [hx.2])

theorem norm_i9Wt_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hw : w ∈ Ioo (0 : ℝ) 1) :
    ‖i9Wt ε x w‖ ≤ (x * (1 - x)) ^ (-(11 / 10) : ℝ) * w ^ (-(11 / 10) : ℝ) := by
  obtain ⟨-, -, hre, -, -⟩ := i9_eps_facts hε
  have ha : -(11 / 10 : ℝ) ≤ (2 * ε - 1).re := by simp; linarith
  rw [i9Wt, norm_mul]
  exact mul_le_mul (norm_cpow_le_rpow_of_le (i9_c_pos hx) ((i9_c_le x).trans (by norm_num)) ha)
    (norm_cpow_le_rpow_of_le hw.1 hw.2.le ha) (norm_nonneg _)
    (Real.rpow_nonneg (i9_c_pos hx).le _)

theorem norm_i9WtY_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ‖i9WtY ε y‖ ≤ y ^ (-(21 / 20) : ℝ) * (1 - y) ^ (-(21 / 20) : ℝ) := by
  obtain ⟨-, -, hre, -, -⟩ := i9_eps_facts hε
  have ha : -(21 / 20 : ℝ) ≤ (ε - 1).re := by simp; linarith
  have h1 : 0 < 1 - y := by linarith [hy.2]
  rw [i9WtY, norm_mul]
  exact mul_le_mul (norm_cpow_le_rpow_of_le hy.1 hy.2.le ha)
    (norm_cpow_le_rpow_of_le h1 (by linarith [hy.1]) ha) (norm_nonneg _)
    (Real.rpow_nonneg hy.1.le _)

theorem rpow_mul_rpow_eq {t a b c : ℝ} (ht : 0 < t) (h : a + b = c) : t ^ a * t ^ b = t ^ c := by
  rw [← Real.rpow_add ht, h]

/-- The dominating bound for `K`. -/
theorem norm_i9K_integrand_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hw : w ∈ Ioo (0 : ℝ) 1) :
    ‖i9Wt ε x w * i9Psi ε x w 1‖ ≤
      17 * ((x * (1 - x)) ^ (-(17 / 20) : ℝ) * w ^ (-(17 / 20) : ℝ)) := by
  obtain ⟨h1, h2, -, hn, -⟩ := i9_eps_facts hε
  have hc := i9_c_pos hx
  have hP := norm_i9Psi_one_le h1 h2 (i9_mem_Icc hx) (i9_mem_Icc hw)
  have hM : 2 * (4 * ‖1 - 3 * ε‖) + 1 ≤ 17 := by linarith
  have hq : 0 ≤ (x * (1 - x)) ^ (1 / 4 : ℝ) * w ^ (1 / 4 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg hw.1.le _)
  rw [norm_mul]
  calc _ ≤ ((x * (1 - x)) ^ (-(11 / 10) : ℝ) * w ^ (-(11 / 10) : ℝ)) *
        (17 * ((x * (1 - x)) ^ (1 / 4 : ℝ) * w ^ (1 / 4 : ℝ))) :=
        mul_le_mul (norm_i9Wt_le hε hx hw) (hP.trans (mul_le_mul_of_nonneg_right hM hq))
          (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg hw.1.le _))
    _ = 17 * (((x * (1 - x)) ^ (-(11 / 10) : ℝ) * (x * (1 - x)) ^ (1 / 4 : ℝ)) *
        (w ^ (-(11 / 10) : ℝ) * w ^ (1 / 4 : ℝ))) := by ring
    _ = _ := by
        rw [rpow_mul_rpow_eq (c := -(17 / 20)) hc (by norm_num),
          rpow_mul_rpow_eq (c := -(17 / 20)) hw.1 (by norm_num)]

/-- The dominating bound for the remainder. -/
theorem norm_i9Rem_integrand_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {x w y : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    ‖i9Wt ε x w * i9WtY ε y * i9PsiSub ε x w y‖ ≤
      51 * ((x * (1 - x)) ^ (-(39 / 40) : ℝ) * (w ^ (-(39 / 40) : ℝ) *
        (y * (1 - y)) ^ (-(37 / 40) : ℝ))) := by
  obtain ⟨h1, h2, -, hn, -⟩ := i9_eps_facts hε
  have hc := i9_c_pos hx
  have hy1 : 0 < 1 - y := by linarith [hy.2]
  have hP := norm_i9PsiSub_le h1 h2 (i9_mem_Icc hx) (i9_mem_Icc hw) (i9_mem_Icc hy)
  have hM : 3 * (2 * (4 * ‖1 - 3 * ε‖) + 1) ≤ 51 := by linarith
  have hq : 0 ≤ (x * (1 - x)) ^ (1 / 8 : ℝ) * w ^ (1 / 8 : ℝ) * y ^ (1 / 8 : ℝ) *
      (1 - y) ^ (1 / 8 : ℝ) := by
    have := Real.rpow_nonneg hc.le (1 / 8 : ℝ)
    have := Real.rpow_nonneg hw.1.le (1 / 8 : ℝ)
    have := Real.rpow_nonneg hy.1.le (1 / 8 : ℝ)
    have := Real.rpow_nonneg hy1.le (1 / 8 : ℝ)
    positivity
  have hq2 : 0 ≤ ((x * (1 - x)) ^ (-(11 / 10) : ℝ) * w ^ (-(11 / 10) : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg hw.1.le _)
  rw [norm_mul, norm_mul]
  calc _ ≤ ((x * (1 - x)) ^ (-(11 / 10) : ℝ) * w ^ (-(11 / 10) : ℝ)) *
        (y ^ (-(21 / 20) : ℝ) * (1 - y) ^ (-(21 / 20) : ℝ)) *
        (51 * ((x * (1 - x)) ^ (1 / 8 : ℝ) * w ^ (1 / 8 : ℝ) * y ^ (1 / 8 : ℝ) *
          (1 - y) ^ (1 / 8 : ℝ))) := by
        refine mul_le_mul (mul_le_mul (norm_i9Wt_le hε hx hw) (norm_i9WtY_le hε hy)
          (norm_nonneg _) hq2) (hP.trans (mul_le_mul_of_nonneg_right hM hq)) (norm_nonneg _)
          (mul_nonneg hq2 (mul_nonneg (Real.rpow_nonneg hy.1.le _)
            (Real.rpow_nonneg hy1.le _)))
    _ = 51 * (((x * (1 - x)) ^ (-(11 / 10) : ℝ) * (x * (1 - x)) ^ (1 / 8 : ℝ)) *
        ((w ^ (-(11 / 10) : ℝ) * w ^ (1 / 8 : ℝ)) *
        ((y ^ (-(21 / 20) : ℝ) * y ^ (1 / 8 : ℝ)) *
          ((1 - y) ^ (-(21 / 20) : ℝ) * (1 - y) ^ (1 / 8 : ℝ))))) := by ring
    _ = _ := by
        rw [rpow_mul_rpow_eq (c := -(39 / 40)) hc (by norm_num),
          rpow_mul_rpow_eq (c := -(39 / 40)) hw.1 (by norm_num),
          rpow_mul_rpow_eq (c := -(37 / 40)) hy.1 (by norm_num),
          rpow_mul_rpow_eq (c := -(37 / 40)) hy1 (by norm_num), Real.mul_rpow hy.1.le hy1.le]

/-! ### Analyticity -/

theorem differentiableAt_i9K {ε₀ : ℂ} (h0 : ‖ε₀‖ < 1 / 40) : DifferentiableAt ℂ i9K ε₀ := by
  have hball : ∀ ε ∈ ball ε₀ (1 / 40), ‖ε‖ < 1 / 20 := fun ε hε => by
    have := norm_sub_norm_le ε ε₀
    rw [mem_ball, dist_eq_norm] at hε
    linarith
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  refine differentiableAt_integral_of_holomorphic (by norm_num : (0 : ℝ) < 1 / 40)
    (b := fun z => 17 * ((z.1 * (1 - z.1)) ^ (-(17 / 20) : ℝ) * z.2 ^ (-(17 / 20) : ℝ)))
    ?_ (fun ε _ => (measurable_i9K_integrand ε).aestronglyMeasurable) ?_ ?_
  · rw [volume_restrict_prod2]
    exact ((integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
      (integrableOn_rpow_Ioo (by norm_num))).const_mul 17
  · refine ae_restrict_of_forall_mem hS fun z hz ε hε => ?_
    exact norm_i9K_integrand_le (hball ε hε) hz.1 hz.2
  · refine ae_restrict_of_forall_mem hS fun z hz ε hε => ?_
    have hne := (i9_eps_facts (hball ε hε)).2.2.2.2
    exact ((differentiableAt_i9Wt (i9_c_pos hz.1) hz.2.1 ε).mul
      (differentiableAt_i9Psi _ _ _ hne)).differentiableWithinAt

theorem differentiableAt_i9Rem {ε₀ : ℂ} (h0 : ‖ε₀‖ < 1 / 40) : DifferentiableAt ℂ i9Rem ε₀ := by
  have hball : ∀ ε ∈ ball ε₀ (1 / 40), ‖ε‖ < 1 / 20 := fun ε hε => by
    have := norm_sub_norm_le ε ε₀
    rw [mem_ball, dist_eq_norm] at hε
    linarith
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :=
    measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)
  refine differentiableAt_integral_of_holomorphic (by norm_num : (0 : ℝ) < 1 / 40)
    (b := fun z => 51 * ((z.1 * (1 - z.1)) ^ (-(39 / 40) : ℝ) * (z.2.1 ^ (-(39 / 40) : ℝ) *
      (z.2.2 * (1 - z.2.2)) ^ (-(37 / 40) : ℝ))))
    ?_ (fun ε _ => (measurable_i9Rem_integrand ε).aestronglyMeasurable) ?_ ?_
  · rw [volume_restrict_prod3]
    exact ((integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
      ((integrableOn_rpow_Ioo (by norm_num)).mul_prod
        (integrableOn_mul_one_sub_rpow_Ioo (by norm_num)))).const_mul 51
  · refine ae_restrict_of_forall_mem hS fun z hz ε hε => ?_
    exact norm_i9Rem_integrand_le (hball ε hε) hz.1 hz.2.1 hz.2.2
  · refine ae_restrict_of_forall_mem hS fun z hz ε hε => ?_
    have hne := (i9_eps_facts (hball ε hε)).2.2.2.2
    have hd : DifferentiableAt ℂ (fun ε => i9PsiSub ε z.1 z.2.1 z.2.2) ε := by
      unfold i9PsiSub
      exact ((differentiableAt_i9Psi _ _ _ hne).sub
        ((differentiableAt_i9Psi _ _ _ hne).const_mul _)).sub
        ((differentiableAt_i9Psi _ _ _ hne).const_mul _)
    exact (((differentiableAt_i9Wt (i9_c_pos hz.1) hz.2.1.1 ε).mul
      (differentiableAt_i9WtY hz.2.2 ε)).mul hd).differentiableWithinAt

/-- **`K` is analytic near `0`.** -/
theorem analyticOnNhd_i9K : AnalyticOnNhd ℂ i9K (ball 0 (1 / 40)) := fun ε hε =>
  DifferentiableOn.analyticAt (fun ε' hε' => (differentiableAt_i9K
    (by simpa using hε')).differentiableWithinAt) (isOpen_ball.mem_nhds hε)

/-- **The remainder is analytic near `0`.** -/
theorem analyticOnNhd_i9Rem : AnalyticOnNhd ℂ i9Rem (ball 0 (1 / 40)) := fun ε hε =>
  DifferentiableOn.analyticAt (fun ε' hε' => (differentiableAt_i9Rem
    (by simpa using hε')).differentiableWithinAt) (isOpen_ball.mem_nhds hε)

end QED.ThreeLoopD
