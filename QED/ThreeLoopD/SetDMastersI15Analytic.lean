/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15Def
public import QED.ThreeLoopD.SetDMastersI9Analytic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Set (d), master `I₁₅`: the subtracted integral `K` is analytic near `ε = 0`

On the disc `‖ε‖ < 1/20` the integrand of `QED.ThreeLoopD.i15K` is dominated, uniformly in
`ε`, by `17 c ^ (-4/5) u ^ (-4/5)` (`c = x(1 - x)`): `Ψ` is the `y = 1` face of `I₉`'s `Ψ` at
`ε' = 2ε/3` (`QED.ThreeLoopD.i15Psi_eq_i9Psi`), so `‖Ψ‖ ≤ 17 (c u) ^ (1/4)` by
`QED.ThreeLoopD.norm_i9Psi_one_le`, and `‖t ^ (ε - 1)‖ ≤ t ^ (-21/20)` on `(0, 1]`. The bound is
an integrable product of one-variable powers and the integrand is holomorphic in `ε`, so `K` is
complex differentiable on `‖ε‖ < 1/40` (`QED.DimReg.differentiableAt_integral_of_holomorphic`),
hence analytic there.

## Main results

* `QED.ThreeLoopD.norm_i15K_integrand_le`, `QED.ThreeLoopD.analyticOnNhd_i15K`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric

namespace QED.ThreeLoopD

theorem i15_eps_small {ε : ℂ} (hε : ‖ε‖ < 1 / 20) : ‖2 * ε / 3‖ < 1 / 20 := by
  rw [norm_div, norm_mul]
  norm_num
  linarith [norm_nonneg ε]

theorem differentiableAt_i15Psi (x u : ℝ) {ε : ℂ} (h : 1 - 2 * ε ≠ 0) :
    DifferentiableAt ℂ (fun ε => i15Psi ε x u) ε := by
  have e : (fun ε => i15Psi ε x u) = (fun e => i9Psi e x u 1) ∘ fun ε : ℂ => 2 * ε / 3 := by
    funext ε; exact i15Psi_eq_i9Psi ε x u
  have h' : 1 - 3 * (2 * ε / 3) ≠ 0 := by rwa [show 1 - 3 * (2 * ε / 3) = 1 - 2 * ε by ring]
  rw [e]
  exact (differentiableAt_i9Psi x u 1 h').comp ε (by fun_prop)

theorem differentiableAt_i15Wt {x u : ℝ} (hc : 0 < x * (1 - x)) (hu : 0 < u) (ε : ℂ) :
    DifferentiableAt ℂ (fun ε => i15Wt ε x u) ε := by
  have e : ∀ r : ℝ, (fun ε : ℂ => (r : ℂ) ^ (ε - 1)) =
      fun ε : ℂ => (r : ℂ) ^ ((1 : ℂ) * ε + -1) := fun r => by funext ε; ring_nf
  unfold i15Wt
  refine (?_ : DifferentiableAt ℂ _ ε).mul ?_ <;> rw [e] <;>
    exact differentiableAt_cpow_lin _ _ _ (Or.inl (ofReal_ne_zero.mpr (by positivity)))

theorem measurable_i15K_integrand (ε : ℂ) :
    Measurable fun z : ℝ × ℝ => i15Wt ε z.1 z.2 * i15Psi ε z.1 z.2 := by
  unfold i15Wt i15Psi i9Poly; fun_prop

theorem norm_i15Wt_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    ‖i15Wt ε x u‖ ≤ (x * (1 - x)) ^ (-(21 / 20) : ℝ) * u ^ (-(21 / 20) : ℝ) := by
  obtain ⟨-, -, hre, -, -⟩ := i9_eps_facts hε
  have ha : -(21 / 20 : ℝ) ≤ (ε - 1).re := by simp; linarith
  rw [i15Wt, norm_mul]
  exact mul_le_mul (norm_cpow_le_rpow_of_le (i9_c_pos hx) ((i9_c_le x).trans (by norm_num)) ha)
    (norm_cpow_le_rpow_of_le hu.1 hu.2.le ha) (norm_nonneg _)
    (Real.rpow_nonneg (i9_c_pos hx).le _)

/-- The dominating bound for `K`. -/
theorem norm_i15K_integrand_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    ‖i15Wt ε x u * i15Psi ε x u‖ ≤
      17 * ((x * (1 - x)) ^ (-(4 / 5) : ℝ) * u ^ (-(4 / 5) : ℝ)) := by
  obtain ⟨h1, h2, -, hn, -⟩ := i9_eps_facts (i15_eps_small hε)
  have hc := i9_c_pos hx
  have hP := norm_i9Psi_one_le h1 h2 (i9_mem_Icc hx) (i9_mem_Icc hu)
  rw [← i15Psi_eq_i9Psi] at hP
  have hM : 2 * (4 * ‖1 - 3 * (2 * ε / 3)‖) + 1 ≤ 17 := by linarith
  have hq : 0 ≤ (x * (1 - x)) ^ (1 / 4 : ℝ) * u ^ (1 / 4 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg hu.1.le _)
  rw [norm_mul]
  calc _ ≤ ((x * (1 - x)) ^ (-(21 / 20) : ℝ) * u ^ (-(21 / 20) : ℝ)) *
        (17 * ((x * (1 - x)) ^ (1 / 4 : ℝ) * u ^ (1 / 4 : ℝ))) :=
        mul_le_mul (norm_i15Wt_le hε hx hu) (hP.trans (mul_le_mul_of_nonneg_right hM hq))
          (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg hu.1.le _))
    _ = 17 * (((x * (1 - x)) ^ (-(21 / 20) : ℝ) * (x * (1 - x)) ^ (1 / 4 : ℝ)) *
        (u ^ (-(21 / 20) : ℝ) * u ^ (1 / 4 : ℝ))) := by ring
    _ = _ := by
        rw [rpow_mul_rpow_eq (c := -(4 / 5)) hc (by norm_num),
          rpow_mul_rpow_eq (c := -(4 / 5)) hu.1 (by norm_num)]

theorem differentiableAt_i15K {ε₀ : ℂ} (h0 : ‖ε₀‖ < 1 / 40) : DifferentiableAt ℂ i15K ε₀ := by
  have hball : ∀ ε ∈ ball ε₀ (1 / 40), ‖ε‖ < 1 / 20 := fun ε hε => by
    have := norm_sub_norm_le ε ε₀
    rw [mem_ball, dist_eq_norm] at hε
    linarith
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  refine QED.DimReg.differentiableAt_integral_of_holomorphic (by norm_num : (0 : ℝ) < 1 / 40)
    (b := fun z => 17 * ((z.1 * (1 - z.1)) ^ (-(4 / 5) : ℝ) * z.2 ^ (-(4 / 5) : ℝ)))
    ?_ (fun ε _ => (measurable_i15K_integrand ε).aestronglyMeasurable) ?_ ?_
  · rw [volume_restrict_prod2]
    exact ((integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
      (integrableOn_rpow_Ioo (by norm_num))).const_mul 17
  · refine ae_restrict_of_forall_mem hS fun z hz ε hε => ?_
    exact norm_i15K_integrand_le (hball ε hε) hz.1 hz.2
  · refine ae_restrict_of_forall_mem hS fun z hz ε hε => ?_
    have hne := (i9_eps_facts (i15_eps_small (hball ε hε))).2.2.2.2
    rw [show 1 - 3 * (2 * ε / 3) = 1 - 2 * ε by ring] at hne
    exact ((differentiableAt_i15Wt (i9_c_pos hz.1) hz.2.1 ε).mul
      (differentiableAt_i15Psi _ _ hne)).differentiableWithinAt

/-- **`K` is analytic near `0`.** -/
theorem analyticOnNhd_i15K : AnalyticOnNhd ℂ i15K (ball 0 (1 / 40)) := fun ε hε =>
  DifferentiableOn.analyticAt (fun ε' hε' => (differentiableAt_i15K
    (by simpa using hε')).differentiableWithinAt) (isOpen_ball.mem_nhds hε)

end QED.ThreeLoopD
