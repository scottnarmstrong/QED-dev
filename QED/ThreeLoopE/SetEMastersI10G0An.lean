/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI10Def
public import QED.ThreeLoopD.SetDMastersI9Analytic

/-!
# Set (e), master `I₁₀`: the face integral `G₀` is analytic near `ε = 0`

`G₀ = (1 - ε)⁻¹ ∫₀¹ A(σ) ψ(σ) dσ` (`QED.ThreeLoopE.i10G0`) with
`ψ(σ) = ∫₀¹ u ^ (-ε) σ ^ (ε - 1) ((1 - (1 - u) σ) ^ (1 - 3ε) - 1) du`. On `‖ε‖ < 1/20` the Hölder
bound `QED.DimReg.norm_cpow_sub_cpow_le_sqrt` gives `‖(1 - (1 - u) σ) ^ (1 - 3ε) - 1‖ ≤ 8 √σ`,
so the integrand of `ψ` is dominated by `8 u ^ (-1/20) σ ^ (-11/20)`
(`QED.ThreeLoopE.norm_i10PsiF_le`) and that of the double integral by
`8 (σ(1 - σ)) ^ (-11/20) u ^ (-1/20)`. Hence `G₀` is the double integral over `(σ, u) ∈ (0,1)²`
(`QED.ThreeLoopE.i10G0_eq_prod`) and is analytic on `‖ε‖ < 1/40`
(`QED.ThreeLoopE.analyticOnNhd_i10G0`).

## Main results

* `QED.ThreeLoopE.norm_i10PsiF_le`, `QED.ThreeLoopE.integrableOn_i10G0F`.
* `QED.ThreeLoopE.i10G0_eq_prod`, `QED.ThreeLoopE.analyticOnNhd_i10G0`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric QED.DimReg QED.ThreeLoopD

namespace QED.ThreeLoopE

/-- The integrand of `ψ`: `u ^ (-ε) τ ^ (ε - 1) ((1 - (1 - u) τ) ^ (1 - 3ε) - 1)`. -/
noncomputable def i10PsiF (ε : ℂ) (τ u : ℝ) : ℂ :=
  (u : ℂ) ^ (-ε) * ((τ : ℂ) ^ (ε - 1) * (((1 - (1 - u) * τ : ℝ) : ℂ) ^ (1 - 3 * ε) - 1))

/-- The integrand of `(1 - ε) G₀` on `(σ, u) ∈ (0,1)²`. -/
noncomputable def i10G0F (ε : ℂ) (q : ℝ × ℝ) : ℂ := i10A ε q.1 * i10PsiF ε q.1 q.2

theorem i10Psi_eq (ε : ℂ) (τ : ℝ) : i10Psi ε τ = ∫ u in Ioo (0 : ℝ) 1, i10PsiF ε τ u := rfl

theorem i10_re_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) : ε.re ≤ 1 / 20 :=
  (le_abs_self _).trans ((abs_re_le_norm ε).trans hε.le)

theorem norm_i10A_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    ‖i10A ε σ‖ ≤ (1 - σ) ^ (-(11 / 20) : ℝ) := by
  have h1 : 0 < 1 - σ := by linarith [hσ.2]
  have hr := i10_re_le hε
  rw [i10A]
  exact norm_cpow_le_rpow_of_le h1 (by linarith [hσ.1]) (by simp; linarith)

theorem norm_i10PsiF_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {τ u : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    ‖i10PsiF ε τ u‖ ≤ 8 * (u ^ (-(1 / 20) : ℝ) * τ ^ (-(11 / 20) : ℝ)) := by
  obtain ⟨h1, h2, hre, hn, -⟩ := i9_eps_facts hε
  have hr := i10_re_le hε
  have hut : 0 ≤ (1 - u) * τ := mul_nonneg (by linarith [hu.2]) hτ.1.le
  have hut1 : (1 - u) * τ ≤ τ := mul_le_of_le_one_left hτ.1.le (by linarith [hu.1])
  have hp0 : 0 ≤ 1 - (1 - u) * τ := by linarith [hτ.2]
  have hH := norm_cpow_sub_cpow_le_sqrt hp0 zero_le_one (by linarith) (by norm_num) h1 h2
  rw [ofReal_one, one_cpow, show |1 - (1 - u) * τ - 1| = (1 - u) * τ by
    rw [show 1 - (1 - u) * τ - 1 = -((1 - u) * τ) by ring, abs_neg, abs_of_nonneg hut]] at hH
  have hs : √((1 - u) * τ) ≤ τ ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_le_sqrt hut1
  have hB : ‖((1 - (1 - u) * τ : ℝ) : ℂ) ^ (1 - 3 * ε) - 1‖ ≤ 8 * τ ^ (1 / 2 : ℝ) :=
    hH.trans (mul_le_mul (by linarith) hs (Real.sqrt_nonneg _) (by norm_num))
  have hU : ‖(u : ℂ) ^ (-ε)‖ ≤ u ^ (-(1 / 20) : ℝ) :=
    norm_cpow_le_rpow_of_le hu.1 hu.2.le (by simp; linarith)
  have hT : ‖(τ : ℂ) ^ (ε - 1)‖ ≤ τ ^ (-(21 / 20) : ℝ) :=
    norm_cpow_le_rpow_of_le hτ.1 hτ.2.le (by simp; linarith)
  have hu0 := Real.rpow_nonneg hu.1.le (-(1 / 20) : ℝ)
  have ht0 := Real.rpow_nonneg hτ.1.le (-(21 / 20) : ℝ)
  rw [i10PsiF, norm_mul, norm_mul]
  calc _ ≤ u ^ (-(1 / 20) : ℝ) * (τ ^ (-(21 / 20) : ℝ) * (8 * τ ^ (1 / 2 : ℝ))) :=
        mul_le_mul hU (mul_le_mul hT hB (norm_nonneg _) ht0) (by positivity) hu0
    _ = 8 * (u ^ (-(1 / 20) : ℝ) * (τ ^ (-(21 / 20) : ℝ) * τ ^ (1 / 2 : ℝ))) := by ring
    _ = _ := by rw [rpow_mul_rpow_eq (c := -(11 / 20)) hτ.1 (by norm_num)]

/-- The dominating bound for the double integral of `G₀`. -/
theorem norm_i10G0F_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {q : ℝ × ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    ‖i10G0F ε q‖ ≤ 8 * ((q.1 * (1 - q.1)) ^ (-(11 / 20) : ℝ) * q.2 ^ (-(1 / 20) : ℝ)) := by
  have h1 : 0 < 1 - q.1 := by linarith [hq.1.2]
  have hA := norm_i10A_le hε hq.1
  have hP := norm_i10PsiF_le hε hq.1 hq.2
  have ha0 := Real.rpow_nonneg h1.le (-(11 / 20) : ℝ)
  rw [i10G0F, norm_mul]
  calc _ ≤ (1 - q.1) ^ (-(11 / 20) : ℝ) *
        (8 * (q.2 ^ (-(1 / 20) : ℝ) * q.1 ^ (-(11 / 20) : ℝ))) :=
        mul_le_mul hA hP (norm_nonneg _) ha0
    _ = 8 * ((q.1 ^ (-(11 / 20) : ℝ) * (1 - q.1) ^ (-(11 / 20) : ℝ)) *
        q.2 ^ (-(1 / 20) : ℝ)) := by ring
    _ = _ := by rw [← Real.mul_rpow hq.1.1.le h1.le]

theorem measurable_i10G0F (ε : ℂ) : Measurable (i10G0F ε) := by
  unfold i10G0F i10A i10PsiF; fun_prop

theorem integrable_i10G0Bound :
    IntegrableOn (fun q : ℝ × ℝ =>
      8 * ((q.1 * (1 - q.1)) ^ (-(11 / 20) : ℝ) * q.2 ^ (-(1 / 20) : ℝ)))
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  rw [IntegrableOn, volume_restrict_prod2]
  exact ((integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
    (integrableOn_rpow_Ioo (by norm_num))).const_mul 8

theorem integrableOn_i10G0F {ε : ℂ} (hε : ‖ε‖ < 1 / 20) :
    IntegrableOn (i10G0F ε) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  refine integrable_i10G0Bound.mono' (measurable_i10G0F ε).aestronglyMeasurable ?_
  exact ae_restrict_of_forall_mem hS fun q hq => norm_i10G0F_le hε hq

/-- **`G₀` as a double integral** over `(σ, u) ∈ (0,1)²`. -/
theorem i10G0_eq_prod {ε : ℂ} (hε : ‖ε‖ < 1 / 20) :
    i10G0 ε = (∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i10G0F ε q) / (1 - ε) := by
  have hI := integrableOn_i10G0F hε
  rw [IntegrableOn, Measure.volume_eq_prod] at hI
  rw [i10G0, Measure.volume_eq_prod, setIntegral_prod _ hI]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo fun σ _ => ?_
  rw [i10Psi_eq, ← integral_const_mul]
  rfl

/-! ### Analyticity -/

theorem differentiableAt_i10G0F {q : ℝ × ℝ} (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) (ε : ℂ) :
    DifferentiableAt ℂ (fun ε => i10G0F ε q) ε := by
  have h1 : (0 : ℝ) < 1 - q.1 := by linarith [hq.1.2]
  have hp : (0 : ℝ) < 1 - (1 - q.2) * q.1 := by
    nlinarith [hq.1.1, hq.1.2, hq.2.1, hq.2.2]
  have e1 : (fun ε : ℂ => ((1 - q.1 : ℝ) : ℂ) ^ (-ε)) =
      fun ε => ((1 - q.1 : ℝ) : ℂ) ^ ((-1 : ℂ) * ε + 0) := by funext ε; ring_nf
  have e2 : (fun ε : ℂ => (q.2 : ℂ) ^ (-ε)) = fun ε => (q.2 : ℂ) ^ ((-1 : ℂ) * ε + 0) := by
    funext ε; ring_nf
  have e3 : (fun ε : ℂ => (q.1 : ℂ) ^ (ε - 1)) = fun ε => (q.1 : ℂ) ^ ((1 : ℂ) * ε + -1) := by
    funext ε; ring_nf
  have e4 : (fun ε : ℂ => ((1 - (1 - q.2) * q.1 : ℝ) : ℂ) ^ (1 - 3 * ε)) =
      fun ε => ((1 - (1 - q.2) * q.1 : ℝ) : ℂ) ^ ((-3 : ℂ) * ε + 1) := by funext ε; ring_nf
  have d1 : DifferentiableAt ℂ (fun ε : ℂ => ((1 - q.1 : ℝ) : ℂ) ^ (-ε)) ε := by
    rw [e1]; exact differentiableAt_cpow_lin _ _ _ (Or.inl (ofReal_ne_zero.mpr h1.ne'))
  have d2 : DifferentiableAt ℂ (fun ε : ℂ => (q.2 : ℂ) ^ (-ε)) ε := by
    rw [e2]; exact differentiableAt_cpow_lin _ _ _ (Or.inl (ofReal_ne_zero.mpr hq.2.1.ne'))
  have d3 : DifferentiableAt ℂ (fun ε : ℂ => (q.1 : ℂ) ^ (ε - 1)) ε := by
    rw [e3]; exact differentiableAt_cpow_lin _ _ _ (Or.inl (ofReal_ne_zero.mpr hq.1.1.ne'))
  have d4 : DifferentiableAt ℂ
      (fun ε : ℂ => ((1 - (1 - q.2) * q.1 : ℝ) : ℂ) ^ (1 - 3 * ε)) ε := by
    rw [e4]; exact differentiableAt_cpow_lin _ _ _ (Or.inl (ofReal_ne_zero.mpr hp.ne'))
  unfold i10G0F i10A i10PsiF
  exact d1.mul (d2.mul (d3.mul (d4.sub_const 1)))

theorem differentiableAt_i10G0 {ε₀ : ℂ} (h0 : ‖ε₀‖ < 1 / 40) : DifferentiableAt ℂ i10G0 ε₀ := by
  have hball : ∀ ε ∈ ball ε₀ (1 / 40), ‖ε‖ < 1 / 20 := fun ε hε => by
    have := norm_sub_norm_le ε ε₀
    rw [mem_ball, dist_eq_norm] at hε
    linarith
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hI : DifferentiableAt ℂ
      (fun ε => ∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i10G0F ε q) ε₀ := by
    refine differentiableAt_integral_of_holomorphic (by norm_num : (0 : ℝ) < 1 / 40)
      integrable_i10G0Bound (fun ε _ => (measurable_i10G0F ε).aestronglyMeasurable) ?_ ?_
    · exact ae_restrict_of_forall_mem hS fun q hq ε hε => norm_i10G0F_le (hball ε hε) hq
    · exact ae_restrict_of_forall_mem hS fun q hq ε _ =>
        (differentiableAt_i10G0F hq ε).differentiableWithinAt
  have h1 : (1 : ℂ) - ε₀ ≠ 0 := by
    intro h
    rw [← (sub_eq_zero.mp h)] at h0
    norm_num at h0
  have heq : (fun ε => (∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i10G0F ε q) / (1 - ε)) =ᶠ[nhds ε₀]
      i10G0 := by
    have hO : IsOpen {e : ℂ | ‖e‖ < 1 / 20} := isOpen_lt continuous_norm continuous_const
    filter_upwards [hO.mem_nhds (show ‖ε₀‖ < 1 / 20 by linarith)] with e he
    exact (i10G0_eq_prod he).symm
  exact (hI.div ((differentiableAt_const _).sub differentiableAt_id) h1).congr_of_eventuallyEq
    heq.symm

/-- **`G₀` is analytic near `0`.** -/
theorem analyticOnNhd_i10G0 : AnalyticOnNhd ℂ i10G0 (ball 0 (1 / 40)) := fun ε hε =>
  DifferentiableOn.analyticAt (fun ε' hε' => (differentiableAt_i10G0
    (by simpa using hε')).differentiableWithinAt) (isOpen_ball.mem_nhds hε)

end QED.ThreeLoopE
