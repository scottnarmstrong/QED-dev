/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the Laurent `Y`-integrals of the outer-massive corner

Helper level (no frozen statement). In the coordinates `y₃ = a Y` the branch-one weights of
the outer-massive corner times the Jacobian `Y` are Laurent polynomials
`n₃/Y³ + n₂/Y² + n₁/Y + p₀ + p₁ Y` (`formOCLaur`) in `Y`, with coefficients rational in
`(x, a, v)`; branch one is `Y > Y_c` (`formOC_branch_iff`). **`formOC_integral_laur`**:
for `0 < c ≤ 1`, `∫_{(0,1)} 1{c < Y} L(Y) dY = formOCLaurI c` with

`formOCLaurI = n₃ (c⁻² - 1)/2 + n₂ (c⁻¹ - 1) - n₁ log c + p₀ (1 - c) + p₁ (1 - c²)/2`,

the integrand being integrable (the fundamental theorem of calculus on `[c, 1]`).
-/

@[expose] public section

open Real Set MeasureTheory

namespace QED.ChainProof.SetCK

/-- The Laurent polynomial `n₃/Y³ + n₂/Y² + n₁/Y + p₀ + p₁ Y`. -/
noncomputable def formOCLaur (n₃ n₂ n₁ p₀ p₁ Y : ℝ) : ℝ :=
  n₃ / Y ^ 3 + n₂ / Y ^ 2 + n₁ / Y + p₀ + p₁ * Y

/-- Its antiderivative `-n₃/(2Y²) - n₂/Y + n₁ log Y + p₀ Y + p₁ Y²/2`. -/
noncomputable def formOCLaurP (n₃ n₂ n₁ p₀ p₁ Y : ℝ) : ℝ :=
  -(n₃ / (2 * Y ^ 2)) - n₂ / Y + n₁ * log Y + p₀ * Y + p₁ * Y ^ 2 / 2

/-- **The integral over `(c, 1)`** of the Laurent polynomial. -/
noncomputable def formOCLaurI (n₃ n₂ n₁ p₀ p₁ c : ℝ) : ℝ :=
  n₃ * (1 / c ^ 2 - 1) / 2 + n₂ * (1 / c - 1) - n₁ * log c + p₀ * (1 - c) + p₁ * (1 - c ^ 2) / 2

theorem hasDerivAt_formOCLaurP (n₃ n₂ n₁ p₀ p₁ : ℝ) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (formOCLaurP n₃ n₂ n₁ p₀ p₁) (formOCLaur n₃ n₂ n₁ p₀ p₁ Y) Y := by
  have hY0 : Y ≠ 0 := hY.ne'
  have h1 : HasDerivAt (fun Y : ℝ => 2 * Y ^ 2) (2 * (2 * Y)) Y := by
    simpa using ((hasDerivAt_id Y).pow 2).const_mul 2
  have h := ((((hasDerivAt_const Y n₃).div h1 (by positivity)).neg.sub
    ((hasDerivAt_const Y n₂).div (hasDerivAt_id Y) hY0)).add
    ((hasDerivAt_log hY0).const_mul n₁)).add ((hasDerivAt_id Y).const_mul p₀) |>.add
    (((hasDerivAt_id Y).pow 2).const_mul p₁ |>.div_const 2)
  convert h using 1
  · funext Y
    simp only [formOCLaurP, id, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply,
      Pi.pow_apply]
  · simp only [formOCLaur, id]
    field_simp
    ring

theorem continuousOn_formOCLaur (n₃ n₂ n₁ p₀ p₁ : ℝ) :
    ContinuousOn (formOCLaur n₃ n₂ n₁ p₀ p₁) (Ioi 0) := by
  unfold formOCLaur
  refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_)
    continuousOn_const) (continuousOn_const.mul continuousOn_id)
  · exact continuousOn_const.div (continuousOn_id.pow 3) fun Y hY => pow_ne_zero 3 (ne_of_gt hY)
  · exact continuousOn_const.div (continuousOn_id.pow 2) fun Y hY => pow_ne_zero 2 (ne_of_gt hY)
  · exact continuousOn_const.div continuousOn_id fun Y hY => ne_of_gt hY

/-- **The Laurent integral above a threshold** `c ∈ (0, 1]`. -/
theorem formOC_integral_laur (n₃ n₂ n₁ p₀ p₁ : ℝ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    IntegrableOn (fun Y => if c < Y then formOCLaur n₃ n₂ n₁ p₀ p₁ Y else 0) (Ioo 0 1) ∧
      ∫ Y in Ioo (0 : ℝ) 1, (if c < Y then formOCLaur n₃ n₂ n₁ p₀ p₁ Y else 0) =
        formOCLaurI n₃ n₂ n₁ p₀ p₁ c := by
  have hcont : ContinuousOn (formOCLaur n₃ n₂ n₁ p₀ p₁) (Icc c 1) :=
    (continuousOn_formOCLaur n₃ n₂ n₁ p₀ p₁).mono fun Y hY => lt_of_lt_of_le hc hY.1
  have hi : IntegrableOn (formOCLaur n₃ n₂ n₁ p₀ p₁) (Ioc c 1) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have he : (fun Y => if c < Y then formOCLaur n₃ n₂ n₁ p₀ p₁ Y else 0) =ᵐ[volume.restrict
      (Ioo (0 : ℝ) 1)] (Ioc c 1).indicator (formOCLaur n₃ n₂ n₁ p₀ p₁) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with Y hY
    by_cases h : c < Y
    · rw [ite_eq_left_iff.2 (fun h' => absurd h h'),
        indicator_of_mem (show Y ∈ Ioc c 1 from ⟨h, hY.2.le⟩)]
    · rw [ite_eq_right_iff.2 (fun h' => absurd h' h),
        indicator_of_notMem (show Y ∉ Ioc c 1 from fun hm => h hm.1)]
  have hsub : Ioo (0 : ℝ) 1 ∩ Ioc c 1 =ᵐ[volume] Ioc c 1 := by
    refine (ae_eq_refl _).trans ?_
    have : Ioo (0 : ℝ) 1 ∩ Ioc c 1 = Ioo c 1 := by
      ext Y
      simp only [mem_inter_iff, mem_Ioo, mem_Ioc]
      constructor
      · rintro ⟨⟨_, h1⟩, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩; exact ⟨⟨hc.trans h2, h1⟩, h2, h1.le⟩
    rw [this]
    exact Ioo_ae_eq_Ioc
  refine ⟨?_, ?_⟩
  · refine (IntegrableOn.congr_fun_ae ?_ he.symm)
    exact (hi.integrable_indicator measurableSet_Ioc).integrableOn
  · rw [integral_congr_ae he, integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc, inter_comm,
      Measure.restrict_congr_set hsub, ← intervalIntegral.integral_of_le hc1,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun Y hY => hasDerivAt_formOCLaurP n₃ n₂ n₁ p₀ p₁
          (lt_of_lt_of_le hc (by rw [uIcc_of_le hc1] at hY; exact hY.1)))
        (hcont.intervalIntegrable_of_Icc hc1)]
    simp only [formOCLaurP, formOCLaurI, log_one]
    field_simp
    ring

end QED.ChainProof.SetCK

end
