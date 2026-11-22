/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKVScale
public import QED.ChainProof.SetAKSMis

/-!
# Set (a), stage D4: the `log M²` part of the core identity

Helper level for `KsCore` (Set (a) of the three-loop coefficient). By the mass scaling of the
finite parts (`ksW_ksUF_scale`, `ksW_ksUFB_scale`), the coefficient of `log M²` in
`2ΔF + ΔF_B` is `-(2Δc₁ + Δc₁B)` at unit mass, where `Δc(t) = c(1, t) - c(1, 0)` for the
`log Λ` coefficients `c₁` (`ksUc1`) and `c₁B` (`ksUc1B`) of the two vertex classes. This file
proves the identity that matches it with the `log M²` part of the target:

  `2 Δc₁(t) + Δc₁B(t) = 12 D(t)`   (`t > -4`),

`D` the one-loop mass derivative (`ksDm`). Both coefficients reduce to one integral over the
inner Feynman parameter `σ` (the outer parameters enter polynomially; the `VB` shear variable
`Y` integrates to `1/2`), and the logarithms `log(1 + σ(1-σ)t)` cancel under `σ ↦ 1 - σ`.

Main results:

* `ksW_integral_ksDYmax`: `∫₀¹ Y(β, w) dw = 1/2`;
* `ksW_ksUc1_sub`, `ksW_ksUc1B_sub`: the two differences as integrals over `σ`;
* **`ksW_log_coeff`**: the identity above.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral

namespace QED.ChainProof.SetAKS

/-- The unit square measure. -/
local notation "ksWν" =>
  Measure.prod (volume.restrict (Ioo (0 : ℝ) 1)) (volume.restrict (Ioo (0 : ℝ) 1))

/-- The `σ`-density of `Δc₁` without the outer parameter. -/
noncomputable def ksWf (t σ : ℝ) : ℝ := -64 * (σ * (1 - σ)) ^ 2 * t * (1 - σ) / ksDA 1 t σ

/-- The `σ`-density of `Δc₁` multiplying `1 - x`. -/
noncomputable def ksWg (t σ : ℝ) : ℝ :=
  2 * (1 - σ) * (8 * (σ * (1 - σ)) * t * σ / ksDA 1 t σ +
    8 * σ * (4 * σ - 3) * Real.log (ksDA 1 t σ))

/-- The `σ`-density of `Δc₁B`: `16σ(1-σ) log(1 + σ(1-σ)t)`. -/
noncomputable def ksWh (t σ : ℝ) : ℝ := 16 * (σ * (1 - σ)) * Real.log (ksDA 1 t σ)

/-- The summed `σ`-density of `2Δc₁ + Δc₁B`. -/
noncomputable def ksWT (t σ : ℝ) : ℝ := 2 * ksWf t σ + ksWg t σ + ksWh t σ

theorem ksW_ksDA_one_zero (σ : ℝ) : ksDA 1 0 σ = 1 := by unfold ksDA; ring

theorem ksW_ksDA_one (t σ : ℝ) : ksDA 1 t σ = 1 + σ * (1 - σ) * t := by unfold ksDA; ring

theorem ksW_continuous_ksDA (t : ℝ) : Continuous fun σ => ksDA 1 t σ := by
  unfold ksDA; fun_prop

/-- **The `VB` shear variable integrates to `1/2`.** -/
theorem ksW_integral_ksDYmax {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∫ w in Ioo (0 : ℝ) 1, ksDYmax β w = 1 / 2 := by
  obtain ⟨h0, h1⟩ := hβ
  have h1β : 0 < 1 - β := by linarith
  have hc : Continuous fun w => ksDYmax β w := by unfold ksDYmax; fun_prop
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_add_adjacent_intervals (b := β) (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  have e1 : ∫ w in (0 : ℝ)..β, ksDYmax β w = ∫ w in (0 : ℝ)..β, w / β := by
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [uIcc_of_le h0.le] at hw
    refine min_eq_left ?_
    rw [div_le_div_iff₀ h0 h1β]
    nlinarith [hw.1, hw.2]
  have e2 : ∫ w in β..1, ksDYmax β w = ∫ w in β..1, (1 - w) / (1 - β) := by
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [uIcc_of_le h1.le] at hw
    refine min_eq_right ?_
    rw [div_le_div_iff₀ h1β h0]
    nlinarith [hw.1, hw.2]
  rw [e1, e2, intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
    integral_id, integral_id, intervalIntegral.integral_const]
  field_simp
  ring

section Coeff

variable {t : ℝ} (ht : -4 < t)
include ht

theorem ksW_ksDA_pos {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) : 0 < ksDA 1 t σ :=
  ksD_ksDA_pos one_pos (by simpa using ht) hσ

theorem ksW_continuousOn_ksWT :
    ContinuousOn (ksWf t) (Icc 0 1) ∧ ContinuousOn (ksWg t) (Icc 0 1) ∧
      ContinuousOn (ksWh t) (Icc 0 1) := by
  have hA := (ksW_continuous_ksDA t).continuousOn (s := Icc (0 : ℝ) 1)
  have hA0 : ∀ σ ∈ Icc (0 : ℝ) 1, ksDA 1 t σ ≠ 0 := fun σ hσ => (ksW_ksDA_pos ht hσ).ne'
  have hL := hA.log hA0
  refine ⟨?_, ?_, ?_⟩
  · unfold ksWf; exact ContinuousOn.div (by fun_prop) hA hA0
  · unfold ksWg
    exact (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).mul
      ((ContinuousOn.div (by fun_prop) hA hA0).add ((by fun_prop :
        ContinuousOn (fun σ : ℝ => 8 * σ * (4 * σ - 3)) _).mul hL))
  · unfold ksWh; exact (by fun_prop : ContinuousOn (fun σ : ℝ => 16 * (σ * (1 - σ))) _).mul hL

omit ht in
theorem ksW_integrableOn {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
    IntegrableOn f (Ioo (0 : ℝ) 1) :=
  hf.integrableOn_Icc.mono_set Ioo_subset_Icc_self

omit ht in
theorem ksW_intervalIntegrable {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
    IntervalIntegrable f volume 0 1 :=
  hf.intervalIntegrable_of_Icc zero_le_one

/-- The pointwise difference of the `VA` `log Λ` densities. -/
theorem ksW_ksUal1_sub {x σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) :
    ksUal1 1 t x σ - ksUal1 1 0 x σ = ksWf t σ + (1 - x) * ksWg t σ := by
  have hA := (ksW_ksDA_pos ht hσ).ne'
  unfold ksUal1 ksWf ksWg ksDa0 ksDa1
  rw [ksW_ksDA_one_zero, Real.log_one]
  rw [ksW_ksDA_one] at hA ⊢
  field_simp
  ring

/-- **The `VA` difference** `Δc₁ = ∫ f + (1/2) ∫ g`. -/
theorem ksW_ksUc1_sub : ksUc1 1 t - ksUc1 1 0 =
    (∫ σ in Ioo (0 : ℝ) 1, ksWf t σ) + 1 / 2 * ∫ σ in Ioo (0 : ℝ) 1, ksWg t σ := by
  have ht' : -(4 * (1 : ℝ) ^ 2) < t := by simpa using ht
  have h0' : -(4 * (1 : ℝ) ^ 2) < 0 := by norm_num
  have hIt := ksU_integrable_ksUal1 one_pos ht'
  have hI0 := ksU_integrable_ksUal1 one_pos h0'
  obtain ⟨cf, cg, -⟩ := ksW_continuousOn_ksWT ht
  have hf := ksW_integrableOn cf
  have hg := ksW_integrableOn cg
  set F := ∫ σ in Ioo (0 : ℝ) 1, ksWf t σ
  set G := ∫ σ in Ioo (0 : ℝ) 1, ksWg t σ
  unfold ksUc1
  rw [← integral_sub hIt.integral_prod_left hI0.integral_prod_left]
  have e : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      (∫ σ in Ioo (0 : ℝ) 1, ksUal1 1 t x σ) - (∫ σ in Ioo (0 : ℝ) 1, ksUal1 1 0 x σ) =
        F + (1 - x) * G := by
    filter_upwards [hIt.prod_right_ae, hI0.prod_right_ae] with x h1 h2
    rw [← integral_sub h1 h2, setIntegral_congr_fun measurableSet_Ioo
      (fun σ hσ => ksW_ksUal1_sub ht (Ioo_subset_Icc_self hσ)), integral_add hf (hg.const_mul _),
      MeasureTheory.integral_const_mul]
  rw [integral_congr_ae e, integral_add (integrable_const _) ((Continuous.integrableOn_Icc
      (by fun_prop : Continuous fun x : ℝ => 1 - x)).mono_set Ioo_subset_Icc_self |>.mul_const G),
    MeasureTheory.integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const,
    intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
    integral_id, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul, mul_one]
  ring

/-- The pointwise difference of the `VB` `log Λ` densities. -/
theorem ksW_ksUb1_sub {ρ β w : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (hw : w ∈ Ioo (0 : ℝ) 1) :
    ksUb1 1 t ρ β w - ksUb1 1 0 ρ β w = ρ * ksWh t w + ksDYmax β w * ksWh t β := by
  have hAw := (ksW_ksDA_pos ht (Ioo_subset_Icc_self hw)).ne'
  have hY := (ksU_ksDYmax_pos hβ hw).ne'
  have hρ0 := hρ.1.ne'
  unfold ksUb1 ksUl3
  rw [ksW_ksDA_one_zero, ksW_ksDA_one_zero, mul_one, inv_one, Real.log_one, Real.log_inv,
    Real.log_div hY (mul_ne_zero hρ0 hAw), Real.log_div hY hρ0, Real.log_mul hρ0 hAw]
  unfold ksWh ksUcB ksUf0
  ring

omit ht in
theorem ksW_abs_ksWh_le {σ : ℝ} (ht : -4 < t) (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    |ksWh t σ| ≤ 16 * ksULA 1 t := by
  have hl := ksU_abs_log_ksDA_le one_pos (by simpa using ht) (Ioo_subset_Icc_self hσ)
  have hu0 : 0 ≤ σ * (1 - σ) := mul_nonneg hσ.1.le (by linarith [hσ.2])
  have hu1 : σ * (1 - σ) ≤ 1 := by nlinarith [hσ.1, hσ.2]
  unfold ksWh
  rw [abs_mul, abs_mul, abs_of_nonneg hu0, abs_of_pos (by norm_num : (0 : ℝ) < 16)]
  have := abs_nonneg (Real.log (ksDA 1 t σ))
  nlinarith

/-- **The `VB` difference** `Δc₁B = ∫ h`. -/
theorem ksW_ksUc1B_sub : ksUc1B 1 t - ksUc1B 1 0 = ∫ σ in Ioo (0 : ℝ) 1, ksWh t σ := by
  have ht' : -(4 * (1 : ℝ) ^ 2) < t := by simpa using ht
  have h0' : -(4 * (1 : ℝ) ^ 2) < 0 := by norm_num
  have hbt := ksU_integrable_ksUb1 one_pos ht'
  have hb0 := ksU_integrable_ksUb1 one_pos h0'
  have hLA := ksU_ksULA_nonneg 1 t
  have hmh : Measurable (ksWh t) := by unfold ksWh ksDA; fun_prop
  have hmY : Measurable fun q : ℝ × ℝ => ksDYmax q.1 q.2 := by unfold ksDYmax; fun_prop
  have hgg : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ σ ∈ Ioo (0 : ℝ) 1, 1 ≤ ksUg x * ksUg σ := fun x hx σ hσ =>
    one_le_mul_of_one_le_of_one_le (ksU_one_le_ksUg hx) (ksU_one_le_ksUg hσ)
  have i1 : Integrable (fun q : ℝ × ℝ => ksWh t q.2 / 2) ksWν := by
    refine ksU_integrable_of_le (by fun_prop) (16 * ksULA 1 t) fun x hx σ hσ => ?_
    rw [abs_div, abs_two]
    have := ksW_abs_ksWh_le ht hσ
    nlinarith [hgg x hx σ hσ]
  have i2 : Integrable (fun q : ℝ × ℝ => ksDYmax q.1 q.2 * ksWh t q.1) ksWν := by
    refine ksU_integrable_of_le (by fun_prop) (16 * ksULA 1 t) fun x hx σ hσ => ?_
    have hY0 := ksU_ksDYmax_pos hx hσ
    have hY1 := ksU_ksDYmax_le_one hx (w := σ)
    rw [abs_mul, abs_of_pos hY0]
    have := ksW_abs_ksWh_le ht hx
    nlinarith [hgg x hx σ hσ, abs_nonneg (ksWh t x)]
  unfold ksUc1B
  rw [← integral_sub hbt hb0,
    ksU_integral_cube_eq (g := fun z => ksUb1 1 t z.1.1 z.1.2 z.2 - ksUb1 1 0 z.1.1 z.1.2 z.2)
      (hbt.sub hb0)]
  have e : ∀ᵐ q ∂ksWν, (∫ ρ in Ioo (0 : ℝ) 1, (ksUb1 1 t ρ q.1 q.2 - ksUb1 1 0 ρ q.1 q.2)) =
      ksWh t q.2 / 2 + ksDYmax q.1 q.2 * ksWh t q.1 := by
    filter_upwards [ksW_ae_mem_square] with q hq
    rw [setIntegral_congr_fun measurableSet_Ioo
      (fun ρ hρ => ksW_ksUb1_sub ht hρ hq.1 hq.2), ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_add (intervalIntegral.intervalIntegrable_id.mul_const _)
        intervalIntegrable_const, intervalIntegral.integral_mul_const, integral_id,
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [integral_congr_ae e, integral_add i1 i2, integral_prod _ i2]
  have e1 : ∫ q : ℝ × ℝ, ksWh t q.2 / 2 ∂ksWν = (∫ σ in Ioo (0 : ℝ) 1, ksWh t σ) / 2 := by
    have := integral_prod_mul (μ := volume.restrict (Ioo (0 : ℝ) 1))
      (ν := volume.restrict (Ioo (0 : ℝ) 1)) (fun _ : ℝ => (1 : ℝ)) (fun σ => ksWh t σ / 2)
    simp only [one_mul] at this
    rw [this, MeasureTheory.integral_div]
    simp
  have e2 : ∫ β in Ioo (0 : ℝ) 1, (∫ w in Ioo (0 : ℝ) 1, ksDYmax β w * ksWh t β) =
      ∫ β in Ioo (0 : ℝ) 1, ksWh t β / 2 := by
    refine setIntegral_congr_fun measurableSet_Ioo fun β hβ => ?_
    rw [MeasureTheory.integral_mul_const, ksW_integral_ksDYmax hβ]
    ring
  rw [e1, e2, MeasureTheory.integral_div]
  ring

/-- The pointwise symmetry of the summed density under `σ ↦ 1 - σ`. -/
theorem ksW_ksWT_add_reflect {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) :
    ksWT t σ + ksWT t (1 - σ) = -96 * ksDmKer t σ := by
  have hA := (ksW_ksDA_pos ht hσ).ne'
  have hR : ksDA 1 t (1 - σ) = ksDA 1 t σ := by unfold ksDA; ring
  unfold ksWT ksWf ksWg ksWh ksDmKer
  rw [hR]
  rw [ksW_ksDA_one] at hA ⊢
  field_simp
  ring

/-- **The symmetric integral**: `∫₀¹ T = 12 D(t)`. -/
theorem ksW_integral_ksWT : ∫ σ in (0 : ℝ)..1, ksWT t σ = 12 * ksDm t := by
  obtain ⟨cf, cg, ch⟩ := ksW_continuousOn_ksWT ht
  have hT : IntervalIntegrable (ksWT t) volume 0 1 := by
    unfold ksWT
    exact ((ksW_intervalIntegrable cf).const_mul 2 |>.add (ksW_intervalIntegrable cg)).add
      (ksW_intervalIntegrable ch)
  have hT' : IntervalIntegrable (fun σ => ksWT t (1 - σ)) volume 0 1 := by
    have := (hT.comp_sub_left 1).symm
    simpa using this
  have hs : ∫ σ in (0 : ℝ)..1, ksWT t (1 - σ) = ∫ σ in (0 : ℝ)..1, ksWT t σ := by
    rw [intervalIntegral.integral_comp_sub_left (fun σ => ksWT t σ) 1]
    norm_num
  have hsum : ∫ σ in (0 : ℝ)..1, (ksWT t σ + ksWT t (1 - σ)) =
      ∫ σ in (0 : ℝ)..1, -96 * ksDmKer t σ := by
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [uIcc_of_le zero_le_one] at hσ
    exact ksW_ksWT_add_reflect ht hσ
  rw [intervalIntegral.integral_add hT hT', hs, intervalIntegral.integral_const_mul] at hsum
  unfold ksDm
  linarith

/-- **The `log M²` identity**: `2Δc₁(t) + Δc₁B(t) = 12 D(t)` for `t > -4`. -/
theorem ksW_log_coeff :
    2 * (ksUc1 1 t - ksUc1 1 0) + (ksUc1B 1 t - ksUc1B 1 0) = 12 * ksDm t := by
  obtain ⟨cf, cg, ch⟩ := ksW_continuousOn_ksWT ht
  have hf := ksW_intervalIntegrable cf
  have hg := ksW_intervalIntegrable cg
  have hh := ksW_intervalIntegrable ch
  rw [ksW_ksUc1_sub ht, ksW_ksUc1B_sub ht, ← ksW_integral_ksWT ht]
  simp only [← integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_of_le zero_le_one]
  unfold ksWT
  rw [intervalIntegral.integral_add ((hf.const_mul 2).add hg) hh,
    intervalIntegral.integral_add (hf.const_mul 2) hg, intervalIntegral.integral_const_mul]
  ring

end Coeff

end QED.ChainProof.SetAKS

end
