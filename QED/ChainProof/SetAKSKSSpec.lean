/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKSDm
public import QED.ChainProof.SetAKSProfile

/-!
# R-KS, stage S: the target scaling form as one spectral integral

Helper level for the identification (R-KS) of the regulator limit of the frozen goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` with the Källén–Sabry function (the open
input `SetAKSFix e`). The target of `SetAKSFix e` is the scaling form
`decT ksG ksPhi ksKappa μ x s = (Π̂⁽⁴⁾(σ) - (3/4) log(x/μ²) D(σ))/(16π⁴)`, `σ = s/x`. Here it is
written as one once-subtracted dispersive integral in the velocity `δ`, over the **target
spectral density** `ρ_L(δ) = ρ⁽⁴⁾(δ) - (3/4) L ρ_D(δ)`, `L = log(x/μ²)`. Stage S of (R-KS) is the
statement that the summed spectral density of the model (stage D) is `ρ_L`.

Main results:

* `ksSpecKer`, `ksSpecRho`: the dispersive kernel `2δ/(1-δ²) · σ/(σ + 4/(1-δ²))` and `ρ_L`;
* `ksS_intervalIntegrable_ksKer`: the integrand of `piHat4` is integrable for every `σ > -4`;
* `ksS_piHat4_sub_ksDm_eq`: `Π̂⁽⁴⁾(σ) - (3/4) L D(σ) = ∫₀¹ ksSpecKer σ · ρ_L` for `σ > -4`;
* `ksS_decT_eq_spectral`: the target scaling form is that integral over `16π⁴`.
-/

@[expose] public section

open Real MeasureTheory Set intervalIntegral Filter

namespace QED.ChainProof.SetAKS

open QED.Chain QED.GradedProof.RPi4

/-- The once-subtracted dispersive kernel in the velocity `δ`:
`2δ/(1-δ²) · σ/(σ + 4/(1-δ²))` (`dt/t · σ/(σ + t)` at `t = 4/(1-δ²)`). -/
noncomputable def ksSpecKer (σ δ : ℝ) : ℝ :=
  2 * δ / (1 - δ ^ 2) * (σ / (σ + 4 / (1 - δ ^ 2)))

/-- **The target spectral density** `ρ_L(δ) = ρ⁽⁴⁾(δ) - (3/4) L ρ_D(δ)`. -/
noncomputable def ksSpecRho (L δ : ℝ) : ℝ :=
  ksRho δ - 3 / 4 * L * ksRhoDm δ

/-- The kernel is bounded on `[0, 1]` for `σ > -4`. -/
theorem ksS_abs_ksSpecKer_le {σ δ : ℝ} (hσ : -4 < σ) (hδ : δ ∈ Icc (0 : ℝ) 1) :
    |ksSpecKer σ δ| ≤ 2 * |σ| / min 4 (σ + 4) := by
  obtain ⟨h0, h1⟩ := hδ
  have hm : 0 < min 4 (σ + 4) := lt_min (by norm_num) (by linarith)
  rcases h1.lt_or_eq with h1 | rfl
  · have hd : 0 < 1 - δ ^ 2 := by nlinarith
    have hδ2 : δ ^ 2 ≤ 1 := by nlinarith
    have hden : min 4 (σ + 4) ≤ (1 - δ ^ 2) * σ + 4 := by
      rcases le_or_gt 0 σ with h | h
      · exact (min_le_left _ _).trans (by nlinarith)
      · exact (min_le_right _ _).trans (by nlinarith)
    have e : ksSpecKer σ δ = 2 * δ * σ / ((1 - δ ^ 2) * σ + 4) := by
      simp only [ksSpecKer]
      have : σ + 4 / (1 - δ ^ 2) = ((1 - δ ^ 2) * σ + 4) / (1 - δ ^ 2) := by
        field_simp
      rw [this]
      have : 0 < (1 - δ ^ 2) * σ + 4 := hm.trans_le hden
      field_simp
    have hp : 0 < (1 - δ ^ 2) * σ + 4 := hm.trans_le hden
    rw [e, abs_div, abs_of_pos hp, abs_mul, abs_mul, abs_of_nonneg h0, abs_two]
    calc 2 * δ * |σ| / ((1 - δ ^ 2) * σ + 4) ≤ 2 * |σ| / ((1 - δ ^ 2) * σ + 4) := by
          gcongr
          nlinarith [abs_nonneg σ]
      _ ≤ 2 * |σ| / min 4 (σ + 4) := by gcongr
  · simp only [ksSpecKer]
    norm_num
    positivity

theorem ksS_ksKer_eq (σ δ : ℝ) : ksKer σ δ = ksSpecKer σ δ * ksRho δ := by
  simp only [ksKer, ksSpecKer]
  ring

/-- **The integrand of `piHat4` is integrable for every `σ > -4`.** -/
theorem ksS_intervalIntegrable_ksKer {σ : ℝ} (hσ : -4 < σ) :
    IntervalIntegrable (ksKer σ) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Integrable.mono' (integrableOn_abs_ksRho.const_mul (2 * |σ| / min 4 (σ + 4)))
    (aestronglyMeasurable_ksKer σ) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun δ hδ => ?_)
  rw [Real.norm_eq_abs, ksS_ksKer_eq, abs_mul]
  exact mul_le_mul_of_nonneg_right (ksS_abs_ksSpecKer_le hσ (Ioc_subset_Icc_self hδ))
    (abs_nonneg _)

theorem ksS_intervalIntegrable_ksDmSpec {σ : ℝ} (hσ : -4 < σ) :
    IntervalIntegrable (fun δ => ksSpecKer σ δ * ksRhoDm δ) volume 0 1 := by
  have h := (ksS_intervalIntegrable_ksDmDel hσ (a := 0) (b := 1) (by norm_num)
    (by norm_num)).neg
  refine h.congr fun δ hδ => ?_
  rw [uIoc_of_le zero_le_one] at hδ
  rw [Pi.neg_apply, ← ksS_spectral_ksRhoDm_eq hδ]
  simp only [ksSpecKer]
  ring

/-- **`Π̂⁽⁴⁾(σ) - (3/4) L D(σ)` as one spectral integral** over `ρ_L`, for `σ > -4`. -/
theorem ksS_piHat4_sub_ksDm_eq {σ : ℝ} (hσ : -4 < σ) (L : ℝ) :
    piHat4 σ - 3 / 4 * L * ksDm σ = ∫ δ in (0 : ℝ)..1, ksSpecKer σ δ * ksSpecRho L δ := by
  have hD : ksDm σ = ∫ δ in (0 : ℝ)..1, ksSpecKer σ δ * ksRhoDm δ := by
    rw [ksS_ksDm_eq_spectral hσ]
    refine integral_congr fun δ _ => ?_
    simp only [ksSpecKer]
    ring
  have hP : piHat4 σ = ∫ δ in (0 : ℝ)..1, ksSpecKer σ δ * ksRho δ := by
    rw [piHat4_eq_integral_ksKer]
    exact integral_congr fun δ _ => ksS_ksKer_eq σ δ
  have hI : IntervalIntegrable (fun δ => ksSpecKer σ δ * ksRho δ) volume 0 1 :=
    (ksS_intervalIntegrable_ksKer hσ).congr fun δ _ => ksS_ksKer_eq σ δ
  have e : (fun δ => ksSpecKer σ δ * ksSpecRho L δ) =
      fun δ => ksSpecKer σ δ * ksRho δ - 3 / 4 * L * (ksSpecKer σ δ * ksRhoDm δ) := by
    funext δ
    simp only [ksSpecRho]
    ring
  rw [e, integral_sub hI ((ksS_intervalIntegrable_ksDmSpec hσ).const_mul _),
    intervalIntegral.integral_const_mul, hD, hP]

/-- **The target scaling form of `SetAKSFix` as one spectral integral**: for `x > 0` and
`s/x > -4`, `decT ksG ksPhi ksKappa μ x s = (1/16π⁴) ∫₀¹ ksSpecKer(s/x) ρ_L` with
`L = log(x/μ²)`. -/
theorem ksS_decT_eq_spectral {μ x s : ℝ} (hs : -4 < s / x) :
    decT ksG ksPhi ksKappa μ x s =
      (((∫ δ in (0 : ℝ)..1, ksSpecKer (s / x) δ * ksSpecRho (log (x / μ ^ 2)) δ) /
        (16 * π ^ 4) : ℝ) : ℂ) := by
  rw [← ksS_piHat4_sub_ksDm_eq hs]
  simp only [decT, ksG, ksPhi, ksKappa]
  push_cast
  ring

end QED.ChainProof.SetAKS

end
