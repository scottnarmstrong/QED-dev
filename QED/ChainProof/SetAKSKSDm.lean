/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSMis

/-!
# R-KS, stage S: the spectral density of the mismatch profile

Helper level for the identification (R-KS) of the regulator limit of the frozen goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` with the Källén–Sabry function (the open
input `SetAKSFix e`). The mismatch profile `D(σ) = M ∂_M Π̂₂(s/M²)` (`ksDm`) is written in the
same once-subtracted dispersive form as `QED.Chain.piHat4`, in the velocity `δ` with
`t = 4/(1-δ²)` and `dt/t = 2δ dδ/(1-δ²)`. Its spectral density is
`ρ_D(δ) = -(1-δ²)²/(2δ) = -2 t ∂_t ρ₂`, with `ρ₂(δ) = δ(1-δ²/3)/2` the one-loop density.

The proof is the substitution `t(1-t) = (1-δ²)/4`, i.e. `δ = 1 - 2t`, in the Feynman-parameter
integral of `ksDm`, which gives `D(σ) = -∫₀¹ (1-δ²) σ/(σ + 4/(1-δ²)) dδ`.

Main results:

* `ksRhoDm`: the spectral density `ρ_D`;
* `ksS_ksDm_eq_integral`: `D(σ) = -∫₀¹ (1-δ²) σ/(σ + 4/(1-δ²)) dδ` for `σ > -4`;
* `ksS_ksDm_eq_spectral`: `D(σ) = ∫₀¹ 2δ/(1-δ²) ρ_D(δ) σ/(σ + 4/(1-δ²)) dδ` for `σ > -4`.
-/

@[expose] public section

open Real MeasureTheory Set intervalIntegral

namespace QED.ChainProof.SetAKS

/-- **The spectral density of the mismatch profile** `ρ_D(δ) = -(1-δ²)²/(2δ)`. -/
noncomputable def ksRhoDm (δ : ℝ) : ℝ :=
  -((1 - δ ^ 2) ^ 2 / (2 * δ))

/-- The integrand of `ksDm` after the substitution `δ = 1 - 2t`. -/
noncomputable def ksDmDel (σ δ : ℝ) : ℝ :=
  (1 - δ ^ 2) * (σ / (σ + 4 / (1 - δ ^ 2)))

/-- The denominator `1 + t(1-t)σ` is positive on `[0, 1]` for `σ > -4`. -/
theorem ksS_den_pos {σ t : ℝ} (hσ : -4 < σ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < 1 + t * (1 - t) * σ := by
  obtain ⟨h0, h1⟩ := ht
  have ha : 0 ≤ t * (1 - t) := mul_nonneg h0 (by linarith)
  have ha' : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
  rcases le_or_gt 0 σ with h | h
  · have := mul_nonneg ha h
    linarith
  · nlinarith [mul_le_mul_of_nonneg_left ha' (by linarith : (0 : ℝ) ≤ -σ)]

/-- The kernel identity behind the substitution `δ = 1 - 2t`:
`4 ksDmKer σ t = ksDmDel σ (1 - 2t)`. -/
theorem ksS_ksDmKer_eq {σ t : ℝ} (hσ : -4 < σ) (ht : t ∈ Icc (0 : ℝ) 1) :
    4 * ksDmKer σ t = ksDmDel σ (1 - 2 * t) := by
  have hd := ksS_den_pos hσ ht
  have e1 : 1 - (1 - 2 * t) ^ 2 = 4 * (t * (1 - t)) := by ring
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    simp [ksDmKer, ksDmDel]
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · subst h1
    simp [ksDmKer, ksDmDel]
    norm_num
  have hp : 0 < t * (1 - t) := mul_pos h0 (by linarith)
  simp only [ksDmKer, ksDmDel]
  rw [e1]
  have hden : σ + 4 / (4 * (t * (1 - t))) = (1 + t * (1 - t) * σ) / (t * (1 - t)) := by
    field_simp
    ring
  rw [hden]
  field_simp

theorem ksS_continuousOn_ksDmKer {σ : ℝ} (hσ : -4 < σ) :
    ContinuousOn (ksDmKer σ) (Icc 0 1) := by
  refine ContinuousOn.mul (by fun_prop) (ContinuousOn.div continuousOn_const (by fun_prop)
    fun t ht => (ksS_den_pos hσ ht).ne')

/-- `ksDmDel σ` is continuous on `[-1, 1]` for `σ > -4` (it equals `4 ksDmKer σ ((1-δ)/2)`). -/
theorem ksS_ksDmDel_eq {σ δ : ℝ} (hσ : -4 < σ) (hδ : δ ∈ Icc (-1 : ℝ) 1) :
    ksDmDel σ δ = 4 * ksDmKer σ ((1 - δ) / 2) := by
  have ht : (1 - δ) / 2 ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨h0, h1⟩ := hδ
    constructor <;> linarith
  rw [ksS_ksDmKer_eq hσ ht]
  congr 1
  ring

theorem ksS_intervalIntegrable_ksDmDel {σ a b : ℝ} (hσ : -4 < σ) (ha : a ∈ Icc (-1 : ℝ) 1)
    (hb : b ∈ Icc (-1 : ℝ) 1) : IntervalIntegrable (ksDmDel σ) volume a b := by
  have hsub : uIcc a b ⊆ Icc (-1 : ℝ) 1 := Set.uIcc_subset_Icc ha hb
  have hc : ContinuousOn (fun δ => 4 * ksDmKer σ ((1 - δ) / 2)) (Icc (-1 : ℝ) 1) := by
    refine continuousOn_const.mul ((ksS_continuousOn_ksDmKer hσ).comp (by fun_prop) ?_)
    intro δ hδ
    obtain ⟨h0, h1⟩ := hδ
    constructor <;> linarith
  exact ((hc.mono hsub).congr fun δ hδ => ksS_ksDmDel_eq hσ (hsub hδ)).intervalIntegrable

theorem ksS_ksDmDel_neg (σ δ : ℝ) : ksDmDel σ (-δ) = ksDmDel σ δ := by
  simp [ksDmDel]

/-- **`D(σ) = -∫₀¹ (1-δ²) σ/(σ + 4/(1-δ²)) dδ`** for `σ > -4`. -/
theorem ksS_ksDm_eq_integral {σ : ℝ} (hσ : -4 < σ) :
    ksDm σ = -∫ δ in (0 : ℝ)..1, ksDmDel σ δ := by
  have h1 : ∫ t in (0 : ℝ)..1, 4 * ksDmKer σ t = ∫ t in (0 : ℝ)..1, ksDmDel σ (1 - 2 * t) := by
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    exact ksS_ksDmKer_eq hσ ht
  have h2 : ∫ t in (0 : ℝ)..1, ksDmDel σ (1 - 2 * t) =
      (1 / 2) * ∫ δ in (-1 : ℝ)..1, ksDmDel σ δ := by
    have := intervalIntegral.integral_comp_sub_mul (f := ksDmDel σ) (a := 0) (b := 1)
      (by norm_num : (2 : ℝ) ≠ 0) 1
    rw [this]
    norm_num
  have h3 : ∫ δ in (-1 : ℝ)..1, ksDmDel σ δ = 2 * ∫ δ in (0 : ℝ)..1, ksDmDel σ δ := by
    have hm1 : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
    have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
    have hp1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
    rw [← integral_add_adjacent_intervals (b := 0)
      (ksS_intervalIntegrable_ksDmDel hσ hm1 h0) (ksS_intervalIntegrable_ksDmDel hσ h0 hp1)]
    have hneg : ∫ δ in (-1 : ℝ)..0, ksDmDel σ δ = ∫ δ in (0 : ℝ)..1, ksDmDel σ δ := by
      have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) (ksDmDel σ)
      simpa [ksS_ksDmDel_neg] using this.symm
    rw [hneg]
    ring
  have h4 : ∫ t in (0 : ℝ)..1, ksDmKer σ t = (1 / 4) * ∫ δ in (0 : ℝ)..1, ksDmDel σ δ := by
    have h := h1
    rw [intervalIntegral.integral_const_mul, h2, h3] at h
    linarith
  rw [ksDm, h4]
  ring

/-- The spectral integrand of `ρ_D` agrees with `-ksDmDel` on `(0, 1]`. -/
theorem ksS_spectral_ksRhoDm_eq {σ δ : ℝ} (hδ : δ ∈ Ioc (0 : ℝ) 1) :
    2 * δ / (1 - δ ^ 2) * ksRhoDm δ * (σ / (σ + 4 / (1 - δ ^ 2))) = -ksDmDel σ δ := by
  obtain ⟨h0, h1⟩ := hδ
  rcases h1.lt_or_eq with h1 | rfl
  · have hd : 0 < 1 - δ ^ 2 := by nlinarith
    simp only [ksRhoDm, ksDmDel]
    field_simp
  · simp [ksRhoDm, ksDmDel]

/-- **The dispersive form of the mismatch profile**: for `σ > -4`,
`D(σ) = ∫₀¹ 2δ/(1-δ²) ρ_D(δ) σ/(σ + 4/(1-δ²)) dδ`. -/
theorem ksS_ksDm_eq_spectral {σ : ℝ} (hσ : -4 < σ) :
    ksDm σ = ∫ δ in (0 : ℝ)..1,
      2 * δ / (1 - δ ^ 2) * ksRhoDm δ * (σ / (σ + 4 / (1 - δ ^ 2))) := by
  rw [ksS_ksDm_eq_integral hσ, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun δ hδ => ?_)
  rw [uIoc_of_le zero_le_one] at hδ
  exact (ksS_spectral_ksRhoDm_eq hδ).symm

end QED.ChainProof.SetAKS

end
