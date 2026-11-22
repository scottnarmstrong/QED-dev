/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKSSpec

/-!
# Set (a), stage D: the threshold terms in the velocity

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. The
node dispersion of the `VA` class (`ksW_ksUQ_sub_eq`) leaves a threshold term
`-C(x, σ) s/(s + T₀(σ))`, `T₀ = 1/(σ(1-σ))`. On the two halves of `(0, 1)` the substitution
`σ = (1 ∓ δ)/2` (so `T₀ = 4/(1-δ²)`) turns its `σ`-integral into a spectral integral in `δ`:

  `∫₀¹ g(σ) s/(s + T₀(σ)) dσ = ∫₀¹ ksSpecKer(s, δ) (1-δ²)/(4δ) (g((1-δ)/2) + g((1+δ)/2)) dδ`.

Main result:

* **`ksW_integral_threshold_delta`**.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology intervalIntegral

namespace QED.ChainProof.SetAKS

/-- The threshold kernel at the two preimages of the velocity `δ`. -/
theorem ksW_threshold_ker {s δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) (ε : ℝ) (hε : ε ^ 2 = 1) :
    s / (s + ((1 / 2 + ε * (δ / 2)) * (1 - (1 / 2 + ε * (δ / 2))))⁻¹) =
      ksSpecKer s δ * ((1 - δ ^ 2) / (2 * δ)) := by
  obtain ⟨h0, h1⟩ := hδ
  have hd : 0 < 1 - δ ^ 2 := by nlinarith
  have hp : (1 / 2 + ε * (δ / 2)) * (1 - (1 / 2 + ε * (δ / 2))) = (1 - δ ^ 2) / 4 := by
    linear_combination (-(δ ^ 2) / 4) * hε
  rw [hp, inv_div]
  unfold ksSpecKer
  have : δ ≠ 0 := h0.ne'
  have : 1 - δ ^ 2 ≠ 0 := hd.ne'
  field_simp

/-- **The threshold terms in the velocity**: for `F(σ) = g(σ) s/(s + T₀(σ))` integrable on
`(0, 1)`, `∫₀¹ F = ∫₀¹ ksSpecKer(s, δ) (1-δ²)/(4δ) (g((1-δ)/2) + g((1+δ)/2)) dδ`. -/
theorem ksW_integral_threshold_delta {g : ℝ → ℝ} (s : ℝ)
    (hg : IntervalIntegrable (fun σ => g σ * (s / (s + (σ * (1 - σ))⁻¹))) volume 0 1) :
    ∫ σ in (0 : ℝ)..1, g σ * (s / (s + (σ * (1 - σ))⁻¹)) =
      ∫ δ in (0 : ℝ)..1, ksSpecKer s δ * ((1 - δ ^ 2) / (4 * δ) *
        (g ((1 - δ) / 2) + g ((1 + δ) / 2))) := by
  set F : ℝ → ℝ := fun σ => g σ * (s / (s + (σ * (1 - σ))⁻¹)) with hF
  have h₁ : IntervalIntegrable F volume 0 (1 / 2) := by
    refine hg.mono_set ?_
    rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
    exact Icc_subset_Icc_right (by norm_num)
  have h₂ : IntervalIntegrable F volume (1 / 2) 1 := by
    refine hg.mono_set ?_
    rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
    exact Icc_subset_Icc_left (by norm_num)
  -- the two substitutions
  have e₁ : ∫ σ in (0 : ℝ)..1 / 2, F σ = (1 / 2) * ∫ δ in (0 : ℝ)..1, F (1 / 2 - δ / 2) := by
    rw [integral_comp_sub_div F (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
    ring
  have e₂ : ∫ σ in (1 / 2 : ℝ)..1, F σ = (1 / 2) * ∫ δ in (0 : ℝ)..1, F (1 / 2 + δ / 2) := by
    rw [integral_comp_add_div F (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
    ring
  -- integrability of the substituted halves
  have i₁ : IntervalIntegrable (fun δ => F (1 / 2 - δ / 2)) volume 0 1 := by
    have := (h₁.comp_sub_left (1 / 2)).symm.comp_mul_left (c := 1 / 2)
    norm_num at this
    convert this using 1
    funext δ
    congr 1
    ring
  have i₂ : IntervalIntegrable (fun δ => F (1 / 2 + δ / 2)) volume 0 1 := by
    have := (h₂.comp_add_right (1 / 2)).comp_mul_left (c := 1 / 2)
    norm_num at this
    convert this using 1
    funext δ
    congr 1
    ring
  rw [← integral_add_adjacent_intervals h₁ h₂, e₁, e₂, ← mul_add, ← integral_add i₁ i₂,
    ← intervalIntegral.integral_const_mul]
  have hne : ∀ᵐ δ ∂(volume : Measure ℝ), δ ≠ 1 := by
    rw [ae_iff]
    simp
  refine integral_congr_ae ?_
  filter_upwards [hne] with δ hne1 hδ
  rw [uIoc_of_le zero_le_one] at hδ
  have h1 : δ < 1 := hδ.2.lt_of_ne hne1
  have hδ' : δ ∈ Ioo (0 : ℝ) 1 := ⟨hδ.1, h1⟩
  have k₁ := ksW_threshold_ker (s := s) hδ' (-1) (by norm_num)
  have k₂ := ksW_threshold_ker (s := s) hδ' 1 (by norm_num)
  simp only [hF]
  rw [show 1 / 2 - δ / 2 = 1 / 2 + -1 * (δ / 2) by ring,
    show 1 / 2 + δ / 2 = 1 / 2 + 1 * (δ / 2) by ring, k₁, k₂,
    show (1 - δ) / 2 = 1 / 2 + -1 * (δ / 2) by ring,
    show (1 + δ) / 2 = 1 / 2 + 1 * (δ / 2) by ring]
  have : δ ≠ 0 := hδ.1.ne'
  field_simp
  ring

end QED.ChainProof.SetAKS

end
