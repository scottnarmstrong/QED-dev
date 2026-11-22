/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWAsmA

/-!
# Set (a), stage D: the `VA` class against the full density

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. Both
spectral integrands of `ksW_VA_dispersion` are integrable on `(0, 1)`: the threshold part by the
two substitutions `σ = (1 ∓ δ)/2`, the node part by the change of variables `T = 4/(1-δ²)` from
the integrable exchanged density on `T > 4`. Hence

  `ksUF 1 s - ksUF 1 0 = ∫₀¹ ksSpecKer(s, δ) ρ_A(δ) dδ`,   `ρ_A = ksWRhoA`.

Main results:

* `ksW_intervalIntegrable_threshold_delta`, `ksW_intervalIntegrable_VA_node`,
  `ksW_intervalIntegrable_VA_thr`;
* **`ksW_VA_dispersion_rhoA`**.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.ChainProof.SetAKS

/-- The velocity form of a threshold term is integrable when the `σ` form is. -/
theorem ksW_intervalIntegrable_threshold_delta {g : ℝ → ℝ} (s : ℝ)
    (hg : IntervalIntegrable (fun σ => g σ * (s / (s + (σ * (1 - σ))⁻¹))) volume 0 1) :
    IntervalIntegrable (fun δ => ksSpecKer s δ * ((1 - δ ^ 2) / (4 * δ) *
      (g ((1 - δ) / 2) + g ((1 + δ) / 2)))) volume 0 1 := by
  set F : ℝ → ℝ := fun σ => g σ * (s / (s + (σ * (1 - σ))⁻¹)) with hF
  have h₁ : IntervalIntegrable F volume 0 (1 / 2) := by
    refine hg.mono_set ?_
    rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
    exact Icc_subset_Icc_right (by norm_num)
  have h₂ : IntervalIntegrable F volume (1 / 2) 1 := by
    refine hg.mono_set ?_
    rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
    exact Icc_subset_Icc_left (by norm_num)
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
  have hi := (i₁.add i₂).const_mul (1 / 2)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at hi ⊢
  refine hi.congr_fun (fun δ hδ => ?_) measurableSet_Ioo
  have k₁ := ksW_threshold_ker (s := s) hδ (-1) (by norm_num)
  have k₂ := ksW_threshold_ker (s := s) hδ 1 (by norm_num)
  simp only [hF]
  rw [show 1 / 2 - δ / 2 = 1 / 2 + -1 * (δ / 2) by ring,
    show 1 / 2 + δ / 2 = 1 / 2 + 1 * (δ / 2) by ring, k₁, k₂,
    show (1 - δ) / 2 = 1 / 2 + -1 * (δ / 2) by ring,
    show (1 + δ) / 2 = 1 / 2 + 1 * (δ / 2) by ring]
  have : δ ≠ 0 := hδ.1.ne'
  field_simp
  ring

/-- The pointwise form of the velocity substitution of a once-subtracted dispersive integrand. -/
theorem ksW_ksDT_jac {s r δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    |8 * 1 ^ 2 * δ / (1 - δ ^ 2) ^ 2| * (r / ksDT 1 δ * (s / (s + ksDT 1 δ))) =
      ksSpecKer s δ * r := by
  have hd : 0 < 1 - δ ^ 2 := by nlinarith [hδ.1, hδ.2]
  rw [abs_of_nonneg (by have := hδ.1; positivity)]
  unfold ksSpecKer ksDT
  simp only [one_pow, mul_one]
  generalize s / (s + 4 / (1 - δ ^ 2)) = K
  field_simp
  ring

/-- **The `VA` threshold integrand in the velocity is integrable.** -/
theorem ksW_intervalIntegrable_VA_thr {s : ℝ} (hs : -4 < s) :
    IntervalIntegrable (fun δ => ksSpecKer s δ * ksWRhoAc δ) volume 0 1 := by
  set ν := (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)) with hν
  have iQs := ksU_integrable_ksUQ one_pos (by norm_num; linarith : -(4 * (1 : ℝ) ^ 2) < s)
  have iQ0 := ksU_integrable_ksUQ one_pos (by norm_num : -(4 * (1 : ℝ) ^ 2) < 0)
  have hae : ∀ᵐ z ∂ν, z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
    rw [hν, Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  have hint := ksW_integrable_VA_joint hs
  set J : ℝ × ℝ → ℝ := fun z => ∫ T in Ioi (ksWt0 z.2), ksWnA z.1 z.2 T * (s / (T * (s + T)))
    with hJ
  have hJeq : ∀ z, ∫ T, ksWjA s (z, T) ∂(volume.restrict (Ioi 4)) = J z := fun z => by
    rw [show (fun T => ksWjA s (z, T)) = _ from ksW_ksWjA_slice s z,
      integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      Ioi_inter_Ioi, sup_eq_left.2 (ksW_four_le_ksWt0 z.2)]
  have iJ : Integrable J ν := by
    have := hint.integral_prod_left
    simp only [hJeq] at this
    exact this
  set C : ℝ × ℝ → ℝ := fun z => ksWCA z.1 z.2 * (s / (s + (z.2 * (1 - z.2))⁻¹)) with hC
  have iC : Integrable C ν := by
    refine (iJ.sub (iQs.sub iQ0)).congr ?_
    filter_upwards [hae] with z hz
    simp only [Pi.sub_apply, ksW_ksUQ_sub_eq hz.1 hz.2 hs, hJ, hC, ksW_ksWt0_eq hz.2]
    ring
  set g : ℝ → ℝ := fun σ => ∫ x in Ioo (0 : ℝ) 1, ksWCA x σ with hg
  have hgi : IntervalIntegrable (fun σ => g σ * (s / (s + (σ * (1 - σ))⁻¹))) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    have := iC.integral_prod_right
    refine this.congr (Eventually.of_forall fun σ => ?_)
    simp only [hC, hg]
    rw [integral_mul_const]
  exact ksW_intervalIntegrable_threshold_delta s hgi

/-- **The `VA` node integrand in the velocity is integrable.** -/
theorem ksW_intervalIntegrable_VA_node {s : ℝ} (hs : -4 < s) :
    IntervalIntegrable (fun δ => ksSpecKer s δ * ksWRhoAn δ) volume 0 1 := by
  set ν := (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)) with hν
  have hint := ksW_integrable_VA_joint hs
  have hint₁ := (ksW_integrable_VA_joint (s := 1) (by norm_num)).prod_left_ae
  -- the exchanged density times the kernel is integrable on `T > 4`
  have hR : IntegrableOn (fun t => ksWRhoAn (√(1 - 4 / t)) / t * (s / (s + t)))
      (Ioi (4 * 1 ^ 2)) := by
    rw [show (4 : ℝ) * 1 ^ 2 = 4 by norm_num]
    refine hint.integral_prod_right.congr ?_
    filter_upwards [hint₁, ae_restrict_mem measurableSet_Ioi] with T hT hT4
    have hT4' : 4 < T := hT4
    have hT0 : 0 < T := by linarith
    have hk : 1 / (T * (1 + T)) ≠ 0 := by positivity
    have hi : Integrable (fun z : ℝ × ℝ => {z : ℝ × ℝ | ksWt0 z.2 < T}.indicator
        (fun z => ksWnA z.1 z.2 T) z) ν := by
      refine (hT.mul_const (1 / (T * (1 + T)))⁻¹).congr (Eventually.of_forall fun z => ?_)
      simp only [ksWjA, indicator, mem_ofPred_eq]
      split_ifs
      · field_simp
      · simp
    have e : (fun z => ksWjA s (z, T)) = fun z => {z : ℝ × ℝ | ksWt0 z.2 < T}.indicator
        (fun z => ksWnA z.1 z.2 T) z * (s / (T * (s + T))) := by
      funext z
      simp only [ksWjA, indicator, mem_ofPred_eq]
      split_ifs <;> simp
    rw [e, integral_mul_const, ksW_rhoT_eq hT4' hi]
    have : s + T ≠ 0 := by linarith
    field_simp
  rw [← ksD_image_ksDT one_pos, integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioo (fun δ hδ => (ksD_hasDerivAt_ksDT 1 hδ).hasDerivWithinAt)
    (ksD_injOn_ksDT one_pos)] at hR
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  refine hR.congr_fun (fun δ hδ => ?_) measurableSet_Ioo
  simp only [smul_eq_mul]
  rw [ksW_ksDT_jac hδ, ksW_ksWRhoAn_ksDT (Ioo_subset_Icc_self hδ)]

/-- **The dispersive form of the `VA` class against `ρ_A`** (unit mass, `s > -4`):
`ksUF 1 s - ksUF 1 0 = ∫₀¹ ksSpecKer(s, δ) ρ_A(δ) dδ`. -/
theorem ksW_VA_dispersion_rhoA {s : ℝ} (hs : -4 < s) :
    ksUF 1 s - ksUF 1 0 = ∫ δ in (0 : ℝ)..1, ksSpecKer s δ * ksWRhoA δ := by
  rw [ksW_VA_dispersion hs, ← intervalIntegral.integral_sub (ksW_intervalIntegrable_VA_node hs)
    (ksW_intervalIntegrable_VA_thr hs)]
  simp only [ksWRhoA, mul_sub]

end QED.ChainProof.SetAKS

end
