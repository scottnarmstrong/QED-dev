/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWAsmInt
public import QED.ChainProof.SetAKSKWAsmDef
public import QED.ChainProof.SetAKSKWSwap
public import QED.ChainProof.SetAKSKWHalf

/-!
# Set (a), stage D: the dispersive form of the `VA` class

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. The
subtracted `VA` finite part at unit mass has the spectral form

  `ksUF 1 s - ksUF 1 0 = ∫₀¹ ksSpecKer(s, δ) ρ_A^n(δ) dδ - ∫₀¹ ksSpecKer(s, δ) ρ_A^c(δ) dδ`

(`s > -4`), with the node part `ρ_A^n = ksWRhoAn` and the threshold part `ρ_A^c = ksWRhoAc`
of `ρ_A = ksWRhoA`. Proof: integrate the node dispersion `ksW_ksUQ_sub_eq` over the unit square;
the threshold term goes to the velocity by `ksW_integral_threshold_delta`, the density term by
the exchange `ksW_integral_dispersion_swap` (joint integrability `ksW_integrable_VA_joint`) and
`ksD_dispersion_eq_delta`. At a.e. `T > 4` the exchanged density is the iterated integral over
`x ∈ (0, 1)`, `σ ∈ ((1-δ)/2, (1+δ)/2)`, `δ = √(1 - 4/T)`.

Main results:

* `ksW_threshold_iff`: `T₀(σ) < T` iff `σ ∈ ((1-δ)/2, (1+δ)/2)`;
* **`ksW_VA_dispersion`**.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.ChainProof.SetAKS

/-- The nodes above threshold: `T₀(σ) < T` iff `|2σ - 1| < δ`, `δ = √(1 - 4/T)`. -/
theorem ksW_threshold_iff {σ T : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) (hT : 4 < T) :
    (σ * (1 - σ))⁻¹ < T ↔
      σ ∈ Ioo ((1 - √(1 - 4 / T)) / 2) ((1 + √(1 - 4 / T)) / 2) := by
  have hp : 0 < σ * (1 - σ) := mul_pos hσ.1 (by linarith [hσ.2])
  have hT0 : 0 < T := by linarith
  have h4 : 0 ≤ 1 - 4 / T := by
    rw [sub_nonneg, div_le_one hT0]
    linarith
  set δ := √(1 - 4 / T) with hδ
  have hδ0 : 0 ≤ δ := sqrt_nonneg _
  have hδ2 : δ ^ 2 = 1 - 4 / T := sq_sqrt h4
  rw [inv_lt_comm₀ hp hT0]
  have e : (2 * σ - 1) ^ 2 = 1 - 4 * (σ * (1 - σ)) := by ring
  constructor
  · intro h
    have hlt : (2 * σ - 1) ^ 2 < δ ^ 2 := by
      rw [e, hδ2, show 4 / T = 4 * T⁻¹ by ring]
      linarith
    have := abs_lt_of_sq_lt_sq hlt hδ0
    rw [abs_lt] at this
    constructor <;> linarith
  · intro h
    have hlt : (2 * σ - 1) ^ 2 < δ ^ 2 := sq_lt_sq' (by linarith [h.1]) (by linarith [h.2])
    rw [e, hδ2, show 4 / T = 4 * T⁻¹ by ring] at hlt
    linarith

/-- The node part of the `VA` density as a function of `T`. -/
theorem ksW_ksWRhoAn_ksDT {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) :
    ksWRhoAn (√(1 - 4 / ksDT 1 δ)) = ksWRhoAn δ := by
  have h : 1 - 4 / ksDT 1 δ = δ ^ 2 := by
    unfold ksDT
    rcases eq_or_ne (1 - δ ^ 2) 0 with h | h
    · rw [h, div_zero, div_zero]
      linarith
    · field_simp
      ring
  rw [h, sqrt_sq hδ.1]

/-- The exchanged density at `T > 4` is the iterated threshold integral, when the slice is
integrable. -/
theorem ksW_rhoT_eq {T : ℝ} (hT : 4 < T)
    (hi : Integrable (fun z : ℝ × ℝ => {z : ℝ × ℝ | ksWt0 z.2 < T}.indicator
      (fun z => ksWnA z.1 z.2 T) z)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) :
    ∫ z, {z : ℝ × ℝ | ksWt0 z.2 < T}.indicator (fun z => ksWnA z.1 z.2 T) z
      ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) =
      ksWRhoAn (√(1 - 4 / T)) := by
  have hT0 : 0 < T := by linarith
  have h4 : 0 ≤ 1 - 4 / T := by
    rw [sub_nonneg, div_le_one hT0]
    linarith
  set δ := √(1 - 4 / T) with hδ
  have hδ1 : δ ≤ 1 := by
    rw [hδ, sqrt_le_one]
    have : 0 < 4 / T := by positivity
    linarith
  have hDT : ksDT 1 δ = T := by
    have hδ2 : δ ^ 2 = 1 - 4 / T := sq_sqrt h4
    unfold ksDT
    rw [hδ2]
    field_simp
    ring
  rw [integral_prod _ hi, ksWRhoAn, hDT]
  refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
  have hsub : Ioo ((1 - δ) / 2) ((1 + δ) / 2) ⊆ Ioo (0 : ℝ) 1 := fun σ hσ =>
    ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hres : ∫ σ in Ioo ((1 - δ) / 2) ((1 + δ) / 2), ksWnA x σ T =
      ∫ σ in Ioo (0 : ℝ) 1,
        (Ioo ((1 - δ) / 2) ((1 + δ) / 2)).indicator (fun σ => ksWnA x σ T) σ := by
    rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
      inter_eq_left.2 hsub]
  rw [hres]
  refine setIntegral_congr_fun measurableSet_Ioo fun σ hσ => ?_
  have hiff := ksW_threshold_iff hσ hT
  rw [← ksW_ksWt0_eq hσ] at hiff
  by_cases h : ksWt0 σ < T
  · rw [indicator_of_mem (show (x, σ) ∈ {z : ℝ × ℝ | ksWt0 z.2 < T} from h),
      indicator_of_mem (hiff.1 h)]
  · rw [indicator_of_notMem (show (x, σ) ∉ {z : ℝ × ℝ | ksWt0 z.2 < T} from h),
      indicator_of_notMem (fun h' => h (hiff.2 h'))]

/-- **The dispersive form of the `VA` class** (unit mass, `s > -4`). -/
theorem ksW_VA_dispersion {s : ℝ} (hs : -4 < s) :
    ksUF 1 s - ksUF 1 0 = (∫ δ in (0 : ℝ)..1, ksSpecKer s δ * ksWRhoAn δ) -
      ∫ δ in (0 : ℝ)..1, ksSpecKer s δ * ksWRhoAc δ := by
  set ν := (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)) with hν
  have iQs := ksU_integrable_ksUQ one_pos (by norm_num; linarith : -(4 * (1 : ℝ) ^ 2) < s)
  have iQ0 := ksU_integrable_ksUQ one_pos (by norm_num : -(4 * (1 : ℝ) ^ 2) < 0)
  have hF : ksUF 1 s - ksUF 1 0 = ∫ p, (ksUQ 1 s p.1 p.2 - ksUQ 1 0 p.1 p.2) ∂ν := by
    rw [ksUF, ksUF, ← integral_prod _ iQs, ← integral_prod _ iQ0, integral_sub iQs iQ0]
  have hae : ∀ᵐ z ∂ν, z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
    rw [hν, Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  have hint := ksW_integrable_VA_joint hs
  -- the density term at each node
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
  have hnode : ∀ᵐ z ∂ν, ksUQ 1 s z.1 z.2 - ksUQ 1 0 z.1 z.2 = -C z + J z := by
    filter_upwards [hae] with z hz
    rw [ksW_ksUQ_sub_eq hz.1 hz.2 hs, hJ, hC]
    simp only [ksW_ksWt0_eq hz.2]
    ring
  have iC : Integrable C ν := by
    refine (iJ.sub (iQs.sub iQ0)).congr ?_
    filter_upwards [hnode] with z hz
    simp only [Pi.sub_apply, hz]
    ring
  have hadd := integral_add iC.neg iJ
  simp only [Pi.neg_apply] at hadd
  rw [hF, integral_congr_ae hnode, hadd, integral_neg]
  -- the threshold term
  set g : ℝ → ℝ := fun σ => ∫ x in Ioo (0 : ℝ) 1, ksWCA x σ with hg
  have hCg : ∫ z, C z ∂ν = ∫ σ in (0 : ℝ)..1, g σ * (s / (s + (σ * (1 - σ))⁻¹)) := by
    rw [hν, integral_prod_symm _ iC, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun σ _ => ?_
    simp only [hC, hg]
    rw [integral_mul_const]
  have hgi : IntervalIntegrable (fun σ => g σ * (s / (s + (σ * (1 - σ))⁻¹))) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    have := iC.integral_prod_right
    refine this.congr (Eventually.of_forall fun σ => ?_)
    simp only [hC, hg]
    rw [integral_mul_const]
  rw [hCg, ksW_integral_threshold_delta s hgi]
  -- the density term
  have hswap := ksW_integral_dispersion_swap (ν := ν) (n := fun z T => ksWnA z.1 z.2 T)
    (t₀ := fun z => ksWt0 z.2) (s := s) (c := 4) (fun z => ksW_four_le_ksWt0 z.2) hint
  have hJ' : ∫ z, J z ∂ν = ∫ T in Ioi 4,
      (∫ z, {z : ℝ × ℝ | ksWt0 z.2 < T}.indicator (fun z => ksWnA z.1 z.2 T) z ∂ν) *
        (s / (T * (s + T))) := hswap
  -- a.e. `T`, the exchanged density is the iterated integral
  have hint₁ := (ksW_integrable_VA_joint (s := 1) (by norm_num)).prod_left_ae
  have hρ : ∀ᵐ T ∂(volume.restrict (Ioi (4 : ℝ))),
      (∫ z, {z : ℝ × ℝ | ksWt0 z.2 < T}.indicator (fun z => ksWnA z.1 z.2 T) z ∂ν) *
        (s / (T * (s + T))) = ksWRhoAn (√(1 - 4 / T)) / T * (s / (s + T)) := by
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
    rw [ksW_rhoT_eq hT4' hi]
    have : s + T ≠ 0 := by linarith
    field_simp
  rw [hJ', integral_congr_ae hρ]
  have hD := ksD_dispersion_eq_delta one_pos (fun t => ksWRhoAn (√(1 - 4 / t))) s
  simp only [one_pow, mul_one, div_one] at hD
  rw [hD]
  have hcongr : ∫ δ in (0 : ℝ)..1, ksSpecKer s δ * ksWRhoAn (√(1 - 4 / ksDT 1 δ)) =
      ∫ δ in (0 : ℝ)..1, ksSpecKer s δ * ksWRhoAn δ := by
    refine intervalIntegral.integral_congr fun δ hδ => ?_
    rw [uIcc_of_le zero_le_one] at hδ
    simp only [ksW_ksWRhoAn_ksDT hδ]
  rw [hcongr]
  simp only [ksWRhoAc]
  ring

end QED.ChainProof.SetAKS

end
