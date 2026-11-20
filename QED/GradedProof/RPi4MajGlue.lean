/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajRay

/-!
# (R-Π₄) step L10: glue and a variant assembly

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10.

* `maj_asmFaceIds_of_decFaceGen`: the generic face-limit identity `DecFaceGen` gives the
  face-limit identities `AsmFaceIds` at the fermion regulators of the frozen statement;
* `maj_asmMajorant_of_gen`: `maj_asmMajorant_of` without the hypothesis `AsmFaceIds`;
* `MajLimLip4 e`: a scale-Lipschitz bound for the photon limit `asmPolLim` at the configuration
  `decCfg 1 4` itself (no uniformity in the photon pair), the weaker replacement of `MajRayLip`;
* `maj_growT_of_ray_lim`: `MajGrowT` from `MajRayVal` and `MajLimLip4` at `decCfg 1 4`;
* `maj_asmMajorant_of_lim`: the assembly with `MajLimLip4` in place of `MajRayLip`.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

section Glue

variable {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ)

/-- **`DecFaceGen` gives `AsmFaceIds`**: the flavours of the frozen statement have masses at
least `m`, an idempotent representative map and the two Pauli–Villars conditions per block. -/
theorem maj_asmFaceIds_of_decFaceGen (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hF : DecFaceGen P₀.e) : AsmFaceIds P₀ mH := by
  intro M₁ M₂ c₁ c₂ hM₁ hM₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ hcH₁ hcH₂ c s hc hs hsc
  exact hF _ (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) leptonRep P₀.m hm
    (le_leptonFlavors_mass (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ) (heavyH mH MH₁ MH₂ cH₁ cH₂) hM₁ hM₂
      hmH hMH₁ hMH₂)
    leptonRep_idem
    (leptonFlavors_blockPV₁ (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ) (heavyH mH MH₁ MH₂ cH₁ cH₂) hc₁
      hcH₁)
    (leptonFlavors_blockPV₂ (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ) (heavyH mH MH₁ MH₂ cH₁ cH₂) hc₂
      hcH₂)
    c s (by linarith) hs hsc

end Glue

/-- **The scale-Lipschitz bound of the photon limit at `decCfg 1 4`**:
`‖Π(s) - Π(s')‖ ≤ K w(s) (s - s')/s'` for `0 < s' ≤ s`, where `Π = asmPolLim (decCfg 1 4)`. -/
def MajLimLip4 (e : ℝ) : Prop :=
  ∃ K : ℝ, ∀ s s' : ℝ, 0 < s' → s' ≤ s →
    ‖asmPolLim (decCfg 1 4) (fun _ => 0) e s - asmPolLim (decCfg 1 4) (fun _ => 0) e s'‖ ≤
      K * majW s * ((s - s') / s')

/-- **(L10 input) `MajGrowT` from the value bound uniform in the photon pair and the
scale-Lipschitz bound of the photon limit**, at the configuration `decCfg 1 4`. -/
theorem maj_growT_of_ray_lim (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e)
    (hV : MajRayVal (decCfg 1 4) (fun _ => 0) P.e) (hL : MajLimLip4 P.e) : MajGrowT P.e := by
  obtain ⟨K₁, δ₁, R₁, hδ₁, hK₁⟩ := hV
  obtain ⟨K₂, hK₂⟩ := hL
  have hmass : ∀ g, (1 : ℝ) ≤ (decCfg 1 4).mass g :=
    dec_cfg_mass_ge le_rfl one_pos (by norm_num)
  have hpv := dec_cfg_pv (μ := 1) one_ne_zero (by norm_num : (0 : ℝ) ≤ 4)
  have hrep : ∀ f : Fin 3, (fun _ : Fin 3 => (0 : Fin 3)) ((fun _ => 0) f) = (fun _ => 0) f :=
    fun _ => rfl
  have hlim : ∀ s : ℝ, 0 ≤ s → Tendsto (fun Λ : ℝ => qPair (decCfg 1 4) (fun _ => 0) P.e Λ⁻¹ Λ s -
      qPair (decCfg 1 4) (fun _ => 0) P.e Λ⁻¹ Λ 0) atTop
      (𝓝 (asmPolLim (decCfg 1 4) (fun _ => 0) P.e s)) := fun s hs =>
    dec_tendsto_asmPolLim (Φ := decCfg 1 4) (rep := fun _ => 0) one_pos hmass hrep P he hpv.1
      hpv.2 hF (by linarith)
  have hev : ∀ᶠ Λ : ℝ in atTop, 0 < Λ⁻¹ ∧ Λ⁻¹ < δ₁ ∧ R₁ < Λ := by
    filter_upwards [eventually_gt_atTop R₁, eventually_gt_atTop δ₁⁻¹] with Λ hR hΛ
    have hΛ0 : 0 < Λ := (inv_pos.2 hδ₁).trans hΛ
    exact ⟨inv_pos.2 hΛ0, by rwa [inv_lt_comm₀ hΛ0 hδ₁], hR⟩
  have he4 : 0 < ‖(P.e : ℂ) ^ 4‖ := by
    rw [norm_pow, Complex.norm_real]
    have := abs_pos.2 he
    positivity
  set A : ℝ := (|K₁| + |K₂|) / ‖(P.e : ℂ) ^ 4‖ with hA
  refine ⟨A, fun t ht => ⟨?_, fun t' ht' htt => ?_⟩⟩
  · have hle : ‖asmPolLim (decCfg 1 4) (fun _ => 0) P.e t‖ ≤ K₁ * majW t := by
      refine le_of_tendsto (hlim t ht).norm ?_
      filter_upwards [hev] with Λ hΛ
      exact hK₁ _ _ hΛ.1 hΛ.2.1 hΛ.2.2 t ht
    rw [decT₀, norm_div, div_le_iff₀ he4]
    have hw := (majW_pos ht).le
    calc _ ≤ K₁ * majW t := hle
      _ ≤ (|K₁| + |K₂|) * majW t := by
          gcongr
          linarith [le_abs_self K₁, abs_nonneg K₂]
      _ = _ := by rw [hA]; field_simp
  · rw [decT₀, decT₀, ← sub_div, norm_div, div_le_iff₀ he4]
    have hw := (majW_pos ht).le
    have hq : 0 ≤ (t - t') / t' := div_nonneg (by linarith) ht'.le
    calc _ ≤ K₂ * majW t * ((t - t') / t') := hK₂ t t' ht' htt
      _ ≤ (|K₁| + |K₂|) * majW t * ((t - t') / t') := by
          gcongr
          linarith [le_abs_self K₂, abs_nonneg K₁]
      _ = _ := by rw [hA]; field_simp

section Assembly

variable {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ)

/-- The frozen-flavour value bound, as taken by `maj_asmMajorant_of`. -/
abbrev MajFixRay : Prop :=
  ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ →
    1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
    ∀ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) → (∀ ℓ, mH ℓ < MH₂ ℓ) →
      (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) →
      (∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0) →
        MajRayVal (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) leptonRep P₀.e

/-- **(L10) `AsmMajorant` without `AsmFaceIds`**: it follows from `DecFaceGen`. -/
theorem maj_asmMajorant_of_gen (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hF : DecFaceGen P₀.e) (hDc : DecContD P₀.e)
    (hD48 : DecLipD48 P₀.e) (hTc : DecContT P₀.e) (hT48 : DecLipT48 P₀.e)
    (hGD : MajGrowD P₀.e) (hV4 : MajRayVal (decCfg 1 4) (fun _ => 0) P₀.e)
    (hL4 : MajRayLip (decCfg 1 4) (fun _ => 0) P₀.e) (hFix : MajFixRay P₀ mH) :
    AsmMajorant P₀ mH :=
  maj_asmMajorant_of P₀ mH he hm hmH (maj_asmFaceIds_of_decFaceGen P₀ mH hm hmH hF) hF hDc hD48
    hTc hT48 hGD hV4 hL4 hFix

/-- **(L10) `AsmMajorant` with the scale-Lipschitz bound of the photon limit** (`MajLimLip4`) in
place of the one uniform in the photon pair (`MajRayLip`). -/
theorem maj_asmMajorant_of_lim (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hF : DecFaceGen P₀.e) (hDc : DecContD P₀.e)
    (hD48 : DecLipD48 P₀.e) (hTc : DecContT P₀.e) (hT48 : DecLipT48 P₀.e)
    (hGD : MajGrowD P₀.e) (hV4 : MajRayVal (decCfg 1 4) (fun _ => 0) P₀.e)
    (hL4 : MajLimLip4 P₀.e) (hFix : MajFixRay P₀ mH) :
    AsmMajorant P₀ mH :=
  maj_majorant_of_lim_fixed P₀ mH he hm hmH (maj_asmFaceIds_of_decFaceGen P₀ mH hm hmH hF)
    (maj_limBound_of_grow P₀ mH he hm hmH hF hDc hD48 hTc hT48
      (maj_growT_of_ray_lim P₀ he hF hV4 hL4) hGD)
    (maj_fixedBound_of_ray P₀ mH hm hFix)

end Assembly

end QED.GradedProof.RPi4

end
