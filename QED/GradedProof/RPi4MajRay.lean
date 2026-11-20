/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajScalG

/-!
# (R-Π₄) step L10: the remaining large-`s` input, uniform in the photon pair

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. What remains of
the majorant, besides the inputs of the decoupling (step L9), is one statement at **fixed**
fermion masses: the subtracted class sum `Q(a, b; s) - Q(a, b; 0)` grows at most like
`w(s) = 1 + log(1 + s)` for all `s ≥ 0` (and, where needed, so do its increments on the scale of
`s`), uniformly for light `a` and heavy `b`.

* `MajRayVal Φ rep e`, `MajRayLip Φ rep e`: these two statements for a flavour set `Φ`;
* `maj_majW_le`: `w(s) ≤ (1 + log(max 1 m²)) (1 + log(1 + s/m²))`;
* `maj_fixedBound_of_ray`: `MajRayVal` at every fermion-regulator point of the frozen statement
  gives **`MajFixedBound`**;
* `maj_growT_of_ray`: `MajRayVal` and `MajRayLip` at the configuration `decCfg 1 4` give
  **`MajGrowT`**, given the generic face-limit identity (the bounds pass to the diagonal limit
  `asmPolLim`, `dec_tendsto_asmPolLim`);
* `maj_asmMajorant_of`: **`AsmMajorant`** from these, the inputs of the decoupling and `MajGrowD`.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

section Ray

variable {F : Type} [Fintype F] [DecidableEq F]

/-- **The large-`s` value bound at fixed fermion masses**, uniform in the photon pair: for
`0 < a < δ`, `b > R` and every `s ≥ 0`, `‖Q(a, b; s) - Q(a, b; 0)‖ ≤ K w(s)`. -/
def MajRayVal (Φ : Lepton.Flavors F) (rep : F → F) (e : ℝ) : Prop :=
  ∃ K δ R : ℝ, 0 < δ ∧ ∀ a b : ℝ, 0 < a → a < δ → R < b → ∀ s : ℝ, 0 ≤ s →
    ‖qPair Φ rep e a b s - qPair Φ rep e a b 0‖ ≤ K * majW s

/-- **The large-`s` bound on the scale of `s` at fixed fermion masses**, uniform in the photon
pair: `‖Q(a, b; s) - Q(a, b; s')‖ ≤ K w(s) (s - s')/s'` for `0 < s' ≤ s`. -/
def MajRayLip (Φ : Lepton.Flavors F) (rep : F → F) (e : ℝ) : Prop :=
  ∃ K δ R : ℝ, 0 < δ ∧ ∀ a b : ℝ, 0 < a → a < δ → R < b → ∀ s s' : ℝ, 0 < s' → s' ≤ s →
    ‖qPair Φ rep e a b s - qPair Φ rep e a b s'‖ ≤ K * majW s * ((s - s') / s')

end Ray

/-- `w(s) ≤ (1 + log(max 1 m²)) (1 + log(1 + s/m²))` for `m > 0`, `s ≥ 0`. -/
theorem maj_majW_le {m s : ℝ} (hm : 0 < m) (hs : 0 ≤ s) :
    majW s ≤ (1 + Real.log (max 1 (m ^ 2))) * (1 + Real.log (1 + s / m ^ 2)) := by
  have hm2 : 0 < m ^ 2 := by positivity
  set M : ℝ := max 1 (m ^ 2) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMm : m ^ 2 ≤ M := le_max_right _ _
  have hq : 0 ≤ s / m ^ 2 := by positivity
  have h1 : 1 + s ≤ (1 + s / m ^ 2) * M := by
    have : s ≤ s / m ^ 2 * M := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hm2]
      nlinarith
    nlinarith
  have hlM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hlq : 0 ≤ Real.log (1 + s / m ^ 2) := Real.log_nonneg (by linarith)
  have h2 : Real.log (1 + s) ≤ Real.log (1 + s / m ^ 2) + Real.log M := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) h1
  simp only [majW]
  nlinarith [mul_nonneg hlM hlq]

section Frozen

variable {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ)

/-- **(L10, fixed-regulator part) `MajFixedBound` from the large-`s` value bound** at every
fermion-regulator point of the frozen statement. -/
theorem maj_fixedBound_of_ray (hm : 0 < P₀.m)
    (h : ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∀ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) → (∀ ℓ, mH ℓ < MH₂ ℓ) →
        (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) →
        (∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0) →
          MajRayVal (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) leptonRep P₀.e) :
    MajFixedBound P₀ mH := by
  intro M₁ M₂ c₁ c₂ hM₁ hM₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ hcH₁ hcH₂
  obtain ⟨K, δ, R, hδ, hK⟩ := h M₁ M₂ c₁ c₂ hM₁ hM₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ hcH₁ hcH₂
  set c : ℝ := 1 + Real.log (max 1 (P₀.m ^ 2)) with hc
  have hc0 : 0 ≤ c := by
    have := Real.log_nonneg (le_max_left 1 (P₀.m ^ 2))
    linarith
  refine ⟨|K| * c, δ, hδ, R, fun mγ Λ hmγ hmγδ hRΛ s hs => ?_⟩
  have hw := maj_majW_le hm hs
  have hw0 := (majW_pos hs).le
  calc _ ≤ K * majW s := hK mγ Λ hmγ hmγδ hRΛ s hs
    _ ≤ |K| * majW s := mul_le_mul_of_nonneg_right (le_abs_self K) hw0
    _ ≤ |K| * (c * (1 + Real.log (1 + s / P₀.m ^ 2))) :=
        mul_le_mul_of_nonneg_left hw (abs_nonneg K)
    _ = _ := by ring

end Frozen

/-- **(L10 input) `MajGrowT` from the large-`s` bounds at the configuration `decCfg 1 4`**,
given the generic face-limit identity: the bounds pass to the diagonal limit. -/
theorem maj_growT_of_ray (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e)
    (hV : MajRayVal (decCfg 1 4) (fun _ => 0) P.e) (hL : MajRayLip (decCfg 1 4) (fun _ => 0) P.e) :
    MajGrowT P.e := by
  obtain ⟨K₁, δ₁, R₁, hδ₁, hK₁⟩ := hV
  obtain ⟨K₂, δ₂, R₂, hδ₂, hK₂⟩ := hL
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
  -- the photon pairs `(Λ⁻¹, Λ)` are eventually admissible
  have hev : ∀ (δ R : ℝ), 0 < δ → ∀ᶠ Λ : ℝ in atTop, 0 < Λ⁻¹ ∧ Λ⁻¹ < δ ∧ R < Λ := by
    intro δ R hδ
    filter_upwards [eventually_gt_atTop R, eventually_gt_atTop δ⁻¹] with Λ hR hΛ
    have hΛ0 : 0 < Λ := (inv_pos.2 hδ).trans hΛ
    exact ⟨inv_pos.2 hΛ0, by rwa [inv_lt_comm₀ hΛ0 hδ], hR⟩
  have he4 : 0 < ‖(P.e : ℂ) ^ 4‖ := by
    rw [norm_pow, Complex.norm_real]
    have := abs_pos.2 he
    positivity
  set A : ℝ := (|K₁| + |K₂|) / ‖(P.e : ℂ) ^ 4‖ with hA
  refine ⟨A, fun t ht => ⟨?_, fun t' ht' htt => ?_⟩⟩
  · have hle : ‖asmPolLim (decCfg 1 4) (fun _ => 0) P.e t‖ ≤ K₁ * majW t := by
      refine le_of_tendsto (hlim t ht).norm ?_
      filter_upwards [hev δ₁ R₁ hδ₁] with Λ hΛ
      exact hK₁ _ _ hΛ.1 hΛ.2.1 hΛ.2.2 t ht
    rw [decT₀, norm_div, div_le_iff₀ he4]
    have hw := (majW_pos ht).le
    calc _ ≤ K₁ * majW t := hle
      _ ≤ (|K₁| + |K₂|) * majW t := by
          gcongr
          linarith [le_abs_self K₁, abs_nonneg K₂]
      _ = _ := by rw [hA]; field_simp
  · have ht0 : 0 ≤ t' := ht'.le
    have hle : ‖asmPolLim (decCfg 1 4) (fun _ => 0) P.e t -
        asmPolLim (decCfg 1 4) (fun _ => 0) P.e t'‖ ≤ K₂ * majW t * ((t - t') / t') := by
      refine le_of_tendsto ((hlim t ht).sub (hlim t' ht0)).norm ?_
      filter_upwards [hev δ₂ R₂ hδ₂] with Λ hΛ
      have := hK₂ _ _ hΛ.1 hΛ.2.1 hΛ.2.2 t t' ht' htt
      convert this using 2
      ring
    rw [decT₀, decT₀, ← sub_div, norm_div, div_le_iff₀ he4]
    have hw := (majW_pos ht).le
    have hq : 0 ≤ (t - t') / t' := div_nonneg (by linarith) ht'.le
    calc _ ≤ K₂ * majW t * ((t - t') / t') := hle
      _ ≤ (|K₁| + |K₂|) * majW t * ((t - t') / t') := by
          gcongr
          linarith [le_abs_self K₂, abs_nonneg K₁]
      _ = _ := by rw [hA]; field_simp

section Assembly

variable {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ)

/-- **(L10) the majorant `AsmMajorant`**, from the face-limit identities, the inputs of the
decoupling (step L9), the one-loop growth `MajGrowD`, and the large-`s` bounds at fixed fermion
masses: at the configuration `decCfg 1 4` (value and scale) and at every fermion-regulator point of
the frozen statement (value). -/
theorem maj_asmMajorant_of (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hId : AsmFaceIds P₀ mH) (hF : DecFaceGen P₀.e) (hDc : DecContD P₀.e)
    (hD48 : DecLipD48 P₀.e) (hTc : DecContT P₀.e) (hT48 : DecLipT48 P₀.e)
    (hGD : MajGrowD P₀.e) (hV4 : MajRayVal (decCfg 1 4) (fun _ => 0) P₀.e)
    (hL4 : MajRayLip (decCfg 1 4) (fun _ => 0) P₀.e)
    (hFix : ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∀ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) → (∀ ℓ, mH ℓ < MH₂ ℓ) →
        (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) →
        (∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0) →
          MajRayVal (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) leptonRep P₀.e) :
    AsmMajorant P₀ mH :=
  maj_majorant_of_lim_fixed P₀ mH he hm hmH hId
    (maj_limBound_of_grow P₀ mH he hm hmH hF hDc hD48 hTc hT48
      (maj_growT_of_ray P₀ he hF hV4 hL4) hGD)
    (maj_fixedBound_of_ray P₀ mH hm hFix)

end Assembly

end QED.GradedProof.RPi4

end
