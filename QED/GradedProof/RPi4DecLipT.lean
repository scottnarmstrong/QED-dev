/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecContT
public import QED.GradedProof.RPi4DecLipF
public import QED.GradedProof.RPi4Dyadic

/-!
# (R-Π₄) step L9: `DecLipT48` reduced to Lipschitz bounds at heavy and light photon pairs

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling),
regularity input D3d (`DecLipT48`) of `QED.GradedProof.RPi4.dec_scalAff_of_weak`. The limit
`asmPolLim` is the limit of `Q(Λ⁻¹, Λ; s) - Q(Λ⁻¹, Λ; 0)`, and `Q(Λ⁻¹, Λ) = Q(Λ⁻¹, 1) + Q(1, Λ)`
(`QED.GradedProof.RPi4.qPair_add`). So a Lipschitz bound in `s` near `0`, uniform in the photon
pair, for heavy pairs `1 ≤ b ≤ d` and for light comparable pairs `a ≤ b ≤ 2a ≤ 2` (with a factor
`bᵖ`, summed by the dyadic lemma `QED.GradedProof.RPi4.norm_le_of_comparable_rpow`) passes to
the limit.

* `DecLipHeavy Φ rep e`, `DecLipLight Φ rep e`: the two named analytic inputs;
* `dec_lipHeavy_of_dens`: `DecLipHeavy` from a density bound
  `‖qDens(s, t) - qDens(s', t)‖ ≤ g(t) |s - s'|`, `g` integrable on `[1, ∞)`;
* `dec_lip0_asmPolLim`: `DecLip0 (asmPolLim Φ rep e)` from the two inputs (given the face-limit
  identity on a neighbourhood of `0`);
* **`dec_lipT48_of`**: `DecLipT48` from the two inputs at the configurations `decCfg 1 4`,
  `decCfg 1 8`; **`dec_scalAff_of_lipQ`**: `DecScalAff` modulo `DecFaceGen` and these inputs.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.WickModel (Params)

section Lip

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

/-- **Lipschitz in `s` near `0` at heavy photon pairs, uniformly in the pair.** -/
def DecLipHeavy (e : ℝ) : Prop :=
  ∃ δ L : ℝ, 0 < δ ∧ ∀ b d : ℝ, 1 ≤ b → b ≤ d → ∀ s s' : ℝ, |s| ≤ δ → |s'| ≤ δ →
    ‖qPair Φ rep e b d s - qPair Φ rep e b d s'‖ ≤ L * |s - s'|

/-- **Lipschitz in `s` near `0` at light comparable photon pairs, with a factor `bᵖ`.** -/
def DecLipLight (e : ℝ) : Prop :=
  ∃ δ C p : ℝ, 0 < δ ∧ 0 ≤ C ∧ 0 < p ∧ ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2 * a → b ≤ 1 →
    ∀ s s' : ℝ, |s| ≤ δ → |s'| ≤ δ →
      ‖qPair Φ rep e a b s - qPair Φ rep e a b s'‖ ≤ C * b ^ p * |s - s'|

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **`DecLipHeavy` from a Lipschitz bound on the photon-mass density** (`t ≥ 1`). -/
theorem dec_lipHeavy_of_dens (P : Params) (he : P.e ≠ 0) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hδm : δ < 4 * m₀ ^ 2) (hδc : δ < 2 * c ^ 2) {g : ℝ → ℝ} (hg : IntegrableOn g (Ici 1))
    (hΔ : ∀ s s' : ℝ, |s| ≤ δ → |s'| ≤ δ → ∀ t : ℝ, 1 ≤ t →
      ‖qDens Φ rep P.e m₀ c s t - qDens Φ rep P.e m₀ c s' t‖ ≤ g t * |s - s'|) :
    DecLipHeavy Φ rep P.e := by
  refine ⟨δ, ∫ t in Ici (1 : ℝ), g t, hδ, fun b d hb hbd s s' hs hs' => ?_⟩
  have hreg : ∀ r : ℝ, |r| ≤ δ → -(4 * m₀ ^ 2) < r ∧ r < 2 * c ^ 2 := fun r hr =>
    ⟨by linarith [neg_abs_le r], by linarith [le_abs_self r]⟩
  have hgs : IntegrableOn (fun t => g t * |s - s'|) (Ici ((1 : ℝ) ^ 2)) := by
    rw [one_pow]; exact hg.mul_const _
  have h := norm_qPair_sub_le_of_dens (Q := fun b d =>
      qPair Φ rep P.e b d s - qPair Φ rep P.e b d s')
    (Δ := fun t => qDens Φ rep P.e m₀ c s t - qDens Φ rep P.e m₀ c s' t) one_pos
    (fun b d hb hbd => by
      have hb0 : 0 < b := one_pos.trans_le hb
      obtain ⟨i1, e1⟩ := qPair_eq_integral Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he hb0 hbd hc
        (hreg s hs).1 (hreg s hs).2
      obtain ⟨i2, e2⟩ := qPair_eq_integral Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he hb0 hbd hc
        (hreg s' hs').1 (hreg s' hs').2
      exact ⟨i1.sub i2, by rw [e1, e2, intervalIntegral.integral_sub i1 i2]⟩)
    (fun b hb => by
      have hb0 : 0 < b := one_pos.trans_le hb
      have e1 := qPair_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he hb0 hb0 hb0 (hreg s hs).1
      have e2 := qPair_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he hb0 hb0 hb0 (hreg s' hs').1
      have z1 : qPair Φ rep P.e b b s = 0 := by linear_combination -e1
      have z2 : qPair Φ rep P.e b b s' = 0 := by linear_combination -e2
      simp only [z1, z2, sub_zero])
    hgs (fun t ht => hΔ s s' hs hs' t (by rwa [one_pow] at ht)) b d hb hbd
  refine h.trans ?_
  have hsub : Ici (b ^ 2) ⊆ Ici (1 : ℝ) := Ici_subset_Ici.2 (by nlinarith)
  rw [integral_mul_const]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have hg0 : ∀ t ∈ Ici (1 : ℝ), 0 ≤ g t := fun t ht => by
    have h1 := (norm_nonneg _).trans (hΔ δ (-δ) (by rw [abs_of_pos hδ])
      (by rw [abs_neg, abs_of_pos hδ]) t ht)
    have h2 : (0 : ℝ) < |δ - -δ| := by
      rw [sub_neg_eq_add, abs_of_pos (by linarith)]; linarith
    exact nonneg_of_mul_nonneg_left h1 h2
  exact setIntegral_mono_set hg (ae_restrict_of_forall_mem measurableSet_Ici hg0)
    hsub.eventuallyLE

/-- **Lipschitz near `0` of the photon-regulator limit** from the heavy and light inputs, given
the face-limit identity on a neighbourhood of `0`. -/
theorem dec_lip0_asmPolLim (P : Params) (he : P.e ≠ 0)
    (hId : ∀ s : ℝ, min (-(2 * m₀ ^ 2)) 0 ≤ s → s ≤ max (m₀ ^ 2) 0 →
      FaceLimitId Φ rep P.e m₀ (1 + |max (m₀ ^ 2) 0|) s)
    (hH : DecLipHeavy Φ rep P.e) (hL : DecLipLight Φ rep P.e) :
    DecLip0 (asmPolLim Φ rep P.e) := by
  obtain ⟨δ₁, L₁, hδ₁, hH⟩ := hH
  obtain ⟨δ₂, C, p, hδ₂, hC, hp, hL⟩ := hL
  have hS₀ : -(4 * m₀ ^ 2) < -(2 * m₀ ^ 2) := by nlinarith
  obtain ⟨K, hK⟩ := asm_exists_norm_sub_polLim_le Φ rep P hm₀ hmass hrep hPV₁ hPV₂ he
    (S₀ := -(2 * m₀ ^ 2)) (S := m₀ ^ 2) hS₀ hId
  set δ : ℝ := min (min δ₁ δ₂) (m₀ ^ 2)
  have hδ : 0 < δ := lt_min (lt_min hδ₁ hδ₂) (by positivity)
  have hδ1 : δ ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ m₀ ^ 2 := min_le_right _ _
  set Lt : ℝ := L₁ + C * 1 ^ p / (1 - (2 : ℝ) ^ (-p))
  refine ⟨δ, Lt, hδ, fun s s' hs hs' => ?_⟩
  have hreg : ∀ r : ℝ, |r| ≤ δ → -(4 * m₀ ^ 2) < r := fun r hr => by
    nlinarith [neg_abs_le r]
  have hI : ∀ r : ℝ, |r| ≤ δ → -(2 * m₀ ^ 2) ≤ r ∧ r ≤ m₀ ^ 2 := fun r hr =>
    ⟨by nlinarith [neg_abs_le r], by linarith [le_abs_self r]⟩
  -- the light pairs, by the dyadic lemma
  have hlight : ∀ a, 0 < a → a ≤ 1 →
      ‖qPair Φ rep P.e a 1 s - qPair Φ rep P.e a 1 s'‖ ≤
        C * 1 ^ p / (1 - (2 : ℝ) ^ (-p)) * |s - s'| := by
    intro a ha ha1
    have h := norm_le_of_comparable_rpow (Q := fun a b =>
        (qPair Φ rep P.e a b s - qPair Φ rep P.e a b s') / ((|s - s'| : ℝ) : ℂ)) (r₀ := 1)
      (C := C) hC hp (fun a b d ha hab hbd _ => by
        have hb : 0 < b := ha.trans_le hab
        have hd : 0 < d := hb.trans_le hbd
        rw [qPair_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha hb hd (hreg s hs),
          qPair_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha hb hd (hreg s' hs')]
        ring)
      (fun a b ha hab hb2 hb1 => by
        rcases eq_or_lt_of_le (abs_nonneg (s - s')) with h0 | h0
        · rw [← h0, ofReal_zero, div_zero, norm_zero]
          exact mul_nonneg hC (Real.rpow_nonneg (ha.le.trans hab) _)
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_abs, div_le_iff₀ h0]
        exact hL a b ha hab hb2 hb1 s s' (hs.trans hδ2) (hs'.trans hδ2))
      a 1 ha ha1 le_rfl
    rcases eq_or_lt_of_le (abs_nonneg (s - s')) with h0 | h0
    · have : s = s' := by
        have := h0.symm
        rwa [abs_eq_zero, sub_eq_zero] at this
      subst this
      simp
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_abs, div_le_iff₀ h0] at h
    exact h
  -- pass to the limit
  have hlim : ∀ r, |r| ≤ δ → Tendsto (fun Λ : ℝ => qPair Φ rep P.e Λ⁻¹ Λ r -
      qPair Φ rep P.e Λ⁻¹ Λ 0) atTop (𝓝 (asmPolLim Φ rep P.e r)) := fun r hr => by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (dec_tendsto_rate K)
    filter_upwards [eventually_ge_atTop 1] with Λ hΛ
    exact hK r (hI r hr).1 (hI r hr).2 Λ⁻¹ Λ (inv_pos.2 (one_pos.trans_le hΛ))
      (inv_le_one_of_one_le₀ hΛ) hΛ
  have hdiff := ((hlim s hs).sub (hlim s' hs')).norm
  refine le_of_tendsto hdiff ?_
  filter_upwards [eventually_ge_atTop 1] with Λ hΛ
  have hΛ0 : 0 < Λ := one_pos.trans_le hΛ
  have hi : 0 < Λ⁻¹ := inv_pos.2 hΛ0
  have e1 := qPair_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he hi one_pos hΛ0 (hreg s hs)
  have e2 := qPair_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he hi one_pos hΛ0 (hreg s' hs')
  have e : qPair Φ rep P.e Λ⁻¹ Λ s - qPair Φ rep P.e Λ⁻¹ Λ 0 -
      (qPair Φ rep P.e Λ⁻¹ Λ s' - qPair Φ rep P.e Λ⁻¹ Λ 0) =
      (qPair Φ rep P.e Λ⁻¹ 1 s - qPair Φ rep P.e Λ⁻¹ 1 s') +
        (qPair Φ rep P.e 1 Λ s - qPair Φ rep P.e 1 Λ s') := by
    rw [e1, e2]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1 := hlight Λ⁻¹ hi (inv_le_one_of_one_le₀ hΛ)
  have h2 := hH 1 Λ le_rfl hΛ s s' (hs.trans hδ1) (hs'.trans hδ1)
  calc _ ≤ C * 1 ^ p / (1 - (2 : ℝ) ^ (-p)) * |s - s'| + L₁ * |s - s'| := add_le_add h1 h2
    _ = Lt * |s - s'| := by simp only [Lt]; ring

end Lip

/-- **`DecLipT48` from the heavy and light Lipschitz inputs** at the configurations
`decCfg 1 4` and `decCfg 1 8` (counterterms at the flavour `0`), given `DecFaceGen`. -/
theorem dec_lipT48_of (P : Params) (hF : DecFaceGen P.e)
    (hH : ∀ x : ℝ, x = 4 ∨ x = 8 → DecLipHeavy (decCfg 1 x) (fun _ => 0) P.e)
    (hL : ∀ x : ℝ, x = 4 ∨ x = 8 → DecLipLight (decCfg 1 x) (fun _ => 0) P.e) :
    DecLipT48 P.e := by
  by_cases he : P.e = 0
  · have e0 : ∀ x, decT₀ P.e 1 x = fun _ => 0 := fun x => funext fun s => by simp [decT₀, he]
    refine ⟨?_, ?_⟩ <;> rw [e0] <;> exact ⟨1, 0, one_pos, fun t t' _ _ => by simp⟩
  have key : ∀ x : ℝ, x = 4 ∨ x = 8 → DecLip0 (decT₀ P.e 1 x) := by
    intro x hx
    have hx0 : 0 < x := by rcases hx with rfl | rfl <;> norm_num
    have hx1 : (1 : ℝ) ≤ x := by rcases hx with rfl | rfl <;> norm_num
    have hm₀ : (0 : ℝ) < 1 := one_pos
    have hmass : ∀ g, (1 : ℝ) ≤ (decCfg 1 x).mass g := dec_cfg_mass_ge le_rfl hm₀
      (by rw [one_pow]; exact hx1)
    have hpv := dec_cfg_pv (μ := 1) one_ne_zero hx0.le
    have hrep : ∀ f : Fin 3, (fun _ : Fin 3 => (0 : Fin 3)) ((fun _ => 0) f) = (fun _ => 0) f :=
      fun _ => rfl
    obtain ⟨δ, L, hδ, h⟩ := dec_lip0_asmPolLim (decCfg 1 x) (fun _ => 0) hm₀ hmass hrep hpv.1
      hpv.2 P he (fun s h₀ h₁ => hF (Fin 3) (decCfg 1 x) (fun _ => 0) 1 hm₀ hmass hrep hpv.1
        hpv.2 _ s (by positivity) ((lt_min (by norm_num) (by norm_num)).trans_le h₀)
        (h₁.trans_lt (asm_max_lt_two_mul_sq _))) (hH x hx) (hL x hx)
    have he4 : 0 < ‖(P.e : ℂ) ^ 4‖ := norm_pos_iff.mpr (pow_ne_zero 4 (ofReal_ne_zero.mpr he))
    refine ⟨δ, L / ‖(P.e : ℂ) ^ 4‖, hδ, fun t t' ht ht' => ?_⟩
    simp only [decT₀]
    rw [← sub_div, norm_div, div_le_iff₀ he4]
    have e : L / ‖(P.e : ℂ) ^ 4‖ * |t - t'| * ‖(P.e : ℂ) ^ 4‖ = L * |t - t'| := by
      field_simp
    rw [e]
    exact h t t' ht ht'
  exact ⟨key 4 (Or.inl rfl), key 8 (Or.inr rfl)⟩

/-- **`DecScalAff` modulo `DecFaceGen` and the heavy and light Lipschitz inputs at the two
configurations.** -/
theorem dec_scalAff_of_lipQ (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e)
    (hH : ∀ x : ℝ, x = 4 ∨ x = 8 → DecLipHeavy (decCfg 1 x) (fun _ => 0) P.e)
    (hL : ∀ x : ℝ, x = 4 ∨ x = 8 → DecLipLight (decCfg 1 x) (fun _ => 0) P.e) :
    DecScalAff P.e :=
  dec_scalAff_of_lip48 P he hF (dec_lipD48 P) (dec_lipT48_of P hF hH hL)

end QED.GradedProof.RPi4

end
