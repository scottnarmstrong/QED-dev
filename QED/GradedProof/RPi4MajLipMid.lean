/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajLipRay
public import QED.GradedProof.RPi4DecDilQ

/-!
# (R-Π₄) step L10: the middle range of `MajLimLip4` by dilation

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. The input
`MajLipMid4` (Lipschitz bound of `Π = asmPolLim (decCfg 1 4)` on `[s₀, 2]`) needs no separate
analysis: dilating all masses by `l` (`QED.GradedProof.RPi4.dec_asmPolLim_dil`, with the proved
`QED.GradedProof.RPi4.dec_dilQ`) gives `Π(s) = Π_l(l² s)` for the dilated configuration
`decDil l (decCfg 1 4)`, and for `l² s₀ ≥ 1` the increments on one scale of `Π_l` at `l² s ≥ 1`
(`MajRayInc`) are a Lipschitz bound of `Π` on `[s₀, 2]`.

* `majLip_decDil_one`: `decDil 1 Φ = Φ`;
* `majLip_decDil_mass_ge`, `majLip_decDil_pv₂`: the dilated configuration is PV-closed with
  masses at least `l`;
* `majLip_limInc_of_rayInc`: `MajRayInc` passes to the photon limit, for any PV-closed `Φ`;
* **`majLip_mid4_of_dil`**: `MajRayInc` at every `decDil l (decCfg 1 4)`, `l ≥ 1`, gives
  `MajLipMid4`.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

/-- Dilation by `1` is the identity. -/
theorem majLip_decDil_one {F : Type} (Φ : Lepton.Flavors F) : decDil 1 Φ = Φ := by
  cases Φ
  simp [decDil]

/-- The dilated configuration has masses at least `l m₀`. -/
theorem majLip_decDil_mass_ge {F : Type} {Φ : Lepton.Flavors F} {m₀ l : ℝ} (hl : 0 ≤ l)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (g : F) : l * m₀ ≤ (decDil l Φ).mass g :=
  mul_le_mul_of_nonneg_left (hmass g) hl

/-- The second Pauli–Villars condition survives the dilation. -/
theorem majLip_decDil_pv₂ {F : Type} [Fintype F] [DecidableEq F] {Φ : Lepton.Flavors F}
    {rep : F → F} (l : ℝ)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0) :
    ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b),
      (decDil l Φ).coeff f * (decDil l Φ).mass f ^ 2 = 0 := by
  intro b hb
  simp only [decDil, mul_pow]
  rw [show (∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * (l ^ 2 * Φ.mass f ^ 2))
    = l ^ 2 * ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun f _ => by ring, hPV₂ b hb, mul_zero]

section Limit

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)
  {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **Increments on one scale pass to the photon limit.** -/
theorem majLip_limInc_of_rayInc (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e)
    (hI : MajRayInc Φ rep P.e) :
    ∃ K : ℝ, ∀ s s' : ℝ, 1 ≤ s' → s' ≤ s → s ≤ 2 * s' →
      ‖asmPolLim Φ rep P.e s - asmPolLim Φ rep P.e s'‖ ≤ K * majW s * ((s - s') / s') := by
  obtain ⟨K, δ, R, hδ, hK⟩ := hI
  refine ⟨K, fun s s' hs' hss hs2 => ?_⟩
  have hm2 := pow_pos hm₀ 2
  have hlim : ∀ t : ℝ, 1 ≤ t → Tendsto (fun Λ : ℝ => qPair Φ rep P.e Λ⁻¹ Λ t -
      qPair Φ rep P.e Λ⁻¹ Λ 0) atTop (𝓝 (asmPolLim Φ rep P.e t)) := fun t ht =>
    dec_tendsto_asmPolLim (Φ := Φ) (rep := rep) hm₀ hmass hrep P he hPV₁ hPV₂ hF (by linarith)
  have hev : ∀ᶠ Λ : ℝ in atTop, 0 < Λ⁻¹ ∧ Λ⁻¹ < δ ∧ R < Λ := by
    filter_upwards [eventually_gt_atTop R, eventually_gt_atTop δ⁻¹] with Λ hR hΛ
    have hΛ0 : 0 < Λ := (inv_pos.2 hδ).trans hΛ
    exact ⟨inv_pos.2 hΛ0, by rwa [inv_lt_comm₀ hΛ0 hδ], hR⟩
  refine le_of_tendsto ((hlim s (hs'.trans hss)).sub (hlim s' hs')).norm ?_
  filter_upwards [hev] with Λ hΛ
  have e : qPair Φ rep P.e Λ⁻¹ Λ s - qPair Φ rep P.e Λ⁻¹ Λ 0 -
      (qPair Φ rep P.e Λ⁻¹ Λ s' - qPair Φ rep P.e Λ⁻¹ Λ 0) =
      qPair Φ rep P.e Λ⁻¹ Λ s - qPair Φ rep P.e Λ⁻¹ Λ s' := by ring
  rw [e]
  exact hK _ _ hΛ.1 hΛ.2.1 hΛ.2.2 s s' hs' hss hs2

end Limit

/-- **(L10) `MajLipMid4` by dilation**: increments on one scale, uniform in the photon pair, at
the dilated configurations `decDil l (decCfg 1 4)`, `l ≥ 1`. -/
theorem majLip_mid4_of_dil (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e)
    (hI : ∀ l : ℝ, 1 ≤ l → MajRayInc (decDil l (decCfg 1 4)) (fun _ => 0) P.e) :
    MajLipMid4 P.e := by
  intro s₀ hs₀
  have hmass : ∀ g, (1 : ℝ) ≤ (decCfg 1 4).mass g :=
    dec_cfg_mass_ge le_rfl one_pos (by norm_num)
  have hpv := dec_cfg_pv (μ := 1) one_ne_zero (by norm_num : (0 : ℝ) ≤ 4)
  have hrep : ∀ f : Fin 3, (fun _ : Fin 3 => (0 : Fin 3)) ((fun _ => 0) f) = (fun _ => 0) f :=
    fun _ => rfl
  set l : ℝ := Real.sqrt (1 + 1 / s₀) with hl_def
  have hl2 : l ^ 2 = 1 + 1 / s₀ := Real.sq_sqrt (by positivity)
  have hl1 : 1 ≤ l := by
    have h0 : 0 ≤ l := Real.sqrt_nonneg _
    nlinarith [one_div_pos.2 hs₀]
  have hl0 : 0 < l := one_pos.trans_le hl1
  have hl2s : 1 ≤ l ^ 2 * s₀ := by
    rw [hl2, add_mul, one_div_mul_cancel hs₀.ne']
    linarith
  have hmass' : ∀ g, l * 1 ≤ (decDil l (decCfg 1 4)).mass g :=
    majLip_decDil_mass_ge hl0.le hmass
  obtain ⟨K, hK⟩ := majLip_limInc_of_rayInc (decDil l (decCfg 1 4)) (fun _ => 0)
    (by positivity : (0 : ℝ) < l * 1) hmass' hrep hpv.1 (majLip_decDil_pv₂ l hpv.2) P he hF
    (hI l hl1)
  refine ⟨|K| * majW (2 * l ^ 2) / s₀, fun s s' hs' hss hs2 hs2' => ?_⟩
  have hs'0 : 0 < s' := hs₀.trans_le hs'
  have hd : 0 ≤ s - s' := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hdil : ∀ t : ℝ, 0 ≤ t → asmPolLim (decCfg 1 4) (fun _ => 0) P.e t =
      asmPolLim (decDil l (decCfg 1 4)) (fun _ => 0) P.e (l ^ 2 * t) := fun t ht =>
    (dec_asmPolLim_dil one_pos hmass hrep hpv.1 hpv.2 P he (dec_dilQ P he) hF hl0
      (by linarith)).symm
  rw [hdil s (by linarith), hdil s' hs'0.le]
  have hl2p : 0 < l ^ 2 := by positivity
  have h := hK (l ^ 2 * s) (l ^ 2 * s')
    (hl2s.trans (mul_le_mul_of_nonneg_left hs' hl2p.le))
    (mul_le_mul_of_nonneg_left hss hl2p.le) (by nlinarith)
  have hq : (l ^ 2 * s - l ^ 2 * s') / (l ^ 2 * s') = (s - s') / s' := by
    field_simp
  rw [hq] at h
  have hw : majW (l ^ 2 * s) ≤ majW (2 * l ^ 2) :=
    majW_mono (mul_nonneg hl2p.le hs0) (by nlinarith)
  have hw0 : 0 ≤ majW (l ^ 2 * s) := (majW_pos (mul_nonneg hl2p.le hs0)).le
  have hq' : (s - s') / s' ≤ (s - s') / s₀ := div_le_div_of_nonneg_left hd hs₀ hs'
  refine h.trans ?_
  calc K * majW (l ^ 2 * s) * ((s - s') / s') ≤ |K| * majW (2 * l ^ 2) * ((s - s') / s₀) :=
        mul_le_mul (mul_le_mul (le_abs_self _) hw hw0 (abs_nonneg _)) hq'
          (div_nonneg hd hs'0.le) (mul_nonneg (abs_nonneg _) (majW_pos (by positivity)).le)
    _ = _ := by ring

end QED.GradedProof.RPi4

end
