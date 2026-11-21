/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajLipMid
public import QED.GradedProof.RPi4Wire
public import QED.GradedProof.RPi4MajLClass
public import QED.GradedProof.RPi4FaceIdDone

/-!
# (R-Π₄) step L10: `MajLimLip4` at `decCfg 1 4` from the open per-class inputs

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. At the
configuration `decCfg 1 4` (masses `1, √2, 2`, `m₀ = 1`) the proved inputs are discharged:
`DecFaceGen` (`QED.GradedProof.RPi4.faceId_decFaceGen_all`), `DecLip0 (decT₀ e 1 4)`
(`QED.GradedProof.RPi4.wire_lipT48_of_faceGen`), `MajLRay` of the three class entries
(`QED.GradedProof.RPi4.majL_vVal_VA`, …) and `MajTiltRay` of the single-flavour blocks
(`QED.GradedProof.RPi4.maj_tiltRay_fLim_gen`); `MajRayVal` comes from
`QED.GradedProof.RPi4.wire_rayVal4_of_inputs`.

* **`majLip_limLip4_of_inputs`**: `MajLimLip4` from `MajDRay` (three classes) and `MajFaceRate`
  (the inputs of the value bound), their increment forms `MajDRayInc` and `MajFaceRateInc`,
  `MajLRayInc` of the three class entries, and `MajLipMid4`;
* `MajLipIns Φ rep e m₀`: the per-class inputs of `MajRayInc` (`MajDRay`, `MajLRayInc`,
  `MajDRayInc` of the three classes, `MajFaceRateInc`); `majLip_rayInc_of_ins`: they give
  `MajRayInc` when all masses are at least `1`;
* **`majLip_limLip4_of_ins`**: `MajLimLip4` from `MajFaceRate` at `decCfg 1 4` and `MajLipIns` at
  every dilated configuration `decDil l (decCfg 1 4)`, `l ≥ 1` (these give `MajLipMid4` by
  `QED.GradedProof.RPi4.majLip_mid4_of_dil`).
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2

/-- **(L10) `MajLimLip4` at `decCfg 1 4` from the open per-class inputs.** -/
theorem majLip_limLip4_of_inputs (P : Params) (he : P.e ≠ 0)
    (hDA : MajDRay fun u k => vDens aVA baseVA cVA (decCfg 1 4) P.e 1 u k 2 3)
    (hDB : MajDRay fun u k => vDens aVB baseVB cVB (decCfg 1 4) P.e 1 u k 2 3)
    (hDC : MajDRay fun u k => vDens aVC baseVC cVC (decCfg 1 4) P.e 1 u k 2 3)
    (hR : MajFaceRate (decCfg 1 4) (fun _ => 0) P.e 1)
    (hA' : MajLRayInc fun a b k => vVal aVA baseVA cVA (decCfg 1 4) P.e 1 a b k 2 3)
    (hB' : MajLRayInc fun a b k => vVal aVB baseVB cVB (decCfg 1 4) P.e 1 a b k 2 3)
    (hC' : MajLRayInc fun a b k => vVal aVC baseVC cVC (decCfg 1 4) P.e 1 a b k 2 3)
    (hDA' : MajDRayInc fun u k => vDens aVA baseVA cVA (decCfg 1 4) P.e 1 u k 2 3)
    (hDB' : MajDRayInc fun u k => vDens aVB baseVB cVB (decCfg 1 4) P.e 1 u k 2 3)
    (hDC' : MajDRayInc fun u k => vDens aVC baseVC cVC (decCfg 1 4) P.e 1 u k 2 3)
    (hRI : MajFaceRateInc (decCfg 1 4) (fun _ => 0) P.e 1) (hM : MajLipMid4 P.e) :
    MajLimLip4 P.e := by
  have hmass : ∀ g, (1 : ℝ) ≤ (decCfg 1 4).mass g :=
    dec_cfg_mass_ge le_rfl one_pos (by norm_num)
  have hpv := dec_cfg_pv (μ := 1) one_ne_zero (by norm_num : (0 : ℝ) ≤ 4)
  have hrep : ∀ f : Fin 3, (fun _ : Fin 3 => (0 : Fin 3)) ((fun _ => 0) f) = (fun _ => 0) f :=
    fun _ => rfl
  have hF := faceId_decFaceGen_all P.e
  have hA := majL_vVal_VA (decCfg 1 4) one_pos hmass P.e 2 3
  have hB := majL_vVal_VB (decCfg 1 4) one_pos hmass P.e 2 3
  have hC := majL_vVal_VC (decCfg 1 4) one_pos hmass P.e 2 3
  have hFl := fun g => maj_tiltRay_fLim_gen P (decCfg 1 4) (fun _ => 0) hrep hpv.1 hpv.2 hmass he
    (Pi.single g 1)
  exact majLip_limLip4_of P he hF (wire_lipT48_of_faceGen P he hF).1
    (wire_rayVal4_of_inputs P he hF hA hB hC hDA hDB hDC hR)
    (majLip_rayInc_of_inputs (decCfg 1 4) (fun _ => 0) one_pos hmass hrep hpv.1 hpv.2 P he hA hB
      hC hA' hB' hC' hDA hDB hDC hDA' hDB' hDC' hRI hFl) hM

/-- **The per-class inputs of `MajRayInc`** at a flavour set. -/
def MajLipIns {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)
    (e m₀ : ℝ) : Prop :=
  (MajDRay fun u k => vDens aVA baseVA cVA Φ e m₀ u k 2 3) ∧
  (MajDRay fun u k => vDens aVB baseVB cVB Φ e m₀ u k 2 3) ∧
  (MajDRay fun u k => vDens aVC baseVC cVC Φ e m₀ u k 2 3) ∧
  (MajLRayInc fun a b k => vVal aVA baseVA cVA Φ e m₀ a b k 2 3) ∧
  (MajLRayInc fun a b k => vVal aVB baseVB cVB Φ e m₀ a b k 2 3) ∧
  (MajLRayInc fun a b k => vVal aVC baseVC cVC Φ e m₀ a b k 2 3) ∧
  (MajDRayInc fun u k => vDens aVA baseVA cVA Φ e m₀ u k 2 3) ∧
  (MajDRayInc fun u k => vDens aVB baseVB cVB Φ e m₀ u k 2 3) ∧
  (MajDRayInc fun u k => vDens aVC baseVC cVC Φ e m₀ u k 2 3) ∧
  MajFaceRateInc Φ rep e m₀

/-- **`MajRayInc` from `MajLipIns`** when all masses are at least `1` (the light-pair class
bounds `MajLRay` and the one-loop blocks `MajTiltRay` are proved). -/
theorem majLip_rayInc_of_ins {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (rep : F → F) {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hm1 : ∀ g, 1 ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (P : Params) (he : P.e ≠ 0) (h : MajLipIns Φ rep P.e m₀) : MajRayInc Φ rep P.e := by
  obtain ⟨hDA, hDB, hDC, hA', hB', hC', hDA', hDB', hDC', hRI⟩ := h
  exact majLip_rayInc_of_inputs Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he
    (majL_vVal_VA Φ hm₀ hmass P.e 2 3) (majL_vVal_VB Φ hm₀ hmass P.e 2 3)
    (majL_vVal_VC Φ hm₀ hmass P.e 2 3) hA' hB' hC' hDA hDB hDC hDA' hDB' hDC' hRI
    fun g => maj_tiltRay_fLim_gen P Φ rep hrep hPV₁ hPV₂ hm1 he (Pi.single g 1)

/-- **(L10) `MajLimLip4` from `MajFaceRate` at `decCfg 1 4` and the per-class inputs
`MajLipIns` at the dilated configurations `decDil l (decCfg 1 4)`, `l ≥ 1`** (`m₀ = l`; at
`l = 1` this is `decCfg 1 4` itself). -/
theorem majLip_limLip4_of_ins (P : Params) (he : P.e ≠ 0)
    (hR : MajFaceRate (decCfg 1 4) (fun _ => 0) P.e 1)
    (h : ∀ l : ℝ, 1 ≤ l → MajLipIns (decDil l (decCfg 1 4)) (fun _ => 0) P.e l) :
    MajLimLip4 P.e := by
  have hmass : ∀ g, (1 : ℝ) ≤ (decCfg 1 4).mass g :=
    dec_cfg_mass_ge le_rfl one_pos (by norm_num)
  have hpv := dec_cfg_pv (μ := 1) one_ne_zero (by norm_num : (0 : ℝ) ≤ 4)
  have hrep : ∀ f : Fin 3, (fun _ : Fin 3 => (0 : Fin 3)) ((fun _ => 0) f) = (fun _ => 0) f :=
    fun _ => rfl
  have hF := faceId_decFaceGen_all P.e
  have hM : MajLipMid4 P.e := majLip_mid4_of_dil P he hF fun l hl => by
    have hl0 : 0 < l := one_pos.trans_le hl
    have hm : ∀ g, l ≤ (decDil l (decCfg 1 4)).mass g := fun g => by
      simpa using majLip_decDil_mass_ge hl0.le hmass g
    exact majLip_rayInc_of_ins (decDil l (decCfg 1 4)) (fun _ => 0) hl0 hm
      (fun g => hl.trans (hm g)) hrep hpv.1 (majLip_decDil_pv₂ l hpv.2) P he (h l hl)
  have h1 := h 1 le_rfl
  rw [majLip_decDil_one] at h1
  obtain ⟨hDA, hDB, hDC, hA', hB', hC', hDA', hDB', hDC', hRI⟩ := h1
  exact majLip_limLip4_of_inputs P he hDA hDB hDC hR hA' hB' hC' hDA' hDB' hDC' hRI hM

end QED.GradedProof.RPi4

end
