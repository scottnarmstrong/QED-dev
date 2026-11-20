/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecDilV

/-!
# (R-Π₄) step L9, D3a: `DecDilQ` (dimensional analysis of the class sum) is a theorem

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling),
part D3a. Dilating masses, photon regulators by `l` and `s` by `l²` leaves every projected class
limit of `qPair` unchanged:

* `dec_projS_wV_dil`: the two-loop classes (`VA`, `VB`, `VC`, any class with `VPJ` integrands);
* `dec_projS_fLim_dil`: the mass-derivative block with any weight;
* **`dec_dilQ : DecDilQ P.e`** (for `P.e ≠ 0`), and hence
  **`dec_scaleT₀_of_faceGen : DecFaceGen P.e → DecScaleT₀ P.e`**.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded
open QED.GradedProof.VP2

namespace QED.GradedProof.RPi4

variable {F : Type} [Fintype F]

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-- **A two-loop class limit at the dilated point.** -/
theorem dec_projS_wV_dil (Φ : Lepton.Flavors F) (e : ℝ)
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Mat) (base : Fin 5 → Fin 2 → ℤ)
    (c : Fin 5 → ℝ) {T a b l s : ℝ} (hV : VPJ T (vSumF Φ e A base c a b)) (hT : 0 < T)
    (hl : 0 < l) (hs : -T ^ 2 < s) :
    projS (wV (decDil l Φ) e A base c (l * a) (l * b)) (l ^ 2 * s) =
      projS (wV Φ e A base c a b) s :=
  dec_projS_smul hV.hasVPLim hT hl
    (fun ε _ k μ ν => dec_jef_vSumF_smul Φ e A base c a b ε k μ ν hl) hs

/-- **The mass-derivative block at the dilated point.** -/
theorem dec_projS_fLim_dil (Φ : Lepton.Flavors F) (rep : F → F) (e : ℝ) (δ : F → ℝ)
    {T l s : ℝ}
    (hV : VPF T fun ε k q μ ν => dBlockD Φ rep e δ ε k q μ ν) (hT : 0 < T) (hl : 0 < l)
    (hs : -T ^ 2 < s) :
    projS (fLim (decDil l Φ) rep e δ) (l ^ 2 * s) = projS (fLim Φ rep e δ) s :=
  dec_projS_smul hV.hasVPLim hT hl
    (fun ε _ k μ ν => dec_efi_dBlockD_smul Φ rep e δ ε k μ ν hl) hs

/-- **(D3a) the dimensional analysis of the class sum at fixed photon regulators.** -/
theorem dec_dilQ (P : Params) (he : P.e ≠ 0) : DecDilQ P.e := by
  intro F _ _ Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ l a b s hl ha hb hs
  have hT : 0 < 2 * m₀ := by positivity
  have hs' : -(2 * m₀) ^ 2 < s := by nlinarith
  have hT' : 0 < m₀ + m₀ := by positivity
  have hs'' : -(m₀ + m₀) ^ 2 < s := by nlinarith
  have hδ : (fun g => ctPair P.e ((decDil l Φ).mass g) (l * a) (l * b)) =
      fun g => ctPair P.e (Φ.mass g) a b :=
    funext fun g => dec_ctPair_smul P.e _ a b hl.ne'
  simp only [qPair, hδ]
  rw [dec_projS_wV_dil Φ P.e aVA baseVA cVA (vpj_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb)
      hT hl hs',
    dec_projS_wV_dil Φ P.e aVB baseVB cVB (vpj_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb)
      hT hl hs',
    dec_projS_wV_dil Φ P.e aVC baseVC cVC (vpj_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb)
      hT hl hs',
    dec_projS_fLim_dil Φ rep P.e _ (vpf_dBlockD Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he _) hT' hl
      hs'']

/-- **`DecScaleT₀` modulo only the generic face-limit identity.** -/
theorem dec_scaleT₀_of_faceGen (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e) :
    DecScaleT₀ P.e :=
  dec_scaleT₀ P he (dec_dilQ P he) hF

end QED.GradedProof.RPi4

end
