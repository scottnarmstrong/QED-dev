/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdRayAQClass
public import QED.GradedProof.RPi4MajDPRB
public import QED.GradedProof.RPi4FaceIdRateNull
public import QED.GradedProof.RPi4MajTiltM
public import QED.GradedProof.RPi4WireRed

/-!
# (R-Π₄) wiring: the bounded class densities and the face rate for every flavour set

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57). The gain bound
`QED.GradedProof.RPi4.FaceIdRayAQPow` of the three class densities (for all `u ≥ 1`) is the
bound `QED.GradedProof.RPi4.MajDRayPow`; with the rate (B) of the class densities it gives the
ray half of `MajDRay`, and the null half is `QED.GradedProof.RPi4.majDRayNull_vDens_VA` (and
`VB`, `VC`). The face rate follows in the same way from (A) with a power loss, (B) and the
one-loop blocks along the ray with masses at least `m₀ > 0`.

* `wire2_majDRay_VA`, `wire2_majDRay_VB`, `wire2_majDRay_VC`, **`wire2_wireDRay`**,
  **`wire2_wireDRayGen`**: `MajDRay` of the class densities for every flavour set with masses
  at least `m₀ > 0`;
* `wire2_faceIdRateRay_VA`, `wire2_faceIdRateRay_VB`, `wire2_faceIdRateRay_VC`,
  **`wire2_majFaceRate`**, **`wire2_wireFaceRateGen`**: `MajFaceRate` for every
  Pauli–Villars-closed flavour set with masses at least `m₀ > 0`;
* **`wire2_wireFixDens`**: the per-class inputs at every frozen-flavour configuration.
-/

@[expose] public section

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2
open QED.WickModel (Params)

/-- The face rate at the end `k'(s)` of a class density from (A) with a power loss and (B). -/
theorem wire2_faceIdRateRay_of {G : ℝ → (Fin 4 → ℝ) → ℂ} (hA : FaceIdRayAQPow G)
    (hB : FaceIdRayRateB G) : FaceIdRateRay G := by
  obtain ⟨B, p, hp, L, hL⟩ := hB
  exact faceIdRay_of_pow_rate hp hA.faceIdRayAPow hL

section Classes

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {m₀ : ℝ} (hm₀ : 0 < m₀)
  (hmass : ∀ g, m₀ ≤ Φ.mass g) (e : ℝ)

include hm₀ hmass

/-- **`MajDRay` of the class density `VA`**, masses at least `m₀ > 0`. -/
theorem wire2_majDRay_VA : MajDRay fun u k => vDens aVA baseVA cVA Φ e m₀ u k 2 3 :=
  majDRay_of_halves (majDRayRay_of_pow_rateB (faceIdRayAQ_vDens_VA Φ hm₀ hmass e 2 3)
      (faceIdRayB_vDens_VA Φ hm₀ hmass e 2 3)) (majDRayNull_vDens_VA Φ hm₀ hmass e)

/-- **`MajDRay` of the class density `VB`**, masses at least `m₀ > 0`. -/
theorem wire2_majDRay_VB : MajDRay fun u k => vDens aVB baseVB cVB Φ e m₀ u k 2 3 :=
  majDRay_of_halves (majDRayRay_of_pow_rateB (faceIdRayAQ_vDens_VB Φ hm₀ hmass e 2 3)
      (faceIdRayB_vDens_VB Φ hm₀ hmass e 2 3)) (majDRayNull_vDens_VB Φ hm₀ hmass e)

/-- **`MajDRay` of the class density `VC`**, masses at least `m₀ > 0`. -/
theorem wire2_majDRay_VC : MajDRay fun u k => vDens aVC baseVC cVC Φ e m₀ u k 2 3 :=
  majDRay_of_halves (majDRayRay_of_pow_rateB (faceIdRayAQ_vDens_VC Φ hm₀ hmass e 2 3)
      (faceIdRayB_vDens_VC Φ hm₀ hmass e 2 3)) (majDRayNull_vDens_VC Φ hm₀ hmass e)

/-- **`WireDRay`** for every flavour set with masses at least `m₀ > 0`. -/
theorem wire2_wireDRay : WireDRay Φ e m₀ :=
  ⟨wire2_majDRay_VA Φ hm₀ hmass e, wire2_majDRay_VB Φ hm₀ hmass e,
    wire2_majDRay_VC Φ hm₀ hmass e⟩

/-- **The face rate at the end `k'(s)` of the class density `VA`.** -/
theorem wire2_faceIdRateRay_VA : FaceIdRateRay fun u k => vDens aVA baseVA cVA Φ e m₀ u k 2 3 :=
  wire2_faceIdRateRay_of (faceIdRayAQ_vDens_VA Φ hm₀ hmass e 2 3)
    (faceIdRayB_vDens_VA Φ hm₀ hmass e 2 3)

/-- **The face rate at the end `k'(s)` of the class density `VB`.** -/
theorem wire2_faceIdRateRay_VB : FaceIdRateRay fun u k => vDens aVB baseVB cVB Φ e m₀ u k 2 3 :=
  wire2_faceIdRateRay_of (faceIdRayAQ_vDens_VB Φ hm₀ hmass e 2 3)
    (faceIdRayB_vDens_VB Φ hm₀ hmass e 2 3)

/-- **The face rate at the end `k'(s)` of the class density `VC`.** -/
theorem wire2_faceIdRateRay_VC : FaceIdRateRay fun u k => vDens aVC baseVC cVC Φ e m₀ u k 2 3 :=
  wire2_faceIdRateRay_of (faceIdRayAQ_vDens_VC Φ hm₀ hmass e 2 3)
    (faceIdRayB_vDens_VC Φ hm₀ hmass e 2 3)

end Classes

/-- **`MajFaceRate`** for every Pauli–Villars-closed flavour set with masses at least
`m₀ > 0`. -/
theorem wire2_majFaceRate (P : Params) (he : P.e ≠ 0) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (rep : F → F) {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0) :
    MajFaceRate Φ rep P.e m₀ :=
  faceIdRate_of_ray Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he
    (wire2_faceIdRateRay_VA Φ hm₀ hmass P.e) (wire2_faceIdRateRay_VB Φ hm₀ hmass P.e)
    (wire2_faceIdRateRay_VC Φ hm₀ hmass P.e)
    fun _ => maj_tiltRay_fLim_pos P Φ rep hrep hPV₁ hPV₂ hm₀ hmass he _

/-- **`WireDRayGen`**, unconditionally. -/
theorem wire2_wireDRayGen (e : ℝ) : WireDRayGen e :=
  fun _ _ _ Φ _ _ hm₀ hmass _ _ _ => wire2_wireDRay Φ hm₀ hmass e

/-- **`WireFaceRateGen`**, unconditionally (`e ≠ 0`). -/
theorem wire2_wireFaceRateGen (P : Params) (he : P.e ≠ 0) : WireFaceRateGen P.e :=
  fun _ _ _ Φ rep _ hm₀ hmass hrep hPV₁ hPV₂ =>
    wire2_majFaceRate P he Φ rep hm₀ hmass hrep hPV₁ hPV₂

/-- **`WireFixDens`**, unconditionally: `WireDRay` and `MajFaceRate` at every frozen-flavour
configuration. -/
theorem wire2_wireFixDens {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ) (he : P₀.e ≠ 0)
    (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ) : WireFixDens P₀ mH :=
  wire_fixDens_of_gen P₀ mH hm hmH (wire2_wireDRayGen P₀.e) (wire2_wireFaceRateGen P₀ he)

end QED.GradedProof.RPi4

end
