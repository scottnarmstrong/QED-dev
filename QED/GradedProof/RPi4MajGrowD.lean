/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajNum

/-!
# (R-Π₄) step L10, one loop: `MajGrowD`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10, input
`MajGrowD`. The ten pieces of the inserted bubble satisfy `MajTiltRay`
(`QED.GradedProof.RPi4.maj_tiltRay_eVal0`, …), hence so do the bubble `insVal`, the block sum
`fbVal` at the pure mass insertion (`d₂ = 0`), and, through
`QED.GradedProof.RPi4.fLim_eq_fbVal`, the limit `fLim (decCfg 1 4)` of the weighted
mass-derivative block. With `QED.GradedProof.RPi4.maj_growD_of_tiltRay` this closes `MajGrowD`.
No Pauli–Villars cancellation is used.

* `maj_tiltRay_insVal`, `maj_tiltRay_fbVal`, `maj_tiltRay_fLim`;
* **`maj_growD`**: `P.e ≠ 0 → MajGrowD P.e`.
-/

@[expose] public section

open Complex
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2

/-- **`MajTiltRay` of the inserted bubble** at a pure mass insertion, `bx ≠ bY`. -/
theorem maj_tiltRay_insVal (sw : Bool) (dm : ℝ) {bx bY : Bool} (h : bx ≠ bY) {m₀ : ℝ}
    (hm₀ : 0 < m₀) {M X Y : ℝ} (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y) :
    MajTiltRay (insVal m₀ sw 0 dm bx bY M X Y) := by
  exact (((((((((((maj_tiltRay_eVal0 sw dm h hm₀ ⟨hM, hM, hX, hY, hM⟩ bY bY bY).add
    (maj_tiltRay_eVal0 sw dm h hm₀ ⟨hM, hM, hX, hY, hX⟩ bY bY bY)).add
    (maj_tiltRay_eVal0 sw dm h hm₀ ⟨hM, hM, hX, hY, hY⟩ bY bY bY)).add
    (maj_tiltRay_eVal0 sw dm h hm₀ ⟨hM, hX, hX, hY, hX⟩ bx bY bY)).add
    (maj_tiltRay_eVal0 sw dm h hm₀ ⟨hM, hX, hX, hY, hY⟩ bx bY bY)).add
    (maj_tiltRay_eVal0 sw dm h hm₀ ⟨hM, hX, hY, hY, hY⟩ bx bx bY)).add
    (maj_tiltRay_eVal2 sw dm h hm₀ ⟨hM, hM, hX, hY⟩ bY bY)).add
    (maj_tiltRay_eVal2 sw dm h hm₀ ⟨hM, hX, hX, hY⟩ bx bY)).add
    (maj_tiltRay_eVal2 sw dm h hm₀ ⟨hM, hX, hY, hY⟩ bx bx)).add
    (maj_tiltRay_eVal4 m₀ sw 0 dm bx bY M X Y bx bx bx)).const_mul
    (((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2))).congr fun _ _ => rfl

theorem maj_one_le_auxX {F : Type} [Fintype F] (Φ : Lepton.Flavors F)
    (hmass : ∀ g, 1 ≤ Φ.mass g) : 1 ≤ auxX Φ := by
  have := Finset.sum_nonneg (s := Finset.univ) fun g (_ : g ∈ Finset.univ) =>
    (zero_le_one.trans (hmass g))
  simp only [auxX]
  linarith

section Block

variable (P : Params) {F : Type} [Fintype F] (Φ : Lepton.Flavors F)
  (D : Counterterms F) (rep : F → F)

/-- **`MajTiltRay` of the block-summed bubble** at the pure mass insertion `ctδ D`. -/
theorem maj_tiltRay_fbVal (hmass : ∀ g, 1 ≤ Φ.mass g) (sw : Bool) {bx bY : Bool}
    (h : bx ≠ bY) :
    MajTiltRay fun k μ ν => fbVal P Φ (ctδ D) rep 1 sw bx bY k μ ν := by
  have hX := maj_one_le_auxX Φ hmass
  refine MajTiltRay.sum Finset.univ fun f _ => ?_
  refine ((maj_tiltRay_insVal sw (P.e ^ 2 * (ctδ D).dm (rep f) 0) h one_pos (hmass f) hX
    (Y := auxX Φ + 1) (by linarith)).const_mul ((Φ.coeff f : ℂ) * kF P.e)).congr fun s _ => ?_
  simp [ctδ]

end Block

/-- **`MajTiltRay` of the limit of the weighted mass-derivative block** at `decCfg 1 4`. -/
theorem maj_tiltRay_fLim (P : Params) (he : P.e ≠ 0) :
    MajTiltRay (fLim (decCfg 1 4) (fun _ => 0) P.e fun _ => 1) := by
  have hmass : ∀ g, (1 : ℝ) ≤ (decCfg 1 4).mass g :=
    dec_cfg_mass_ge le_rfl one_pos (by norm_num)
  have hpv := dec_cfg_pv (μ := 1) one_ne_zero (by norm_num : (0 : ℝ) ≤ 4)
  have hrep : ∀ f : Fin 3, (fun _ : Fin 3 => (0 : Fin 3)) ((fun _ => 0) f) = (fun _ => 0) f :=
    fun _ => rfl
  refine ((maj_tiltRay_fbVal P (decCfg 1 4) (ctOf P.e fun _ => 1) (fun _ => 0) hmass true
    (by decide : true ≠ false)).add (maj_tiltRay_fbVal P (decCfg 1 4) (ctOf P.e fun _ => 1)
      (fun _ => 0) hmass false (by decide : false ≠ true))).congr fun s hs => ?_
  have hk : -(4 * (1 : ℝ) ^ 2) < Minkowski.dot (majRayVec s) (majRayVec s) := by
    rw [dot_majRayVec (by linarith)]
    linarith
  exact (fLim_eq_fbVal P (decCfg 1 4) (fun _ => 0) one_pos hmass hrep hpv.1 hpv.2 he _ hk 2
    3).symm

/-- **(L10) `MajGrowD`.** -/
theorem maj_growD (P : Params) (he : P.e ≠ 0) : MajGrowD P.e :=
  maj_growD_of_tiltRay P he (maj_tiltRay_fLim P he)

end QED.GradedProof.RPi4

end
