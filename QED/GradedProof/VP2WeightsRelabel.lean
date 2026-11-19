/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2Classes
public import QED.GradedProof.VP2Relabel
public import QED.Frozen.Graded.ContractionValue

/-!
# Relabelling invariance of graded values and the signs of the representatives

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2, step L0.

* `contractionValue_relabelK`: the graded value (G₅) of a relabelled 1PI contraction at the
  transported grading is that of the contraction, under momentum conservation (the integral form
  of `QED.GradedProof.VP2.jointEnergyFirstIntegrable_relabelK_graded`).
* `fermionSign_repVA`, …: every representative of `QED/GradedProof/VP2Classes.lean` has fermion
  sign `-1` (one closed loop).
* `onePIG1_nodup`, …: the enumeration lists have no repetitions.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.VP2

open QED.Graded QED.TwoLoop.Relabel QED.TwoLoop.Routing QED.TwoLoop.Enumeration
open QED.GradedProof.SE2
open QED.WickModel (Params Contraction IsOnePI VerticesConnected externalMomentum loopCount
  lineMomentum₂ Line fermionSign)

variable {nf nA N : ℕ} {κ κ' : Fin N → Wick.VertexKind} {F : Type} [Fintype F] [DecidableEq F]

/-- **Relabelling invariance of the graded value** (G₅) of a 1PI contraction across kind
sequences, at the transported grading, under momentum conservation. -/
theorem contractionValue_relabelK (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
    (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t) {C : Contraction nf nA κ}
    (hC : IsOnePI C) (g : Grading κ) {pOut pIn : Fin nf → Fin 4 → ℝ}
    {kIn : Fin nA → Fin 4 → ℝ} (hmom : ∑ i, pOut i = ∑ i, pIn i + ∑ j, kIn j)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionValue P Φ D (relabelK π hκ C) (gradMap π hκ g) pOut pIn kIn αOut βIn μ =
      contractionValue P Φ D C g pOut pIn kIn αOut βIn μ := by
  have hV := hC.2.1
  have hsum : ∑ v, externalMomentum C pOut pIn kIn v = 0 := by
    rw [sum_externalMomentum hC.1, hmom, sub_self]
  have hV' := (verticesConnected_relabelK_iff π hκ C).mpr hV
  have hL' := loopCount_relabelK π hκ C hV
  obtain ⟨M, hM, a, hr⟩ := (relabelCorrK π hκ C).exists_routing_change hV hV'
    (externalMomentum_relabelK π hκ C pOut pIn kIn) hsum rfl hL'
  unfold contractionValue
  revert hr
  generalize loopCount (relabelK π hκ C) = L at hL' ⊢
  subst hL'
  intro hr
  simp only [regulatedAmplitude_relabelK, hr]
  exact QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add _
    (fun ℓ => (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ) M hM a

/-- Momentum conservation of the two-photon kinematics. -/
theorem mom_two (k : Fin 4 → ℝ) :
    ∑ i, (![] : Fin 0 → Fin 4 → ℝ) i = ∑ i, (![] : Fin 0 → Fin 4 → ℝ) i + ∑ j, ![k, -k] j := by
  simp [Fin.sum_univ_two]

/-! ### The signs of the representatives -/

theorem fermionSign_repVA : fermionSign repVA = -1 := by decide +kernel
theorem fermionSign_repVB : fermionSign repVB = -1 := by decide +kernel
theorem fermionSign_repVC : fermionSign repVC = -1 := by decide +kernel
theorem fermionSign_repG0 : fermionSign repG0 = -1 := by decide +kernel
theorem fermionSign_repG1 : fermionSign repG1 = -1 := by decide +kernel
theorem fermionSign_repF0 : fermionSign repF0 = -1 := by decide +kernel
theorem fermionSign_repF1 : fermionSign repF1 = -1 := by decide +kernel

/-! ### No repetitions in the enumeration -/

theorem onePI2_gC_nodup : onePI2_gC.Nodup := by decide +kernel
theorem onePI2_Cg_nodup : onePI2_Cg.Nodup := by decide +kernel
theorem onePI2_ggf_nodup : onePI2_ggf.Nodup := by decide +kernel
theorem onePI2_gfg_nodup : onePI2_gfg.Nodup := by decide +kernel
theorem onePI2_fgg_nodup : onePI2_fgg.Nodup := by decide +kernel
theorem onePIG1_nodup : onePIG1.Nodup := by decide +kernel
theorem onePIG2_nodup : onePIG2.Nodup := by decide +kernel
theorem onePIG3_nodup : onePIG3.Nodup := by decide +kernel
theorem onePIG4_nodup : onePIG4.Nodup := by decide +kernel

end QED.GradedProof.VP2

end
