/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0Enum
public import QED.GradedProof.X0Sep

/-!
# (X₀): every open-line contraction of five gauge vertices

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), step X0d. The three
contractions of `sixList` (two one-loop self-energies) pass the separated criterion `SepCrit`
(`sixList_sepCrit`, kernel evaluation), so with `jointEnergyFirstIntegrable_open_or_six` every
attached connected contraction of five `gauge` vertices without a closed fermion loop satisfies
(T₉′) at the zero grading, for any masses and `ε > 0` (`jointEnergyFirstIntegrable_open`).
-/

@[expose] public section

namespace QED.GradedProof.X0

open QED.WickModel (Params Contraction Line lineMomentum₂ loopCount ExternalsAttached
  VerticesConnected)
open QED.TwoLoop.Enumeration (gauges withSigma relabel lineData relabel_mul relabel_one
  externalsAttached_relabel_iff)
open QED.TwoLoop.Relabel (verticesConnected_relabel_iff)

theorem sixList_sepCrit : ∀ C ∈ sixList, SepCrit (lineData C) := by decide +kernel

/-- (T₉′) at T1 for a member of `sixList`. -/
theorem jointEnergyFirstIntegrable_six (P : Params) (hε : 0 < P.ε)
    {C : Contraction 1 1 (gauges 5)} (hC : C ∈ sixList)
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (pOut pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        QED.WickModel.regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn
          μ := by
  rw [withSigma0_loopCount C (List.mem_of_mem_filter hC)]
  simp only [QED.TwoLoop.Insertion.regulatedAmplitude₂_eq_zeroFlavoring P hcyc]
  exact jointEnergyFirstIntegrable_of_sepCrit P hε gauges5 _ (sixList_sepCrit C hC) pOut pIn kIn
    αOut βIn μ _

open scoped Classical in
/-- **(X₀) for the open-line contractions of five gauge vertices**, at the zero grading. -/
theorem jointEnergyFirstIntegrable_open (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : QED.Graded.Counterterms F) (hε : 0 < P.ε)
    (C : Contraction 1 1 (gauges 5)) (hA : ExternalsAttached C) (hV : VerticesConnected C)
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (pOut pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin 1 → Fin 4 → ℝ) (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        QED.Graded.regulatedAmplitude P Φ D C 0 pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn
          μ := by
  rcases jointEnergyFirstIntegrable_open_or_six P Φ D hε C hA hV hcyc pOut pIn kIn hmom αOut βIn
    μ with h | ⟨ρ, hρ⟩
  · exact h
  have hcyc' := cycle_relabel ρ hcyc
  have hA' := (externalsAttached_relabel_iff ρ C).mpr hA
  have hV' := (verticesConnected_relabel_iff ρ C).mpr hV
  have hmom' : ∑ i, pOut i = ∑ i, pIn i + ∑ j, kIn j := by simp [hmom]
  have h := jointEnergyFirstIntegrable_relabel' (openParams P Φ) ρ⁻¹ hA' hV' hmom' αOut βIn μ
    (jointEnergyFirstIntegrable_six (openParams P Φ) hε hρ hcyc' pOut pIn kIn αOut βIn μ)
  rw [← relabel_mul, inv_mul_cancel, relabel_one] at h
  simp only [QED.TwoLoop.Insertion.regulatedAmplitude₂_eq_zeroFlavoring _ hcyc] at h
  simpa only [regulatedAmplitude_zero_eq_contractionAmplitude₂ P Φ D gauges5 C hcyc] using h

end QED.GradedProof.X0

end
