/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0TwoLoop
public import QED.GradedProof.X0Link
public import QED.TwoLoop.EnumerationGauge5
public import QED.TwoLoop.IntegrableOrderFiveTransfer

/-!
# (X₀): the open-line contractions of five gauge vertices

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), step X0d.7. Let `C`
be an attached connected contraction of five `gauge` vertices with one fermion pair and one
photon whose fermion fields all lie on the cycle of the external field (no closed loop). It is a
relabelling of one of the fifteen contractions `withSigma sigma0` with the open line
`0 → 1 → 2 → 3 → 4`. Twelve of them pass the Boolean tests `EdgeCrit`, `EdgeSize`; the other
three (`sixList`, two one-loop self-energies, six parametric lines on the loops) do not. So the
graded integrand of `C` at the zero grading satisfies (T₉′), unless `C` is a relabelling of a
member of `sixList` (`jointEnergyFirstIntegrable_open_or_six`).

All checks are kernel evaluations (`decide +kernel`, peak memory about 4.3 GB including the
imports).
-/

@[expose] public section

namespace QED.GradedProof.X0

open QED.WickModel (Params Contraction Line lineMomentum₂ loopCount ExternalsAttached
  VerticesConnected externalMomentum)
open QED.TwoLoop.Enumeration (gauges withSigma fermionPerm stdList exists_std relabel extF
  mem_withSigma lineData relabel_mul relabel_one externalsAttached_relabel_iff)
open QED.TwoLoop.Relabel (verticesConnected_relabel_iff loopCount_relabel relabelCorr
  externalMomentum_relabel sum_externalMomentum regulatedAmplitude₂_relabel)

/-- The open line `0 → 1 → 2 → 3 → 4`. -/
def sigma0 : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5)) := fermionPerm [0, 1, 2, 3, 4] []

/-- The three open-line contractions with six parametric lines on the loops. -/
def sixList : List (Contraction 1 1 (gauges 5)) :=
  (withSigma sigma0).filter fun C => edgeLoopWeight (lineData C) = 6

theorem sigma0_cycle : ∀ x, Equiv.Perm.SameCycle sigma0 x (.inl 0) := by decide +kernel

theorem eq_sigma0_of_mem_stdList : ∀ σ ∈ stdList,
    (∀ x, Equiv.Perm.SameCycle σ x (.inl 0)) → σ = sigma0 := by decide +kernel

/-- **The fifteen open-line contractions in normal form.** -/
theorem withSigma0_classify : ∀ C ∈ withSigma sigma0,
    (EdgeCrit (lineData C) ∧ EdgeSize (lineData C)) ∨ C ∈ sixList := by decide +kernel

open QED.TwoLoop.Enumeration in
theorem withSigma0_loopCount : ∀ C ∈ withSigma sigma0, loopCount C = 2 := by
  intro C hC
  rw [loopCount_eq_card]
  revert C
  decide +kernel

theorem gauges5 : ∀ t : Fin 5, gauges 5 t = .gauge := fun _ => rfl

/-- Relabelling keeps every fermion field on the cycle of the external field. -/
theorem cycle_relabel (ρ : Equiv.Perm (Fin 5)) {C : Contraction 1 1 (gauges 5)}
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) :
    ∀ x, Equiv.Perm.SameCycle (relabel ρ C).1.1 x (.inl 0) := by
  intro x
  have h := (hcyc (((extF ρ : Equiv.Perm _))⁻¹ x)).conj (g := (extF ρ : Equiv.Perm _))
  have he : (relabel ρ C).1.1 = (extF ρ : Equiv.Perm _) * C.1.1 * (extF ρ : Equiv.Perm _)⁻¹ :=
    Equiv.ext fun _ => rfl
  rw [he]
  simpa using h

/-- (T₉′) passes to relabellings of attached connected contractions (as
`QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_relabel`, without irreducibility). -/
theorem jointEnergyFirstIntegrable_relabel' (P : Params) {N nf nA : ℕ} (π : Equiv.Perm (Fin N))
    {C : Contraction nf nA (gauges N)} (hA : ExternalsAttached C) (hV : VerticesConnected C)
    {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ}
    (hmom : ∑ i, pOut i = ∑ i, pIn i + ∑ j, kIn j) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4)
    (h : QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        QED.WickModel.regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn
          μ) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount (relabel π C)) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount (relabel π C)) : ℝ) : ℂ)⁻¹ *
        QED.WickModel.regulatedAmplitude₂ P (relabel π C) pIn kIn
          (lineMomentum₂ (relabel π C) pOut pIn kIn ℓ) αOut βIn μ := by
  have hsum : ∑ v, externalMomentum C pOut pIn kIn v = 0 := by
    rw [sum_externalMomentum hA, hmom, sub_self]
  have hV' := (verticesConnected_relabel_iff π C).mpr hV
  have hL' := loopCount_relabel π C hV
  obtain ⟨M, hM, a, hr⟩ := (relabelCorr π C).exists_routing_change hV hV'
    (externalMomentum_relabel π C pOut pIn kIn) hsum rfl hL'
  rw [hL']
  exact QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_of_matAct M hM a h
    fun ℓ => by rw [regulatedAmplitude₂_relabel, hr]

/-- (T₉′) at T1 for a normal-form contraction passing the tests. -/
theorem jointEnergyFirstIntegrable_std (P : Params) (hε : 0 < P.ε) {C : Contraction 1 1 (gauges 5)}
    (hC : C ∈ withSigma sigma0) (hcrit : EdgeCrit (lineData C)) (hsize : EdgeSize (lineData C))
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (pOut pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        QED.WickModel.regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn
          μ := by
  rw [withSigma0_loopCount C hC]
  simp only [QED.TwoLoop.Insertion.regulatedAmplitude₂_eq_zeroFlavoring P hcyc]
  exact jointEnergyFirstIntegrable_of_edgeCrit P hε gauges5 _ hcrit hsize pOut pIn kIn αOut βIn
    μ _

open scoped Classical in
/-- **(X₀) for the open-line contractions of five gauge vertices**, at the zero grading: (T₉′)
holds unless the contraction is a relabelling of a member of `sixList`. -/
theorem jointEnergyFirstIntegrable_open_or_six (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : QED.Graded.Counterterms F) (hε : 0 < P.ε)
    (C : Contraction 1 1 (gauges 5)) (hA : ExternalsAttached C) (hV : VerticesConnected C)
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (pOut pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin 1 → Fin 4 → ℝ) (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    (QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        QED.Graded.regulatedAmplitude P Φ D C 0 pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn
          μ) ∨ ∃ ρ : Equiv.Perm (Fin 5), relabel ρ C ∈ sixList := by
  obtain ⟨ρ, hρ⟩ := exists_std C.1.1
  have hcyc' := cycle_relabel ρ hcyc
  have hσ : (relabel ρ C).1.1 = sigma0 := eq_sigma0_of_mem_stdList _ hρ hcyc'
  have hmem : relabel ρ C ∈ withSigma sigma0 := hσ ▸ mem_withSigma (relabel ρ C)
  rcases withSigma0_classify _ hmem with ⟨hcrit, hsize⟩ | hsix
  · left
    have hA' := (externalsAttached_relabel_iff ρ C).mpr hA
    have hV' := (verticesConnected_relabel_iff ρ C).mpr hV
    have hmom' : ∑ i, pOut i = ∑ i, pIn i + ∑ j, kIn j := by simp [hmom]
    have h := jointEnergyFirstIntegrable_relabel' (openParams P Φ) ρ⁻¹ hA' hV' hmom' αOut βIn μ
      (jointEnergyFirstIntegrable_std (openParams P Φ) hε hmem hcrit hsize hcyc' pOut pIn kIn
        αOut βIn μ)
    rw [← relabel_mul, inv_mul_cancel, relabel_one] at h
    simp only [QED.TwoLoop.Insertion.regulatedAmplitude₂_eq_zeroFlavoring _ hcyc] at h
    simpa only [regulatedAmplitude_zero_eq_contractionAmplitude₂ P Φ D gauges5 C hcyc] using h
  · exact Or.inr ⟨ρ, hsix⟩

end QED.GradedProof.X0

end
