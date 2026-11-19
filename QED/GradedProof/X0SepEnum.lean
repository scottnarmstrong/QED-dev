/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0SepCrit
public import QED.GradedProof.X0Enum
public import QED.GradedProof.VP2Relabel

/-!
# (X₀): the separated two-loop contractions with closed loops

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), part A of
`TwoLoopClosedGoal`. Every attached connected contraction of five `gauge` vertices is a
relabelling of one whose fermion pairing is in normal form (`stdList`), and (T₉′) of the graded
integrand passes to relabellings (`jointEnergyFirstIntegrable_relabel_graded`, as
`QED.GradedProof.VP2.jointEnergyFirstIntegrable_relabelK_graded` without irreducibility). So
`TwoLoopClosedGoal` reduces to the normal forms (`twoLoopClosedGoal_of_std`). Among the
normal-form contractions with a closed fermion loop, those whose two loops share no line are to
pass `SepClosedCrit` (`SepCheck`, checked by kernel evaluation in `X0SepCheck`).
-/

@[expose] public section

namespace QED.GradedProof.X0

open QED.Graded
open QED.WickModel (Params Contraction ExternalsAttached VerticesConnected loopCount
  lineMomentum₂ externalMomentum)
open QED.TwoLoop.Enumeration (gauges withSigma stdList
  exists_std lineData reachE relabel relabel_mul relabel_one externalsAttached_relabel_iff)
open QED.TwoLoop.Relabel (relabelK verticesConnected_relabelK_iff loopCount_relabelK
  relabelCorrK externalMomentum_relabelK sum_externalMomentum)
open QED.GradedProof.VP2 (gradMap regulatedAmplitude_relabelK)

variable {F : Type} [Fintype F] [DecidableEq F]

/-- **(T₉′) for the graded integrand passes to relabellings** of an attached connected
contraction, under momentum conservation. -/
theorem jointEnergyFirstIntegrable_relabel_graded (P : Params) (Φ : Lepton.Flavors F)
    (D : Counterterms F) {nf nA N : ℕ} {κ κ' : Fin N → Wick.VertexKind}
    (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t) {C : Contraction nf nA κ}
    (hA : ExternalsAttached C) (hV : VerticesConnected C) (g : Grading κ)
    {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ}
    (hmom : ∑ i, pOut i = ∑ i, pIn i + ∑ j, kIn j) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4)
    (h : QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount (relabelK π hκ C)) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount (relabelK π hκ C)) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude P Φ D (relabelK π hκ C) (gradMap π hκ g) pIn kIn
          (lineMomentum₂ (relabelK π hκ C) pOut pIn kIn ℓ) αOut βIn μ := by
  have hsum : ∑ v, externalMomentum C pOut pIn kIn v = 0 := by
    rw [sum_externalMomentum hA, hmom, sub_self]
  have hV' := (verticesConnected_relabelK_iff π hκ C).mpr hV
  have hL' := loopCount_relabelK π hκ C hV
  obtain ⟨M, hM, a, hr⟩ := (relabelCorrK π hκ C).exists_routing_change hV hV'
    (externalMomentum_relabelK π hκ C pOut pIn kIn) hsum rfl hL'
  rw [hL']
  exact QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_of_matAct M hM a h fun ℓ => by
    rw [regulatedAmplitude_relabelK, hr]

/-- The normal-form goal: `TwoLoopClosedGoal` for the contractions whose fermion pairing is in
`stdList`. -/
def TwoLoopStdGoal (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F) : Prop :=
  ∀ C : Contraction 1 1 (gauges 5), C.1.1 ∈ stdList → ExternalsAttached C →
    VerticesConnected C → ¬ (∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) →
    ∀ pOut pIn kIn : Fin 1 → Fin 4 → ℝ, pOut 0 = pIn 0 + kIn 0 → ∀ αOut βIn μ : Fin 1 → Fin 4,
      QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C)
        (integrand P Φ D C 0 pOut pIn kIn αOut βIn μ)

theorem relabelK_gauges (π : Equiv.Perm (Fin 5)) (C : Contraction 1 1 (gauges 5)) :
    relabelK π (fun _ => rfl) C = relabel π C := rfl

/-- **`TwoLoopClosedGoal` from the normal forms.** -/
theorem twoLoopClosedGoal_of_std (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
    (h : TwoLoopStdGoal P Φ D) : TwoLoopClosedGoal P Φ D := by
  intro C hA hV hcyc pOut pIn kIn hmom αOut βIn μ
  obtain ⟨ρ, hρ⟩ := exists_std C.1.1
  have hA' := (externalsAttached_relabel_iff ρ C).mpr hA
  have hV' := (QED.TwoLoop.Relabel.verticesConnected_relabel_iff ρ C).mpr hV
  have hback : relabel ρ⁻¹ (relabel ρ C) = C := by
    rw [← relabel_mul, inv_mul_cancel, relabel_one]
  have hcyc' : ¬ ∀ x, Equiv.Perm.SameCycle (relabel ρ C).1.1 x (.inl 0) := fun h' => by
    have := cycle_relabel ρ⁻¹ h'
    rw [hback] at this
    exact hcyc this
  have hmom' : ∑ i, pOut i = ∑ i, pIn i + ∑ j, kIn j := by simp [hmom]
  have hρ' : (relabel ρ C).1.1 ∈ stdList := hρ
  have h0 := h (relabel ρ C) hρ' hA' hV' hcyc' pOut pIn kIn hmom αOut βIn μ
  unfold integrand at h0
  have h1 := jointEnergyFirstIntegrable_relabel_graded P Φ D ρ⁻¹ (κ := gauges 5)
    (κ' := gauges 5) (fun _ => rfl) hA' hV' (0 : Grading (gauges 5)) hmom' αOut βIn μ h0
  rw [relabelK_gauges, QED.GradedProof.VP2.gradMap_zero, hback] at h1
  exact h1

/-! ### The kernel check -/

/-- The separated test for one fermion pairing. -/
def SepCheckσ (σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5))) : Prop :=
  ∀ C ∈ withSigma σ, C.1.2 (.inl 0) ≠ .inl 0 →
    (∀ (h : 0 < 5) (w : Fin 5), w ∈ reachE (lineData C) (fun _ => true) ⟨0, h⟩ 5) →
      SepLines C → SepClosedCrit C

instance (σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5))) : Decidable (SepCheckσ σ) := by
  unfold SepCheckσ; infer_instance

/-- The separated test for a list of fermion pairings. -/
def SepCheck (L : List (Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5)))) : Prop :=
  ∀ σ ∈ L, σ (.inl 0) ≠ .inl 0 → ¬ (∀ x, Equiv.Perm.SameCycle σ x (.inl 0)) → SepCheckσ σ

instance (L : List (Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5)))) :
    Decidable (SepCheck L) := by
  unfold SepCheck; infer_instance

/-- Five `gauge` vertices with attached externals, connected: two loops. -/
theorem loopCount_gauges_five {C : Contraction 1 1 (gauges 5)} (hA : ExternalsAttached C)
    (hV : VerticesConnected C) : loopCount C = 2 := by
  have h := QED.TwoLoop.LoopBoundTwo.two_mul_loopCount_add_eq hA hV (by norm_num)
  have h5 : (Finset.univ.filter fun t : Fin 5 => gauges 5 t = .gauge ∨
      gauges 5 t = .gaugeCt).card = 5 := by decide
  omega

end QED.GradedProof.X0

end
