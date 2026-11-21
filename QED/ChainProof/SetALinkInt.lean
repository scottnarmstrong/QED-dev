/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkSum

/-!
# The integrability goal (HA₀) from nine class obligations

Helper for the Phase 5 Stage 3a goal (HA₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setA`
(decision D-58). Every graded contraction of graded order `7` satisfying (A₁) is a relabelling of
one of the nine representatives at its grading (`QED.ChainProof.SetALink.exists_rep_setA`), the
representatives are 1PI, and (T₉′) for the graded integrand of a 1PI contraction passes to its
relabellings under momentum conservation
(`QED.GradedProof.VP2.jointEnergyFirstIntegrable_relabelK_graded`). So (HA₀) reduces to the class
obligation `ClassIntA R.rep R.grad` (the same (T₉′), under the same hypotheses `IntHypA`) for the
nine representatives: `jointEnergyFirstIntegrable_setA_of_classes`, stated with exactly the
hypotheses and conclusion of (HA₀) after the nine class obligations.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetALink

open QED.WickModel QED.TwoLoop.Relabel QED.ChainProof.Enum

/-- **The standing hypotheses of (HA₀)**: a positive Feynman regulator `ε`, an idempotent scheme
map `rep` whose classes satisfy the two Pauli–Villars conditions, and level-`0` fermion
counterterm data constant on the classes. -/
structure IntHypA (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Graded.Counterterms F) (rep : F → F) : Prop where
  hε : 0 < P.ε
  hrep : ∀ f, rep (rep f) = rep f
  hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0
  hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0
  hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
    D.dm f 0 = D.dm (rep f) 0

/-- **The class obligation**: (T₉′) for the graded integrand of a vertex contraction at the
grading `g`, under the hypotheses of (HA₀), at all external momenta with momentum conservation
and all external indices. -/
def ClassIntA {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
    (g : Graded.Grading κ) : Prop :=
  ∀ (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Graded.Counterterms F) (rep : F → F), IntHypA P Φ D rep →
    ∀ (pOut pIn kIn : Fin 1 → Fin 4 → ℝ), pOut 0 = pIn 0 + kIn 0 →
      ∀ αOut βIn μ : Fin 1 → Fin 4,
        QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
          (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
            Graded.regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut
              βIn μ

/-- The class obligation passes to relabellings of 1PI contractions, at the transported
grading. -/
theorem classIntA_relabelK {N : ℕ} {κ κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
    (hκ : ∀ t, κ' (π t) = κ t) {C : Contraction 1 1 κ} (hC : IsOnePI C) {g : Graded.Grading κ}
    (h : ClassIntA C g) : ClassIntA (relabelK π hκ C) (QED.GradedProof.VP2.gradMap π hκ g) := by
  intro P F _ _ Φ D rep hH pOut pIn kIn hmom αOut βIn μ
  exact QED.GradedProof.VP2.jointEnergyFirstIntegrable_relabelK_graded Φ P D π hκ hC g
    (by simpa using hmom) αOut βIn μ (h P Φ D rep hH pOut pIn kIn hmom αOut βIn μ)

/-- **(HA₀) from the nine class obligations**, with exactly the hypotheses and conclusion of
`QED.ThreeLoop.jointEnergyFirstIntegrable_setA` after the class obligations. -/
theorem jointEnergyFirstIntegrable_setA_of_classes (hP : ∀ s, ClassIntA (repP s) gradP)
    (hGW : ClassIntA repGW 0) (hGU : ClassIntA repGU 0) (hFA : ClassIntA repFA 0)
    (hFB : ClassIntA repFB 0) (hVA : ClassIntA repVA 0) (hVB : ClassIntA repVB 0)
    (hVC : ClassIntA repVC 0)
    (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (rep : F → F) (hε : 0 < P.ε)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} (g : Graded.Grading κ)
    (hg : Graded.gradedOrder κ g = 7) (C : Contraction 1 1 κ) (hC : QED.ThreeLoop.IsSetA C)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 1 → Fin 4 → ℝ) (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        Graded.regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn
          μ := by
  have hcl : ∀ R ∈ repsA N, ClassIntA R.rep R.grad := by
    refine repsA_cases (fun _ R => ClassIntA R.rep R.grad) ?_ ?_ ?_ ?_
    · simp only [repsA4, List.mem_cons, List.not_mem_nil, or_false]
      rintro R (rfl | rfl) <;> exact hP _
    · simp only [repsA5, List.mem_cons, List.not_mem_nil, or_false]
      rintro R (rfl | rfl)
      exacts [hGW, hGU]
    · simp only [repsA6, List.mem_cons, List.not_mem_nil, or_false]
      rintro R (rfl | rfl)
      exacts [hFA, hFB]
    · simp only [repsA7, List.mem_cons, List.not_mem_nil, or_false]
      rintro R (rfl | rfl | rfl)
      exacts [hVA, hVB, hVC]
  obtain ⟨R, hR, π, hκ, rfl, rfl⟩ := exists_rep_setA g hg hC
  exact classIntA_relabelK π hκ (repsA_props R hR).1 (hcl R hR) P Φ D rep
    ⟨hε, hrep, hPV₁, hPV₂, hD⟩ pOut pIn kIn hmom αOut βIn μ

end QED.ChainProof.SetALink

end
