/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkSum
public import QED.ChainProof.SetALinkInt

/-!
# The integrability goal (HS₀) from the class obligations

Helper for the Phase 5 Stage 3 goal (HS₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setC`
(decision D-58). Every 1PI graded contraction of graded order `7` satisfying (Sc₃) is a
relabelling of one of the 56 representatives at its grading
(`QED.ChainProof.SetCLink.exists_rep_setC`), the representatives are 1PI (`repsC_props`), and
the class obligation `QED.ChainProof.SetALink.ClassIntA` ((T₉′) for the graded integrand under the
hypotheses `IntHypA` of (HA₀), which are those of (HS₀)) passes to relabellings of 1PI
contractions (`QED.ChainProof.SetALink.classIntA_relabelK`). So (HS₀) reduces to the class
obligations of the 56 representatives, collected by family in `ClassesC`:
`jointEnergyFirstIntegrable_setC_of_classes`, stated with exactly the hypotheses and conclusion of
(HS₀) after the class obligations.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetCLink

open QED.WickModel QED.TwoLoop.Relabel QED.ChainProof.SetALink

/-- **The class obligations of (HS₀)**, by family: (T₉′) for the graded integrand of each of the
56 representatives at its grading. -/
structure ClassesC : Prop where
  hB : ∀ i, ClassIntA (repB i) 0
  hD : ∀ i s, ClassIntA (repD i s) 0
  hCB0 : ClassIntA repCB0 0
  hCB1 : ClassIntA repCB1 0
  hCB2 : ClassIntA repCB2 0
  hCB3 : ClassIntA repCB3 0
  hCB4 : ClassIntA repCB4 0
  hCD0 : ∀ s, ClassIntA (repCD0 s) 0
  hCD1 : ∀ s, ClassIntA (repCD1 s) 0
  hCD2 : ∀ s, ClassIntA (repCD2 s) 0
  hCD3 : ∀ s, ClassIntA (repCD3 s) 0
  hCD4 : ∀ s, ClassIntA (repCD4 s) 0
  hS0 : ClassIntA repS0 (gOne _)
  hS1 : ClassIntA repS1 (gOne _)
  hS2 : ClassIntA repS2 (gOne _)
  hS3 : ClassIntA repS3 (gOne _)
  hS4 : ClassIntA repS4 (gOne _)

/-- The family obligations give the class obligation of every representative. -/
theorem classIntA_repsC (h : ClassesC) {N : ℕ} : ∀ R ∈ repsC N, ClassIntA R.rep R.grad := by
  refine repsC_cases (fun _ R => ClassIntA R.rep R.grad) ?_ ?_ ?_ ?_ ?_
  · simp only [repsC, repsCZ, repsCS, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false]
    rintro R (rfl | rfl | rfl)
    exacts [h.hS2, h.hS3, h.hS4]
  · simp only [repsC, repsCZ, repsCS, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro R (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [h.hCD2 0, h.hCD2 1, h.hCD3 0, h.hCD3 1, h.hCD4 0, h.hCD4 1, h.hS0, h.hS1]
  · simp only [repsC, repsCZ, repsCS, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false]
    rintro R (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [h.hCB2, h.hCB3, h.hCB4, h.hCD0 0, h.hCD0 1, h.hCD1 0, h.hCD1 1]
  · simp only [repsC, repsCZ, repsCS, List.append_nil, List.mem_append, List.mem_flatMap,
      List.mem_finRange, true_and, List.mem_cons, List.not_mem_nil, or_false]
    rintro R (⟨i, rfl | rfl⟩ | rfl | rfl)
    exacts [h.hD i 0, h.hD i 1, h.hCB0, h.hCB1]
  · simp only [repsC, repsCZ, repsCS, List.append_nil, List.mem_map, List.mem_finRange,
      true_and]
    rintro R ⟨i, rfl⟩
    exact h.hB i

/-- **(HS₀) from the class obligations**, with exactly the hypotheses and conclusion of
`QED.ThreeLoop.jointEnergyFirstIntegrable_setC` after the class obligations. -/
theorem jointEnergyFirstIntegrable_setC_of_classes (h : ClassesC)
    (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (rep : F → F) (hε : 0 < P.ε)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} (g : Graded.Grading κ)
    (hg : Graded.gradedOrder κ g = 7) (C : Contraction 1 1 κ) (hC₁ : IsOnePI C)
    (hC : QED.ThreeLoop.IsSetC C g)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 1 → Fin 4 → ℝ) (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        Graded.regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn
          μ := by
  obtain ⟨R, hR, π, hκ, rfl, rfl⟩ := exists_rep_setC g hg hC₁ hC
  exact classIntA_relabelK π hκ (repsC_props R hR).1 (classIntA_repsC h R hR) P Φ D rep
    ⟨hε, hrep, hPV₁, hPV₂, hD⟩ pOut pIn kIn hmom αOut βIn μ

end QED.ChainProof.SetCLink

end
