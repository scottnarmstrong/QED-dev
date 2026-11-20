/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CPeelDefs

/-!
# (X₁) piece C: the peeled vertex set of the out-leg

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (the graph theory of the out-leg peel); the mirror of the
in-leg part of `X1CPeelDefs`. For an out-leg self-energy cut `PeelOutCut C f` (a fermion bridge
whose head side carries no external photon):

* `peelOut C`: the head side of an out-cut with fewest vertices (`∅` if there is none), the
  vertex set of the self-energy peeled off the out-leg (`peelOut_spec`);
  `peelOut_eq_of_forall`: a cut whose head side lies in the head side of every cut is the peeled
  one.
* `peelRedOut`: out-leg reducible (an out-cut exists); `peelOutSelH`: the class of the out-leg
  peel, `peelSelG ∧ ¬ peelRedIn`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line FermionLine)
open Relation Finset

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

open scoped Classical in
/-- An out-cut with fewest vertices on its head side exists when a cut does. -/
theorem peelOut_exists_min (C : Contraction nf nA κ) (h : ∃ f, PeelOutCut C f) :
    ∃ f, PeelOutCut C f ∧ ∀ f', PeelOutCut C f' →
      (peelSide C (.inl f) f.1.1).card ≤ (peelSide C (.inl f') f'.1.1).card := by
  obtain ⟨f₀, hf₀⟩ := h
  obtain ⟨f, hf, hmin⟩ := (univ.filter (PeelOutCut C)).exists_min_image
    (fun f => (peelSide C (.inl f) f.1.1).card) ⟨f₀, by simp [hf₀]⟩
  exact ⟨f, (mem_filter.1 hf).2, fun f' hf' => hmin f' (by simp [hf'])⟩

/-- The out-cut with fewest vertices on its head side. -/
noncomputable def peelOutMin (C : Contraction nf nA κ) (h : ∃ f, PeelOutCut C f) :
    FermionLine C :=
  (peelOut_exists_min C h).choose

open scoped Classical in
/-- **The peeled vertex set of the out-leg**: the head side of the out-cut with fewest
vertices. -/
noncomputable def peelOut (C : Contraction nf nA κ) : Finset (Fin N) :=
  if h : ∃ f, PeelOutCut C f then peelSide C (.inl (peelOutMin C h)) (peelOutMin C h).1.1
  else ∅

/-- The peeled set is the head side of a cut with fewest vertices. -/
theorem peelOut_spec (C : Contraction nf nA κ) (h : ∃ f, PeelOutCut C f) :
    ∃ f, PeelOutCut C f ∧ (∀ f', PeelOutCut C f' →
      (peelSide C (.inl f) f.1.1).card ≤ (peelSide C (.inl f') f'.1.1).card) ∧
      peelOut C = peelSide C (.inl f) f.1.1 := by
  refine ⟨peelOutMin C h, (peelOut_exists_min C h).choose_spec.1,
    (peelOut_exists_min C h).choose_spec.2, ?_⟩
  simp only [peelOut, h, ↓reduceDIte]

/-- **A cut whose head side lies in the head side of every cut is the peeled one.** -/
theorem peelOut_eq_of_forall {C : Contraction nf nA κ} {f : FermionLine C}
    (hf : PeelOutCut C f)
    (hall : ∀ f', PeelOutCut C f' → peelSide C (.inl f) f.1.1 ⊆ peelSide C (.inl f') f'.1.1) :
    peelOut C = peelSide C (.inl f) f.1.1 := by
  obtain ⟨f₀, hf₀, hmin, heq⟩ := peelOut_spec C ⟨f, hf⟩
  rw [heq]
  exact (eq_of_subset_of_card_le (hall f₀ hf₀) (hmin f hf)).symm

/-- Out-leg reducible: the contraction has an out-leg self-energy cut. -/
abbrev peelRedOut : CountSel 1 1 := fun C _ => ∃ f, PeelOutCut C f

/-- The class of the out-leg peel: selected and not in-leg reducible. -/
abbrev peelOutSelH : CountSel 1 1 := fun C g => peelSelG C g ∧ ¬ peelRedIn C g

end QED.GradedProof.X1C

end
