/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CPeelReach
public import QED.GradedProof.X1CTadSide
public import QED.GradedProof.X1CCountSum

/-!
# (X₁) piece C: tadpole-free contractions, self-energy cuts and the peeled vertex set

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (the graph theory of the peels). For a contraction `C` with one
open fermion line (`nf = 1`):

* `PeelExtAt C T`: an external field is attached to a vertex in `T` (the out-vertex, the
  in-vertex or a photon-external vertex); `PeelNoPhotonAt C T`: no photon external is.
* `PeelTadFree C`: **tadpole-free**, both sides of every photon bridge carry an external (the
  negation is exactly the input of `contractionValue_eq_zero_of_isBridge`).
* `PeelInCut C f`: the fermion line `f` is an **in-leg self-energy cut**: a bridge whose tail side
  (which holds the in-vertex, `peel_tail_reach_in`) carries no photon external. `PeelOutCut`:
  the mirror on the head side (for the out-leg peel).
* `peelSide C l w`: the vertices joined to `w` without the line `l`, as a finset.
* `peelIn C`: the tail side of an in-cut with fewest vertices (`∅` if there is none); this is
  the vertex set of the self-energy peeled off the in-leg. `peelIn_eq_of_forall`: a cut whose
  tail side lies in the tail side of every cut is the peeled one.
* `peelSelG`, `peelRedIn`: the selections of the in-leg peel (attached, connected, tadpole-free;
  in-leg reducible).
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line FermionLine PhotonLine Joined IsBridge VerticesConnected
  ExternalsAttached)
open Relation Finset

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- An external field of `C` is attached to a vertex of `T`. -/
def PeelExtAt (C : Contraction 1 nA κ) (T : Fin N → Prop) : Prop :=
  (∃ s, C.1.1 (.inl 0) = .inr s ∧ T s.1) ∨ (∃ s, C.1.1 (.inr s) = .inl 0 ∧ T s.1) ∨
    ∃ j a, C.1.2 (.inl j) = .inr a ∧ T a.1

/-- No external photon of `C` is attached to a vertex of `T`. -/
def PeelNoPhotonAt (C : Contraction nf nA κ) (T : Fin N → Prop) : Prop :=
  ∀ j a, C.1.2 (.inl j) = .inr a → ¬ T a.1

/-- **Tadpole-free**: both sides of every photon bridge carry an external field. -/
def PeelTadFree (C : Contraction 1 nA κ) : Prop :=
  ∀ g : PhotonLine C, IsBridge (.inr g : Line C) → ∀ w, (w = g.1.1 ∨ w = g.head.1) →
    PeelExtAt C (tadComp C g w)

/-- **An in-leg self-energy cut**: a fermion bridge whose tail side carries no external photon. -/
def PeelInCut (C : Contraction nf nA κ) (f : FermionLine C) : Prop :=
  IsBridge (.inl f : Line C) ∧ PeelNoPhotonAt C (ReflTransGen (Joined C {.inl f}) f.tail.1)

/-- **An out-leg self-energy cut**: a fermion bridge whose head side carries no external
photon. -/
def PeelOutCut (C : Contraction nf nA κ) (f : FermionLine C) : Prop :=
  IsBridge (.inl f : Line C) ∧ PeelNoPhotonAt C (ReflTransGen (Joined C {.inl f}) f.1.1)

open scoped Classical in
/-- The vertices joined to `w` without the line `l`. -/
noncomputable def peelSide (C : Contraction nf nA κ) (l : Line C) (w : Fin N) :
    Finset (Fin N) :=
  univ.filter (ReflTransGen (Joined C {l}) w)

theorem mem_peelSide {C : Contraction nf nA κ} {l : Line C} {w v : Fin N} :
    v ∈ peelSide C l w ↔ ReflTransGen (Joined C {l}) w v := by
  classical
  simp [peelSide]

open scoped Classical in
/-- An in-cut with fewest vertices on its tail side exists when a cut does. -/
theorem peel_exists_minInCut (C : Contraction nf nA κ) (h : ∃ f, PeelInCut C f) :
    ∃ f, PeelInCut C f ∧ ∀ f', PeelInCut C f' →
      (peelSide C (.inl f) f.tail.1).card ≤ (peelSide C (.inl f') f'.tail.1).card := by
  obtain ⟨f₀, hf₀⟩ := h
  obtain ⟨f, hf, hmin⟩ := (univ.filter (PeelInCut C)).exists_min_image
    (fun f => (peelSide C (.inl f) f.tail.1).card) ⟨f₀, by simp [hf₀]⟩
  exact ⟨f, (mem_filter.1 hf).2, fun f' hf' => hmin f' (by simp [hf'])⟩

/-- The in-cut with fewest vertices on its tail side. -/
noncomputable def peelInMin (C : Contraction nf nA κ) (h : ∃ f, PeelInCut C f) :
    FermionLine C :=
  (peel_exists_minInCut C h).choose

open scoped Classical in
/-- **The peeled vertex set of the in-leg**: the tail side of the in-cut with fewest vertices. -/
noncomputable def peelIn (C : Contraction nf nA κ) : Finset (Fin N) :=
  if h : ∃ f, PeelInCut C f then peelSide C (.inl (peelInMin C h)) (peelInMin C h).tail.1
  else ∅

/-- The peeled set is the tail side of a cut with fewest vertices. -/
theorem peelIn_spec (C : Contraction nf nA κ) (h : ∃ f, PeelInCut C f) :
    ∃ f, PeelInCut C f ∧ (∀ f', PeelInCut C f' →
      (peelSide C (.inl f) f.tail.1).card ≤ (peelSide C (.inl f') f'.tail.1).card) ∧
      peelIn C = peelSide C (.inl f) f.tail.1 := by
  refine ⟨peelInMin C h, (peel_exists_minInCut C h).choose_spec.1,
    (peel_exists_minInCut C h).choose_spec.2, ?_⟩
  simp only [peelIn, h, ↓reduceDIte]

/-- **A cut whose tail side lies in the tail side of every cut is the peeled one.** -/
theorem peelIn_eq_of_forall {C : Contraction nf nA κ} {f : FermionLine C} (hf : PeelInCut C f)
    (hall : ∀ f', PeelInCut C f' →
      peelSide C (.inl f) f.tail.1 ⊆ peelSide C (.inl f') f'.tail.1) :
    peelIn C = peelSide C (.inl f) f.tail.1 := by
  obtain ⟨f₀, hf₀, hmin, heq⟩ := peelIn_spec C ⟨f, hf⟩
  rw [heq]
  exact (eq_of_subset_of_card_le (hall f₀ hf₀) (hmin f hf)).symm

/-- The selection of the in-leg peel: attached, connected and tadpole-free `(1,1)`
contractions. -/
abbrev peelSelG : CountSel 1 1 := fun C _ =>
  ExternalsAttached C ∧ VerticesConnected C ∧ PeelTadFree C

/-- In-leg reducible: the contraction has an in-leg self-energy cut. -/
abbrev peelRedIn : CountSel 1 1 := fun C _ => ∃ f, PeelInCut C f

end QED.GradedProof.X1C

end
