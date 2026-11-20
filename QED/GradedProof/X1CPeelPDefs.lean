/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CPeelOutDefs

/-!
# (X₁) piece C: photon-leg cuts

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (the graph theory of the photon-leg peel). For a contraction `C`
with one open fermion line:

* `PeelPFermAt C T`: a fermion external (the out-vertex or the in-vertex) is attached to a vertex
  of `T`; `PeelExtAt C T` is `PeelPFermAt C T` or a photon external at `T` (`peelP_extAt_iff`).
* `PeelPCut C g w`: **a photon-leg cut**: the photon line `g` is a bridge, `w` is one of its ends
  and the side of `w` (`tadComp C g w`) carries no fermion external. In a tadpole-free contraction
  this side carries the photon external; it is the vacuum polarization peeled off the photon leg.
* `peelRedP`: photon-leg reducible (a photon-leg cut exists). Out-leg reducibility is the out-leg
  peel's `peelRedOut`.
* `peelPSide C`: the vertices on the cut side of every photon-leg cut (the peeled set recovered
  by the injectivity of the glue); `peelP_exists_minCut`: a photon-leg cut with fewest vertices on
  its cut side.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line FermionLine PhotonLine Joined IsBridge)
open Relation Finset

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- A fermion external of `C` (the out-vertex or the in-vertex) is attached to a vertex of `T`. -/
def PeelPFermAt (C : Contraction 1 nA κ) (T : Fin N → Prop) : Prop :=
  (∃ s, C.1.1 (.inl 0) = .inr s ∧ T s.1) ∨ (∃ s, C.1.1 (.inr s) = .inl 0 ∧ T s.1)

theorem peelP_extAt_iff (C : Contraction 1 nA κ) (T : Fin N → Prop) :
    PeelExtAt C T ↔ PeelPFermAt C T ∨ ∃ j a, C.1.2 (.inl j) = .inr a ∧ T a.1 := by
  unfold PeelExtAt PeelPFermAt
  exact or_assoc.symm

/-- **A photon-leg cut**: a photon bridge `g` whose side of the end `w` carries no fermion
external. -/
def PeelPCut (C : Contraction 1 nA κ) (g : PhotonLine C) (w : Fin N) : Prop :=
  IsBridge (.inr g : Line C) ∧ (w = g.1.1 ∨ w = g.head.1) ∧ ¬ PeelPFermAt C (tadComp C g w)

/-- Photon-leg reducible: the contraction has a photon-leg cut. -/
abbrev peelRedP : CountSel 1 1 := fun C _ => ∃ g w, PeelPCut C g w

open scoped Classical in
/-- The vertices on the cut side of every photon-leg cut. -/
noncomputable def peelPSide (C : Contraction 1 nA κ) : Finset (Fin N) :=
  univ.filter fun v => ∀ g w, PeelPCut C g w → tadComp C g w v

theorem mem_peelPSide {C : Contraction 1 nA κ} {v : Fin N} :
    v ∈ peelPSide C ↔ ∀ g w, PeelPCut C g w → tadComp C g w v := by
  classical
  simp [peelPSide]

open scoped Classical in
/-- A photon-leg cut with fewest vertices on its cut side exists when a cut does. -/
theorem peelP_exists_minCut (C : Contraction 1 nA κ) (h : ∃ g w, PeelPCut C g w) :
    ∃ g w, PeelPCut C g w ∧ ∀ g' w', PeelPCut C g' w' →
      (peelSide C (.inr g) w).card ≤ (peelSide C (.inr g') w').card := by
  obtain ⟨g₀, w₀, h₀⟩ := h
  obtain ⟨x, hx, hmin⟩ := (univ.filter fun x : PhotonLine C × Fin N => PeelPCut C x.1 x.2)
    |>.exists_min_image (fun x => (peelSide C (.inr x.1) x.2).card) ⟨(g₀, w₀), by simp [h₀]⟩
  exact ⟨x.1, x.2, (mem_filter.1 hx).2, fun g' w' h' => hmin (g', w') (by simp [h'])⟩

end QED.GradedProof.X1C

end
