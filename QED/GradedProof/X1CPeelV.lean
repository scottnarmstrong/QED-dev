/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CPeelPDefs
public import QED.GradedProof.X1CCountConn
public import QED.GradedProof.X1CGlueP

/-!
# (X₁) piece C: a fully peeled contraction is 1PI

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5. An attached connected tadpole-free `(1,1)` contraction with no
in-leg cut, no out-leg cut and no photon-leg cut has no bridge, and conversely
(**`peelV_iff_isOnePI`**):

* a fermion bridge has the in-vertex on its tail side and the out-vertex on its head side
  (`peel_tail_reach_in`, `peel_head_reach_out`); the photon external lies on one of the two
  sides, so the bridge is an out-leg cut (photon on the tail side) or an in-leg cut;
* the two fermion externals are joined along the open fermion line without any photon line
  (`peel_reach_out_in`), so for a photon bridge they lie on the same side, and the other side is a
  photon-leg cut.

**`peelV_hV`**: the hypothesis `hV` of `countDyson_dysonFive_t9` for `SelG := peelSelG`,
`RedIn := peelRedIn`, `RedOut := peelRedOut`, `RedP := peelRedP`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line FermionLine PhotonLine Joined IsBridge VerticesConnected
  ExternalsAttached IsOnePI)
open QED.Graded
open Relation

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- In a contraction with no in-leg and no out-leg cut, no fermion line is a bridge. -/
theorem peelV_not_bridge_fermion {C : Contraction 1 1 κ} (hV : VerticesConnected C)
    (hI : ¬ ∃ f, PeelInCut C f) (hO : ¬ ∃ f, PeelOutCut C f) (f : FermionLine C) :
    ¬ IsBridge (.inl f : Line C) := by
  intro hl
  rcases peel_reach_sides hV (.inl f) (extSlot C).1 with h | h
  · refine hO ⟨f, hl, fun j a hj hr => ?_⟩
    rw [Subsingleton.elim j 0, extSlot_spec] at hj
    cases Sum.inr_injective hj
    exact peel_sides_disjoint hl h hr
  · refine hI ⟨f, hl, fun j a hj hr => ?_⟩
    rw [Subsingleton.elim j 0, extSlot_spec] at hj
    cases Sum.inr_injective hj
    exact peel_sides_disjoint hl hr h

/-- In an attached contraction with no photon-leg cut, no photon line is a bridge. -/
theorem peelV_not_bridge_photon {C : Contraction 1 1 κ} (hA : ExternalsAttached C)
    (hV : VerticesConnected C) (hP : ¬ ∃ g w, PeelPCut C g w) (g : PhotonLine C) :
    ¬ IsBridge (.inr g : Line C) := by
  intro hl
  obtain ⟨x, hx⟩ := count_exists_out hA
  obtain ⟨y, hy⟩ := count_exists_in hA
  have hxy : ReflTransGen (Joined C {.inr g}) x.1 y.1 :=
    peel_reach_out_in hx hy fun f hf => Sum.inl_ne_inr (Set.mem_singleton_iff.1 hf)
  have key : ∀ w', ¬ ReflTransGen (Joined C {.inr g}) w' x.1 →
      ¬ PeelPFermAt C (tadComp C g w') := by
    rintro w' hne (⟨s, hs, hr⟩ | ⟨s, hs, hr⟩)
    · cases Sum.inr_injective (hx.symm.trans hs)
      exact hne hr
    · cases Sum.inr_injective (C.1.1.injective (hy.trans hs.symm))
      exact hne (hr.trans (peel_reach_symm hxy))
  rcases peel_reach_sides hV (.inr g) x.1 with h | h
  · exact hP ⟨g, g.head.1, hl, .inr rfl, key _ fun h' => peel_sides_disjoint hl h h'⟩
  · exact hP ⟨g, g.1.1, hl, .inl rfl, key _ fun h' => peel_sides_disjoint hl h' h⟩

/-- **A fully peeled contraction is 1PI, and conversely.** -/
theorem peelV_iff_isOnePI (C : Contraction 1 1 κ) (g : Grading κ) :
    (((peelSelG C g ∧ ¬ peelRedIn C g) ∧ ¬ peelRedOut C g) ∧ ¬ peelRedP C g) ↔ IsOnePI C := by
  constructor
  · rintro ⟨⟨⟨⟨hA, hV, -⟩, hI⟩, hO⟩, hP⟩
    refine ⟨hA, hV, ?_⟩
    rintro (f | p)
    · exact peelV_not_bridge_fermion hV hI hO f
    · exact peelV_not_bridge_photon hA hV hP p
  · intro h
    exact ⟨⟨⟨⟨h.1, h.2.1, fun p hp => absurd hp (h.2.2 _)⟩, fun ⟨f, hf⟩ => h.2.2 _ hf.1⟩,
      fun ⟨f, hf⟩ => h.2.2 _ hf.1⟩, fun ⟨p, _, hp⟩ => h.2.2 _ hp.1⟩

/-- **`hV` of `countDyson_dysonFive_t9`** for `peelSelG`, `peelRedIn`, `peelRedOut`,
`peelRedP`. -/
theorem peelV_hV {M : ℕ} {κ' : Fin M → Wick.VertexKind} (C : Contraction 1 1 κ')
    (g : Grading κ') (_ : gradedOrder κ' g ≤ 5) :
    (((peelSelG C g ∧ ¬ peelRedIn C g) ∧ ¬ peelRedOut C g) ∧ ¬ peelRedP C g) ↔ IsOnePI C :=
  peelV_iff_isOnePI C g

end QED.GradedProof.X1C

end
