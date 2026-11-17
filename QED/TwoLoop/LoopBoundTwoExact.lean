/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.LoopBoundTwo
public import QED.TwoLoop.Routing

/-!
# The number of loops

For a contraction with at least one vertex, attached externals (X₁₆) and connected vertices
(X₁₇), the number of loops (T₂) is given exactly by
`2 · loopCount C + 2 nf + nA = V₃ + 2`, with `V₃` the number of `gauge` and `gaugeCt` vertices
(obligation O2-5 (iii); the formula of the docstring of (T₂)).

* `QED.TwoLoop.LoopBoundTwo.loopCount_add_eq`: the cyclomatic number,
  `loopCount C + V = E + 1`. The non-chords connect the vertices, so there are at least `V - 1` of
  them (`QED.TwoLoop.LoopBound.card_le_card_nonChord_add_one`), and they form a forest, so there
  are at most `V - 1` (`QED.TwoLoop.Routing.card_nonChord_add_one_le`).
* `QED.TwoLoop.LoopBoundTwo.card_fermionLine_add_eq`,
  `QED.TwoLoop.LoopBoundTwo.two_mul_card_photonLine_add_eq`: with attached externals, every
  vertex field is used by exactly one internal line or external field, so the field counts of
  `QED.TwoLoop.LoopBound` are equalities.
* `QED.TwoLoop.LoopBoundTwo.two_mul_loopCount_add_eq`: the formula.
-/

@[expose] public section

namespace QED.TwoLoop.LoopBoundTwo

open QED.WickModel QED.TwoLoop.LoopBound

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- **The cyclomatic number**: a contraction with at least one vertex and connected vertices (X₁₇)
has `loopCount C + V = E + 1`. -/
theorem loopCount_add_eq {C : Contraction nf nA κ} (hV : VerticesConnected C) (hN : 0 < N) :
    loopCount C + N = Nat.card (Line C) + 1 := by
  have h1 := card_le_card_nonChord_add_one hV
  have h2 := Routing.card_nonChord_add_one_le C hN
  have h3 := loopCount_add_card_nonChord C
  omega

/-- With attached externals (X₁₆), the `Ψ` of every `Ψ̄Ψ` vertex is used by exactly one internal
fermion line or external `Ψ̄`. -/
theorem card_fermionLine_add_eq {C : Contraction nf nA κ} (hA : ExternalsAttached C) :
    Nat.card (FermionLine C) + nf = Nat.card (Wick.FermionVertex κ) := by
  refine le_antisymm (card_fermionLine_add_le hA) ?_
  let F : FermionLine C ⊕ Fin nf → Wick.FermionVertex κ
    | .inl f => f.1
    | .inr i => fermionExt hA i
  have hF : Function.Surjective F := by
    intro t
    rcases h : C.1.1 (.inr t) with i | s
    · exact ⟨.inr i,
        Sum.inr_injective (C.1.1.injective ((apply_inr_fermionExt hA i).trans h.symm))⟩
    · exact ⟨.inl ⟨t, by rw [h]; rfl⟩, rfl⟩
  have := Nat.card_le_card_of_surjective F hF
  rwa [Nat.card_sum, Nat.card_fin] at this

/-- With attached externals (X₁₆), every vertex photon field is used by exactly one internal
photon line (as its indexing field or its head) or external `A`. -/
theorem two_mul_card_photonLine_add_eq {C : Contraction nf nA κ} (hA : ExternalsAttached C) :
    2 * Nat.card (PhotonLine C) + nA = Nat.card (Wick.PhotonSlot κ) := by
  refine le_antisymm (two_mul_card_photonLine_add_le hA) ?_
  let F : PhotonLine C ⊕ PhotonLine C ⊕ Fin nA → Wick.PhotonSlot κ
    | .inl g => g.1
    | .inr (.inl g) => g.head
    | .inr (.inr j) => photonExt hA j
  have hF : Function.Surjective F := by
    intro a
    rcases h : C.1.2 (.inr a) with j | b
    · exact ⟨.inr (.inr j),
        Sum.inr_injective (C.1.2.injective ((apply_inr_photonExt hA j).trans h.symm))⟩
    · have hab : a ≠ b := fun hab => (C.2 (.inr a)).2 (by rw [h, hab])
      have hk : Wick.photonKey a ≠ Wick.photonKey b := fun hk =>
        hab (Chord.photonKey_injective hk)
      rcases lt_or_gt_of_ne hk with hk | hk
      · exact ⟨.inl ⟨a, b, h, hk⟩, rfl⟩
      · have hb : C.1.2 (.inr b) = .inr a := by rw [← h, (C.2 _).1]
        exact ⟨.inr (.inl ⟨b, a, hb, hk⟩),
          Sum.inr_injective ((apply_inr_photonLine (C := C) ⟨b, a, hb, hk⟩).symm.trans hb)⟩
  have := Nat.card_le_card_of_surjective F hF
  rw [Nat.card_sum, Nat.card_sum, Nat.card_fin] at this
  omega

/-- Twice the `Ψ̄Ψ` vertices plus the photon fields are twice the vertices plus the number of
`gauge` and `gaugeCt` vertices. -/
theorem two_mul_card_fermionVertex_add_card_photonSlot (κ : Fin N → Wick.VertexKind) :
    2 * Nat.card (Wick.FermionVertex κ) + Nat.card (Wick.PhotonSlot κ) =
      2 * N + (Finset.univ.filter fun t => κ t = .gauge ∨ κ t = .gaugeCt).card := by
  have h : ∑ t, (2 * (if κ t ≠ .photonCt then 1 else 0) + (κ t).photonSlots) =
      ∑ t, (2 + if κ t = .gauge ∨ κ t = .gaugeCt then 1 else 0) :=
    Finset.sum_congr rfl fun t _ => by cases κ t <;> simp [Wick.VertexKind.photonSlots]
  rw [card_fermionVertex, card_photonSlot, Finset.mul_sum, ← Finset.sum_add_distrib, h,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_comm, Finset.card_filter]

/-- **The number of loops** (O2-5 (iii)): a contraction with at least one vertex, attached
externals (X₁₆) and connected vertices (X₁₇) has `2 · loopCount C + 2 nf + nA = V₃ + 2`, with
`V₃` the number of `gauge` and `gaugeCt` vertices. -/
theorem two_mul_loopCount_add_eq {C : Contraction nf nA κ} (hA : ExternalsAttached C)
    (hV : VerticesConnected C) (hN : 0 < N) :
    2 * loopCount C + 2 * nf + nA =
      (Finset.univ.filter fun t => κ t = .gauge ∨ κ t = .gaugeCt).card + 2 := by
  have h1 := card_fermionLine_add_eq hA
  have h2 := two_mul_card_photonLine_add_eq hA
  have h3 := two_mul_card_fermionVertex_add_card_photonSlot κ
  have h4 := loopCount_add_eq hV hN
  have h5 : Nat.card (Line C) = Nat.card (FermionLine C) + Nat.card (PhotonLine C) :=
    Nat.card_sum
  omega

end QED.TwoLoop.LoopBoundTwo

end
