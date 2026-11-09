/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.WickVertex
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Graph lemmas for the classification of Wick contractions

General facts about the frozen Wick contractions of packet 5 (decision D-20), used to classify
the one-particle-irreducible contractions entering `QED.Wick.wickVertex`.

* `isEmpty_contraction_of_not_two_dvd`: an odd number of photon fields (counting the external
  `A(z)`) admits no contraction, since a fixed-point-free involution needs an even carrier.
* `Line.Crosses f v`: the internal line `f` is not a self-loop and ends at the vertex `v`.
* `IsOnePI.exists_crosses_ne`: in a 1PI contraction with at least two vertices, every vertex is
  an end of two distinct internal lines that are not self-loops (a bridgeless graph has no
  single-edge cut around a vertex).
* `reflTransGen_of_forall_eq_or`: a symmetric relation in which one point is related to every
  other point connects all points.
-/

@[expose] public section

namespace QED.Wick

variable {N : ℕ} {κ : Fin N → VertexKind}

/-- The ends of an internal fermion line: it runs from the vertex of the `Ψ̄` contracted with its
`Ψ` to the vertex of that `Ψ`. -/
theorem Line.ends_inl {C : Contraction κ} (f : FermionLine C) {s : FermionVertex κ}
    (h : C.1.1 (some f.1) = some s) : Line.ends (Sum.inl f : Line C) = (s.1, f.1.1) := by
  simp [Line.ends, h]

/-- The ends of an internal photon line: it runs from its indexing field to the field contracted
with it. -/
theorem Line.ends_inr {C : Contraction κ} (g : PhotonLine C) {y : PhotonSlot κ}
    (h : C.1.2 (some g.1) = some y) : Line.ends (Sum.inr g : Line C) = (g.1.1, y.1) := by
  simp [Line.ends, h]

/-- The internal line `f` is not a self-loop and has an end at the vertex `v`, so it crosses the
cut between `{v}` and the other vertices. -/
def Line.Crosses {C : Contraction κ} (f : Line C) (v : Fin N) : Prop :=
  f.ends.1 ≠ f.ends.2 ∧ (f.ends.1 = v ∨ f.ends.2 = v)

/-- A crossing condition for an internal fermion line in terms of its ends. -/
theorem Line.crosses_inl_iff {C : Contraction κ} (f : FermionLine C) {s : FermionVertex κ}
    (h : C.1.1 (some f.1) = some s) (v : Fin N) :
    Line.Crosses (Sum.inl f : Line C) v ↔ s.1 ≠ f.1.1 ∧ (s.1 = v ∨ f.1.1 = v) := by
  simp only [Line.Crosses, Line.ends_inl f h]

/-- A crossing condition for an internal photon line in terms of its ends. -/
theorem Line.crosses_inr_iff {C : Contraction κ} (g : PhotonLine C) {y : PhotonSlot κ}
    (h : C.1.2 (some g.1) = some y) (v : Fin N) :
    Line.Crosses (Sum.inr g : Line C) v ↔ g.1.1 ≠ y.1 ∧ (g.1.1 = v ∨ y.1 = v) := by
  simp only [Line.Crosses, Line.ends_inr g h]

/-- `Joined` is symmetric. -/
theorem Joined.symm {C : Contraction κ} {S : Set (Line C)} {u w : Fin N}
    (h : Joined C S u w) : Joined C S w u := by
  obtain ⟨f, hf, h⟩ := h
  exact ⟨f, hf, h.symm⟩

/-- A set closed under the steps of `r` is closed under `Relation.ReflTransGen r`. -/
theorem reflTransGen_mem_of_closed {α : Type*} {r : α → α → Prop} {A : Set α}
    (hA : ∀ x y, r x y → x ∈ A → y ∈ A) {u w : α} (h : Relation.ReflTransGen r u w)
    (hu : u ∈ A) : w ∈ A := by
  induction h with
  | refl => exact hu
  | tail _ hxy ih => exact hA _ _ hxy ih

/-- If the vertex `v` is connected to a different vertex by the internal lines outside `S`, then
some line outside `S` crosses the cut around `v`. -/
theorem exists_crosses_of_reflTransGen {C : Contraction κ} {S : Set (Line C)} {v w : Fin N}
    (hvw : v ≠ w) (h : Relation.ReflTransGen (Joined C S) v w) : ∃ f ∉ S, f.Crosses v := by
  by_contra hne
  push Not at hne
  refine hvw (reflTransGen_mem_of_closed (A := {v}) ?_ h rfl).symm
  rintro x y ⟨f, hfS, hf⟩ rfl
  by_contra hy
  apply hne f hfS
  rcases hf with hf | hf <;> simp only [Line.Crosses, hf] <;> exact ⟨by simpa [eq_comm] using hy,
    by simp⟩

/-- In a 1PI contraction, a vertex `v` (in a graph with another vertex `w`) is an end of two
distinct internal lines that are not self-loops. -/
theorem IsOnePI.exists_crosses_ne {C : Contraction κ} (hC : IsOnePI C) {v w : Fin N}
    (hvw : v ≠ w) : ∃ f₁ f₂ : Line C, f₁ ≠ f₂ ∧ f₁.Crosses v ∧ f₂.Crosses v := by
  obtain ⟨f₁, -, h₁⟩ := exists_crosses_of_reflTransGen hvw (hC.2 none v w)
  obtain ⟨f₂, h₂S, h₂⟩ := exists_crosses_of_reflTransGen hvw (hC.2 (some f₁) v w)
  exact ⟨f₁, f₂, fun h => h₂S (by simp [h]), h₁, h₂⟩

/-- A symmetric relation in which the point `h` is related to every other point connects any two
points. -/
theorem reflTransGen_of_forall_eq_or {α : Type*} {r : α → α → Prop}
    (hr : ∀ x y, r x y → r y x) (h : α) (hs : ∀ u, u = h ∨ r h u) (u w : α) :
    Relation.ReflTransGen r u w := by
  have hto : ∀ u, Relation.ReflTransGen r h u := fun u => by
    rcases hs u with rfl | hu
    · exact .refl
    · exact .single hu
  have hfrom : ∀ u, Relation.ReflTransGen r u h := fun u => by
    rcases hs u with rfl | hu
    · exact .refl
    · exact .single (hr _ _ hu)
  exact (hfrom u).trans (hto w)

/-- There is no contraction when the number of photon fields, counting the external `A(z)`, is
odd: a fixed-point-free involution needs a carrier of even cardinality. -/
theorem isEmpty_contraction_of_not_two_dvd
    (h : ¬ 2 ∣ Fintype.card (Option (PhotonSlot κ))) : IsEmpty (Contraction κ) := by
  refine ⟨fun C => ?_⟩
  have hsq : C.1.2 ^ 2 ^ 1 = 1 := Equiv.ext fun a => by simp [pow_two, (C.2 a).1]
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime h hsq
  exact (C.2 a).2 ha

/-- Two internal photon lines through a common photon field are equal. -/
theorem PhotonLine.eq_of_mem {C : Contraction κ} {g₁ g₂ : PhotonLine C} {z : PhotonSlot κ}
    (h₁ : g₁.1 = z ∨ C.1.2 (some g₁.1) = some z)
    (h₂ : g₂.1 = z ∨ C.1.2 (some g₂.1) = some z) : g₁ = g₂ := by
  obtain ⟨x₁, y₁, hy₁, hk₁⟩ := g₁
  obtain ⟨x₂, y₂, hy₂, hk₂⟩ := g₂
  simp only at h₁ h₂ ⊢
  have hinv : ∀ a, C.1.2 (C.1.2 a) = a := fun a => (C.2 a).1
  rcases h₁ with rfl | h₁ <;> rcases h₂ with h₂ | h₂
  · subst h₂; rfl
  · have hy : y₂ = x₁ := Option.some_injective _ (hy₂.symm.trans h₂)
    have h' : C.1.2 (some x₁) = some x₂ := by rw [← h₂, hinv]
    have hy' : y₁ = x₂ := Option.some_injective _ (hy₁.symm.trans h')
    subst hy hy'
    omega
  · subst h₂
    have hy : y₁ = x₂ := Option.some_injective _ (hy₁.symm.trans h₁)
    have h' : C.1.2 (some x₂) = some x₁ := by rw [← h₁, hinv]
    have hy' : y₂ = x₁ := Option.some_injective _ (hy₂.symm.trans h')
    subst hy hy'
    omega
  · have : x₁ = x₂ := Option.some_injective _ (C.1.2.injective (h₁.trans h₂.symm))
    subst this
    rfl

end QED.Wick

end
