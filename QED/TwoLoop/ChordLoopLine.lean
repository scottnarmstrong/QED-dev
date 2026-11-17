/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.LoopCount
public import QED.Frozen.WickModel.IsLoopLine

/-!
# Chords and the loop line

Graph facts relating the chords (T₁) of packet T1 (decision D-38) to the bridges (X₁₅) and the
loop line (X₂₁) of packet 6a. No connectedness is assumed.

* `QED.TwoLoop.Chord.label_injective`: distinct internal lines have distinct labels.
* `QED.TwoLoop.not_isBridge_of_isChord`: a chord is not a bridge.
* `QED.TwoLoop.isChord_of_isLoopLine`: the lowest-labelled line that is not a bridge is a chord.
  Every line of lower label is a bridge, and deleting a bridge other than the loop line keeps the
  ends of the loop line connected.
* `QED.TwoLoop.isChord_iff_isLoopLine`: with at most one chord, the chords are the loop lines.
* `QED.TwoLoop.card_chordsBelow_lt`: a chord has fewer than `loopCount C` chords below it.
-/

public section

namespace QED.TwoLoop

open QED.WickModel

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}

/-! The elementary graph lemmas live in the namespace `QED.TwoLoop.Chord`, so that opening
`QED.TwoLoop` next to `QED.WickModel` creates no ambiguous names. -/

namespace Chord

/-- A vertex has at most two photon fields. -/
theorem photonSlots_le_two (k : Wick.VertexKind) : k.photonSlots ≤ 2 := by
  cases k <;> decide

/-- The photon key is injective. -/
theorem photonKey_injective : Function.Injective (Wick.photonKey (κ := κ)) := by
  rintro ⟨t, i⟩ ⟨s, j⟩ h
  have hi := photonSlots_le_two (κ t)
  have hj := photonSlots_le_two (κ s)
  have hi' := i.2
  have hj' := j.2
  simp only [Wick.photonKey] at h
  have hts : t = s := Fin.ext (by omega)
  subst hts
  have hij : i = j := Fin.ext (by omega)
  subst hij
  rfl

/-- Distinct internal lines have distinct labels. -/
theorem label_injective : Function.Injective (Line.label (C := C)) := by
  rintro (f | g) (f' | g') h <;> simp only [Line.label] at h
  · exact congrArg Sum.inl (Subtype.ext (Subtype.ext (Fin.ext h)))
  · have := f.1.1.2
    omega
  · have := f'.1.1.2
    omega
  · exact congrArg Sum.inr (Subtype.ext (photonKey_injective (by omega)))

/-- `Joined` is symmetric. -/
theorem joined_symm {S : Set (Line C)} {u w : Fin N} (h : Joined C S u w) : Joined C S w u := by
  obtain ⟨f, hf, h⟩ := h
  exact ⟨f, hf, h.symm⟩

/-- Connection by the lines outside `S` is symmetric. -/
theorem reflTransGen_joined_symm {S : Set (Line C)} {u w : Fin N}
    (h : Relation.ReflTransGen (Joined C S) u w) : Relation.ReflTransGen (Joined C S) w u := by
  induction h with
  | refl => exact .refl
  | tail _ hcd ih => exact Relation.ReflTransGen.head (joined_symm hcd) ih

/-- Excluding more lines removes connections. -/
theorem reflTransGen_joined_mono {S T : Set (Line C)} (hST : S ⊆ T) {u w : Fin N}
    (h : Relation.ReflTransGen (Joined C T) u w) : Relation.ReflTransGen (Joined C S) u w := by
  induction h with
  | refl => exact .refl
  | tail _ hcd ih =>
    obtain ⟨f, hf, he⟩ := hcd
    exact ih.tail ⟨f, fun hfS => hf (hST hfS), he⟩

/-- Excluding one more line `g` with ends `(x, y)`: a connection from `u` to `w` either survives,
or passes through `g`, in one direction or the other. -/
theorem reflTransGen_joined_insert {S : Set (Line C)} {g : Line C} {x y : Fin N}
    (hg : g.ends = (x, y)) {u w : Fin N} (h : Relation.ReflTransGen (Joined C S) u w) :
    Relation.ReflTransGen (Joined C (insert g S)) u w ∨
      (Relation.ReflTransGen (Joined C (insert g S)) u x ∧
        Relation.ReflTransGen (Joined C (insert g S)) y w) ∨
      (Relation.ReflTransGen (Joined C (insert g S)) u y ∧
        Relation.ReflTransGen (Joined C (insert g S)) x w) := by
  induction h with
  | refl => exact Or.inl .refl
  | @tail c d _ hcd ih =>
    obtain ⟨h, hhS, hends⟩ := hcd
    by_cases hhg : h = g
    · subst hhg
      rcases hends with hends | hends <;> rw [hg, Prod.mk.injEq] at hends <;>
        obtain ⟨rfl, rfl⟩ := hends
      · rcases ih with ih | ih | ih
        · exact Or.inr (Or.inl ⟨ih, .refl⟩)
        · exact Or.inr (Or.inl ⟨ih.1, .refl⟩)
        · exact Or.inl ih.1
      · rcases ih with ih | ih | ih
        · exact Or.inr (Or.inr ⟨ih, .refl⟩)
        · exact Or.inl ih.1
        · exact Or.inr (Or.inr ⟨ih.1, .refl⟩)
    · have e : Joined C (insert g S) c d := ⟨h, by simp [hhg, hhS], hends⟩
      rcases ih with ih | ih | ih
      · exact Or.inl (ih.tail e)
      · exact Or.inr (Or.inl ⟨ih.1, ih.2.tail e⟩)
      · exact Or.inr (Or.inr ⟨ih.1, ih.2.tail e⟩)

end Chord

open Chord

/-- **A chord is not a bridge.** -/
theorem not_isBridge_of_isChord {f : Line C} (hf : IsChord f) : ¬ IsBridge f := by
  intro hb
  apply hb
  refine reflTransGen_joined_mono ?_ hf
  intro g hg
  rw [Set.mem_singleton_iff.mp hg]
  exact le_refl f.label

/-- **The loop line is a chord.** Every line of lower label is a bridge; deleting such a bridge
`g` keeps the ends of the loop line `f` connected, since otherwise every connection of the ends
of `f` avoiding `f` passes through `g`, and `f` would connect the ends of `g` around `g`. -/
theorem isChord_of_isLoopLine {f : Line C} (hf : IsLoopLine f) : IsChord f := by
  classical
  have key : ∀ T : Finset (Line C), (∀ g ∈ T, g.label < f.label) →
      Relation.ReflTransGen (Joined C (insert f (T : Set (Line C)))) f.ends.1 f.ends.2 := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      simpa [IsBridge] using hf.1
    | @insert g T _ ih =>
      intro hT
      have hgf : g.label < f.label := hT g (Finset.mem_insert_self g T)
      have ih := ih fun g' hg' => hT g' (Finset.mem_insert_of_mem hg')
      have hne : f ≠ g := fun h => (lt_irrefl _ (h ▸ hgf))
      have hset : insert f ((insert g T : Finset (Line C)) : Set (Line C)) =
          insert g (insert f (T : Set (Line C))) := by
        rw [Finset.coe_insert, Set.insert_comm]
      rw [hset]
      rcases reflTransGen_joined_insert (g := g) (Prod.mk.eta (p := g.ends)).symm ih with
        h | h | h
      · exact h
      all_goals
        exfalso
        have hbr : IsBridge g := by
          by_contra hnb
          exact absurd (hf.2 g hnb) (not_le.mpr hgf)
        apply hbr
        have hsub : ({g} : Set (Line C)) ⊆ insert g (insert f (T : Set (Line C))) := by
          simp
        have ef : Joined C {g} f.ends.1 f.ends.2 := ⟨f, by simpa using hne, Or.inl rfl⟩
      · have h1 := reflTransGen_joined_symm (reflTransGen_joined_mono hsub h.1)
        exact (h1.tail ef).trans (reflTransGen_joined_symm (reflTransGen_joined_mono hsub h.2))
      · have h1 := reflTransGen_joined_mono hsub h.2
        exact (h1.tail (joined_symm ef)).trans (reflTransGen_joined_mono hsub h.1)
  have hT := key (Finset.univ.filter fun g : Line C => g.label < f.label) (by simp)
  refine reflTransGen_joined_mono ?_ hT
  intro g hg
  simp only [Set.mem_ofPred_eq] at hg
  rcases hg.lt_or_eq with hlt | heq
  · exact Set.mem_insert_of_mem _ (by simpa using hlt)
  · exact Set.mem_insert_iff.mpr (Or.inl (label_injective heq))

/-- **With at most one chord, the chords are the loop lines.** -/
theorem isChord_iff_isLoopLine (hC : loopCount C ≤ 1) (f : Line C) :
    IsChord f ↔ IsLoopLine f := by
  classical
  refine ⟨fun hf => ⟨not_isBridge_of_isChord hf, fun g hg => ?_⟩, isChord_of_isLoopLine⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun g : Line C => ¬ IsBridge g) Line.label ⟨g, by simp [hg]⟩
  have hml : IsLoopLine m :=
    ⟨by simpa using hm, fun g' hg' => hmin g' (by simp [hg'])⟩
  have hmc := isChord_of_isLoopLine hml
  have hmf : m ≠ f := by
    rintro rfl
    exact absurd (hmin g (by simp [hg])) (not_le.mpr hlt)
  have h2 : ({m, f} : Finset (Line C)) ⊆ Finset.univ.filter fun g : Line C => IsChord g := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simpa
  have := Finset.card_le_card h2
  rw [Finset.card_pair hmf] at this
  unfold loopCount at hC
  omega

open scoped Classical in
/-- A chord has fewer than `loopCount C` chords of lower label. -/
theorem card_chordsBelow_lt {f : Line C} (hf : IsChord f) :
    (Finset.univ.filter fun g : Line C => IsChord g ∧ g.label < f.label).card < loopCount C := by
  unfold loopCount
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset (fun g hg => ?_) |>.mpr ⟨f, by simpa using hf, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    exact hg.1
  · simp

end QED.TwoLoop

end
