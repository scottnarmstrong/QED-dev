/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.EnumerationDecide
public import QED.Frozen.TwoLoop.LineMomentum

/-!
# (X₀): the loop coefficients of the routing, computably

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), step X0d.1. The
routing (T₄) `lineMomentum₂` is integer affine in the loop momenta
(`QED.TwoLoop.Relabel.IsIntAffine.lineMomentum₂` gives this existentially). Here the integer
coefficients are computed from the line data (labels and ends, `lineData`) alone, by Boolean
tests suitable for kernel evaluation, and the affine formula is proved for every contraction and
every number `L` of loop momenta.

* `edgeChord E x`: the chord test (T₁) on an edge `x` of the edge data `E`.
* `edgeRank E l`: the number of chord edges of label `< l` (the index of the loop momentum a
  chord carries, (T₃)).
* `edgeSide E x`: the side (T₄) of the tail of a non-chord edge `x`: the vertices reached from
  its tail avoiding `x` and the chords.
* `edgeCoeff E x s`: the coefficient of `ℓ s` in the momentum of `x`: for a chord `1` if its
  rank is `s`; otherwise the number of rank-`s` chords whose head lies on the side minus the
  number whose tail does.
* `loopCoeff C f s = edgeCoeff (lineData C) (f.label, f.ends) s` and `extPart C pOut pIn kIn f`
  (the total external momentum injected into the side, `0` on a chord).
* `lineMomentum₂_eq_loopCoeff`: `lineMomentum₂ C pOut pIn kIn ℓ f =
  ∑ s, (loopCoeff C f s : ℝ) • ℓ s + extPart C pOut pIn kIn f`.
-/

@[expose] public section

namespace QED.GradedProof.X0

open QED.WickModel Relation
open QED.TwoLoop.Enumeration (reachE mAny mAny_eq_true lineData mem_lineData isChord_iff
  reflTransGen_joined_iff)

/-! ### The Boolean data on edges -/

section Edges

variable {N : ℕ}

/-- The chord test (T₁) on an edge: its head is reached from its tail along edges of larger
label. -/
def edgeChord (E : Multiset (ℕ × Fin N × Fin N)) (x : ℕ × Fin N × Fin N) : Bool :=
  decide (x.2.2 ∈ reachE E (fun l => decide (x.1 < l)) x.2.1 N)

/-- Some chord edge has label `l`. -/
def chordLabel (E : Multiset (ℕ × Fin N × Fin N)) (l : ℕ) : Bool :=
  mAny E fun x => decide (x.1 = l) && edgeChord E x

/-- The number of chord edges of label `< l`. -/
def edgeRank (E : Multiset (ℕ × Fin N × Fin N)) (l : ℕ) : ℕ :=
  (E.map fun x => if edgeChord E x && decide (x.1 < l) then 1 else 0).sum

/-- The side of the tail of the edge `x`: the vertices reached from its tail avoiding `x` and the
chord edges. -/
def edgeSide (E : Multiset (ℕ × Fin N × Fin N)) (x : ℕ × Fin N × Fin N) : Finset (Fin N) :=
  reachE E (fun l => l != x.1 && !chordLabel E l) x.2.1 N

/-- The contribution `[head ∈ S] - [tail ∈ S]` of an edge `y` crossing into the vertex set `S`. -/
def crossing (S : Finset (Fin N)) (y : ℕ × Fin N × Fin N) : ℤ :=
  (if y.2.2 ∈ S then 1 else 0) - (if y.2.1 ∈ S then 1 else 0)

/-- The coefficient of `ℓ s` in the momentum of the edge `x`. -/
def edgeCoeff (E : Multiset (ℕ × Fin N × Fin N)) (x : ℕ × Fin N × Fin N) (s : ℕ) : ℤ :=
  if edgeChord E x then (if edgeRank E x.1 = s then 1 else 0) else
    (E.map fun y => if edgeChord E y && decide (edgeRank E y.1 = s) then
      crossing (edgeSide E x) y else 0).sum

end Edges

/-! ### Back to the lines of a contraction -/

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}

/-- The edge of a line: its label and ends. -/
def edgeOf (f : Line C) : ℕ × Fin N × Fin N := (f.label, f.ends)

theorem sum_lineData {M : Type*} [AddCommMonoid M] (F : ℕ × Fin N × Fin N → M) :
    ((lineData C).map F).sum = ∑ g : Line C, F (edgeOf g) := by
  simp only [lineData, Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

theorem isChord_iff_edgeChord (f : Line C) :
    IsChord f ↔ edgeChord (lineData C) (edgeOf f) = true := by
  rw [isChord_iff, edgeChord, decide_eq_true_iff]
  rfl

theorem chordLabel_label_iff (g : Line C) :
    chordLabel (lineData C) g.label = true ↔ IsChord g := by
  rw [chordLabel, mAny_eq_true]
  constructor
  · rintro ⟨x, hx, h⟩
    obtain ⟨g', rfl⟩ := mem_lineData.mp hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have hg : g' = g := QED.TwoLoop.Chord.label_injective h.1
    subst hg
    exact (isChord_iff_edgeChord g').mpr h.2
  · intro h
    exact ⟨edgeOf g, mem_lineData.mpr ⟨g, rfl⟩, by
      simpa [edgeOf] using (isChord_iff_edgeChord g).mp h⟩

open scoped Classical in
/-- The rank is the number of chords of smaller label (as in `chordMomentum`). -/
theorem edgeRank_eq (l : ℕ) :
    edgeRank (lineData C) l = (Finset.univ.filter fun g : Line C => IsChord g ∧ g.label < l).card
    := by
  rw [Finset.card_filter, edgeRank, sum_lineData]
  refine Finset.sum_congr rfl fun g _ => if_congr ?_ rfl rfl
  rw [Bool.and_eq_true, decide_eq_true_iff, ← isChord_iff_edgeChord]
  rfl

open scoped Classical in
theorem mem_edgeSide_iff (f : Line C) (v : Fin N) :
    v ∈ edgeSide (lineData C) (edgeOf f) ↔
      ReflTransGen (Joined C {g | g = f ∨ IsChord g}) f.ends.1 v := by
  rw [edgeSide, reflTransGen_joined_iff C _ _ (fun g => ?_)]
  · rfl
  simp only [Set.mem_ofPred_eq, not_or, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
    edgeOf]
  rw [← Bool.not_eq_true, chordLabel_label_iff]
  exact and_congr_left' ⟨fun h h' => h (QED.TwoLoop.Chord.label_injective h'),
    fun h h' => h (congrArg _ h')⟩

/-- The loop coefficients of the routing (T₄) of `C`. -/
def loopCoeff (C : Contraction nf nA κ) (f : Line C) (s : ℕ) : ℤ :=
  edgeCoeff (lineData C) (edgeOf f) s

/-- The part of the routing (T₄) independent of the loop momenta. -/
noncomputable def extPart (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (f : Line C) : Fin 4 → ℝ :=
  if edgeChord (lineData C) (edgeOf f) then 0 else
    ∑ v ∈ edgeSide (lineData C) (edgeOf f), externalMomentum C pOut pIn kIn v

open scoped Classical in
/-- The chord momentum (T₃) as a combination of the loop momenta. -/
theorem chordMomentum_eq_sum {L : ℕ} (ℓ : Fin L → Fin 4 → ℝ) (g : Line C) :
    chordMomentum ℓ g = ∑ s : Fin L,
      ((if edgeRank (lineData C) g.label = s then 1 else 0 : ℤ) : ℝ) • ℓ s := by
  rw [edgeRank_eq, chordMomentum]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨_, h⟩ (fun b _ hb => ?_) (by simp)]
    · simp
    · split_ifs with h'
      · exact absurd (Fin.ext h'.symm) hb
      · simp
  · refine (Finset.sum_eq_zero fun s _ => ?_).symm
    split_ifs with h'
    · exact absurd (h' ▸ s.2) h
    · simp

/-- The momentum of a non-chord line, summed over the chords: each chord crossing into the side
contributes its momentum with the sign of `crossing`. -/
theorem sum_side_chords {L : ℕ} (ℓ : Fin L → Fin 4 → ℝ) (S : Finset (Fin N))
    (T : Finset (Line C)) :
    ∑ v ∈ S, ∑ g ∈ T, ((if g.ends.2 = v then chordMomentum ℓ g else 0)
      - (if g.ends.1 = v then chordMomentum ℓ g else 0)) =
    ∑ g ∈ T, ((crossing S (edgeOf g) : ℤ) : ℝ) • chordMomentum ℓ g := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq, crossing, edgeOf]
  split_ifs <;> simp

/-- **The routing (T₄) in the loop coefficients**: every line momentum is
`∑ s, loopCoeff C f s • ℓ s + extPart C pOut pIn kIn f`, for every number `L` of loop momenta. -/
theorem lineMomentum₂_eq_loopCoeff {L : ℕ} (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (ℓ : Fin L → Fin 4 → ℝ) (f : Line C) :
    lineMomentum₂ C pOut pIn kIn ℓ f =
      ∑ s : Fin L, ((loopCoeff C f s : ℤ) : ℝ) • ℓ s + extPart C pOut pIn kIn f := by
  classical
  by_cases hf : IsChord f
  · have hf' := (isChord_iff_edgeChord f).mp hf
    rw [lineMomentum₂, ite_eq_left hf, chordMomentum_eq_sum, extPart, ite_eq_left hf', add_zero]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [loopCoeff, edgeCoeff, ite_eq_left hf']
    rfl
  · have hf' : edgeChord (lineData C) (edgeOf f) = false := by
      rw [← Bool.not_eq_true, ← isChord_iff_edgeChord]; exact hf
    have hS : (Finset.univ.filter fun v => ReflTransGen
        (Joined C {g | g = f ∨ IsChord g}) f.ends.1 v) = edgeSide (lineData C) (edgeOf f) :=
      Finset.ext fun v => by simp [mem_edgeSide_iff]
    rw [lineMomentum₂, ite_eq_right hf, hS, Finset.sum_add_distrib, sum_side_chords, extPart,
      ite_eq_right (by simp [hf']), add_comm]
    congr 1
    simp only [loopCoeff, edgeCoeff, hf', Bool.false_eq_true, ite_false, sum_lineData,
      Int.cast_sum, Finset.sum_smul, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : IsChord g
    · have hg' := (isChord_iff_edgeChord g).mp hg
      rw [ite_eq_left hg, chordMomentum_eq_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [edgeOf] at hg' ⊢
      simp only [hg', Bool.true_and]
      split_ifs <;> simp_all
    · have hg' : edgeChord (lineData C) (edgeOf g) = false := by
        rw [← Bool.not_eq_true, ← isChord_iff_edgeChord]; exact hg
      rw [ite_eq_right hg]
      refine (Finset.sum_eq_zero fun s _ => ?_).symm
      simp [hg']

end QED.GradedProof.X0

end
