/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0LoopCoeff
public import QED.Integration.SymanzikIntegrabilityRefinedClasses

/-!
# (X₀): the two-loop power-counting criterion on the line data

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), step X0d.2. The
parametric lines of a contraction are its fermion lines and the two members (masses `mγ`, `Λ`)
of each Pauli–Villars photon pair (`PLine C`). Those on a loop (nonzero row of loop coefficients,
`edgeLoop`) form `LoopLine C`; the others carry constant momenta. Numbered by any equivalence
`ι : LoopLine C ≃ Fin (m + 1)`, their loop matrix is `pMat ι`, read off the loop coefficients
(`QED.GradedProof.X0.loopCoeff`). The numerator-aware criterion of order `2` with the fermion
lines on a loop as numerator lines does not depend on the numbering: it is the Boolean test
`EdgeCrit` on the line data (`lineData C`), in which a photon edge counts twice
(`noSubdivergenceRefined_pMat_of_edgeCrit`).
-/

@[expose] public section

namespace QED.GradedProof.X0

open QED.WickModel
open QED.TwoLoop.Enumeration (lineData mem_lineData)
open QED.Integration.TwoLoop (castLoopMatrix NoSubdivergenceRefined IntNoSubdivergenceRefined
  intPairDet noSubdivergenceRefined_castLoopMatrix_iff)

/-! ### The criterion on edges -/

section Edges

variable {N : ℕ}

/-- The determinant of the two-loop coefficient rows of two edges. -/
def edgeDet (E : Multiset (ℕ × Fin N × Fin N)) (x y : ℕ × Fin N × Fin N) : ℤ :=
  edgeCoeff E x 0 * edgeCoeff E y 1 - edgeCoeff E x 1 * edgeCoeff E y 0

/-- The number of parametric lines of an edge: `1` for a fermion edge (label `< N`), `2` for a
photon edge (its Pauli–Villars pair). -/
def edgeWeight (N : ℕ) (x : ℕ × Fin N × Fin N) : ℕ := if x.1 < N then 1 else 2

/-- The edge `x` lies on a loop: its loop coefficient row is nonzero. -/
def edgeLoop (E : Multiset (ℕ × Fin N × Fin N)) (x : ℕ × Fin N × Fin N) : Bool :=
  edgeCoeff E x 0 != 0 || edgeCoeff E x 1 != 0

/-- **The two-loop criterion on the line data**: for every edge `x` on a loop, four plus the
number of fermion edges not parallel to `x` is less than twice the number of parametric lines
not parallel to `x`. The edges off the loops (zero row) carry constant momenta and are not
parametric lines. -/
def EdgeCrit (E : Multiset (ℕ × Fin N × Fin N)) : Prop :=
  ∀ x ∈ E, edgeLoop E x = true →
    4 + (E.map fun y => if y.1 < N ∧ edgeDet E x y ≠ 0 then 1 else 0).sum <
      2 * (E.map fun y => if edgeDet E x y ≠ 0 then edgeWeight N y else 0).sum

theorem edgeLoop_of_edgeDet_ne_zero {E : Multiset (ℕ × Fin N × Fin N)}
    {x y : ℕ × Fin N × Fin N} (h : edgeDet E x y ≠ 0) : edgeLoop E y = true := by
  by_contra h'
  simp only [edgeLoop, Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at h'
  exact h (by simp [edgeDet, h'.1, h'.2])

theorem edgeLoop_of_edgeDet_ne_zero' {E : Multiset (ℕ × Fin N × Fin N)}
    {x y : ℕ × Fin N × Fin N} (h : edgeDet E x y ≠ 0) : edgeLoop E x = true := by
  by_contra h'
  simp only [edgeLoop, Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at h'
  exact h (by simp [edgeDet, h'.1, h'.2])

instance (E : Multiset (ℕ × Fin N × Fin N)) : Decidable (EdgeCrit E) := by
  unfold EdgeCrit; infer_instance

end Edges

/-! ### The parametric lines -/

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}

/-- The parametric lines: the fermion lines and the two members of each Pauli–Villars photon
pair. -/
abbrev PLine (C : Contraction nf nA κ) : Type := FermionLine C ⊕ (PhotonLine C × Fin 2)

/-- The line of a parametric line. -/
def PLine.line : PLine C → Line C
  | .inl f => .inl f
  | .inr g => .inr g.1

/-- The parametric lines on a loop (nonzero loop coefficient row). -/
abbrev LoopLine (C : Contraction nf nA κ) : Type :=
  {q : PLine C // edgeLoop (lineData C) (edgeOf q.line) = true}

/-- The fermion lines on a loop. -/
abbrev LoopFermion (C : Contraction nf nA κ) : Type :=
  {f : FermionLine C // edgeLoop (lineData C) (edgeOf (.inl f : Line C)) = true}

/-- A fermion line on a loop as a parametric line on a loop. -/
def LoopFermion.toLoopLine (f : LoopFermion C) : LoopLine C := ⟨.inl f.1, f.2⟩

/-- The loop matrix of the parametric lines on a loop, numbered by `ι`. -/
def pMat {m : ℕ} (ι : LoopLine C ≃ Fin (m + 1)) : Fin (m + 1) → Fin 2 → ℤ :=
  fun i s => loopCoeff C (ι.symm i).1.line s

theorem label_lt_iff (l : Line C) : (edgeOf l).1 < N ↔ l.isLeft := by
  rcases l with f | g
  · simp only [edgeOf, Line.label, Sum.isLeft_inl, iff_true]
    exact f.1.1.2
  · simp [edgeOf, Line.label]

theorem sum_line_weight (F : Line C → ℕ) :
    ∑ q : PLine C, F q.line = ∑ l : Line C, edgeWeight N (edgeOf l) * F l := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, PLine.line, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  congr 1
  · refine Finset.sum_congr rfl fun f _ => ?_
    rw [edgeWeight, ite_eq_left ((label_lt_iff (.inl f)).mpr rfl), one_mul]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [edgeWeight, ite_eq_right (by rw [label_lt_iff]; simp)]

theorem sum_loopLine' (F : FermionLine C → ℕ)
    (hF : ∀ f, F f ≠ 0 → edgeLoop (lineData C) (edgeOf (.inl f : Line C)) = true) :
    ∑ f : LoopFermion C, F f.1 = ∑ f : FermionLine C, F f := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter fun f : FermionLine C =>
    edgeLoop (lineData C) (edgeOf (.inl f : Line C)) = true) (by simp) F, Finset.sum_filter]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs with h
  · rfl
  · by_contra h'
    exact h (hF q (Ne.symm h'))

theorem sum_loopLine (F : PLine C → ℕ)
    (hF : ∀ q, F q ≠ 0 → edgeLoop (lineData C) (edgeOf q.line) = true) :
    ∑ q : LoopLine C, F q.1 = ∑ q : PLine C, F q := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter fun q : PLine C =>
    edgeLoop (lineData C) (edgeOf q.line) = true) (by simp) F, Finset.sum_filter]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs with h
  · rfl
  · by_contra h'
    exact h (hF q (Ne.symm h'))

/-- **The criterion does not depend on the numbering.** -/
theorem noSubdivergenceRefined_pMat_of_edgeCrit {m : ℕ} (ι : LoopLine C ≃ Fin (m + 1))
    (h : EdgeCrit (lineData C)) :
    NoSubdivergenceRefined 2 (Finset.univ.image fun f : LoopFermion C => ι f.toLoopLine)
      (castLoopMatrix (pMat ι)) := by
  classical
  rw [noSubdivergenceRefined_castLoopMatrix_iff]
  intro i
  set l₀ := (ι.symm i).1.line
  have hdet : ∀ j, intPairDet (pMat ι) i j =
      edgeDet (lineData C) (edgeOf l₀) (edgeOf (ι.symm j).1.line) := fun j => rfl
  have hx := h (edgeOf l₀) (mem_lineData.mpr ⟨l₀, rfl⟩) (ι.symm i).2
  rw [sum_lineData, sum_lineData] at hx
  have hR : (Finset.univ.filter fun j => intPairDet (pMat ι) i j ≠ 0).card =
      ∑ l : Line C, if edgeDet (lineData C) (edgeOf l₀) (edgeOf l) ≠ 0 then
        edgeWeight N (edgeOf l) else 0 := by
    rw [Finset.card_filter]
    simp only [hdet]
    rw [← Fintype.sum_equiv ι (fun q => if edgeDet (lineData C) (edgeOf l₀) (edgeOf q.1.line) ≠ 0
      then 1 else 0) _ (fun q => by simp)]
    rw [sum_loopLine (fun q => if edgeDet (lineData C) (edgeOf l₀) (edgeOf q.line) ≠ 0
      then 1 else 0) (fun q hq => edgeLoop_of_edgeDet_ne_zero (by simpa using hq))]
    refine (sum_line_weight fun l =>
      if edgeDet (lineData C) (edgeOf l₀) (edgeOf l) ≠ 0 then 1 else 0).trans ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  have hL : ((Finset.univ.image fun f : LoopFermion C => ι f.toLoopLine).filter
      fun e => intPairDet (pMat ι) i e ≠ 0).card =
      ∑ l : Line C, if (edgeOf l).1 < N ∧ edgeDet (lineData C) (edgeOf l₀) (edgeOf l) ≠ 0 then
        1 else 0 := by
    rw [Finset.filter_image, Finset.card_image_of_injective _
      (fun a b hab => Subtype.ext (Sum.inl_injective (congrArg Subtype.val (ι.injective hab)))),
      Finset.card_filter]
    simp only [hdet, Equiv.symm_apply_apply, Fintype.sum_sum_type]
    have h0 : ∀ g : PhotonLine C, ¬ (edgeOf (Sum.inr g : Line C)).1 < N := fun g => by
      simp [label_lt_iff]
    simp only [h0, false_and, ite_false, Finset.sum_const_zero, add_zero]
    refine Eq.trans (sum_loopLine' (C := C) (fun f => if edgeDet (lineData C) (edgeOf l₀)
      (edgeOf (Sum.inl f : Line C)) ≠ 0 then 1 else 0)
      (fun f hf => edgeLoop_of_edgeDet_ne_zero (by simpa using hf))) ?_
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [label_lt_iff, Sum.isLeft_inl, true_and]
  rw [hR, hL]
  exact hx

end QED.GradedProof.X0

end
