/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.GradedOrder
public import QED.Frozen.Graded.Flavoring
public import QED.Frozen.WickModel.Contraction
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Equiv.Sum

/-!
# (X₁) piece C: splitting the vertices of a kind sequence into two pieces

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C1. A one-particle-reducible contraction of the vertex sequence
`κ : Fin N → VertexKind` is glued from two contractions on complementary sets of vertices. The
two sets are given by a bijection `e : Fin N₁ ⊕ Fin N₂ ≃ Fin N`; the pieces live on the kind
sequences `leftKinds κ e = κ ∘ e ∘ inl` and `rightKinds κ e = κ ∘ e ∘ inr`, so that no cast is
needed between the kinds of a vertex and of its image. Summing over all `e` covers every way of
placing the labels of the two pieces (the `N! / (N₁! N₂!)` label placements of the counting).

* `fvSplit`, `psSplit`, `ctSplit`: the fermion vertices, photon fields and counterterm vertices of
  `κ` are those of the two pieces.
* `gradedOrder_split`: the graded order is additive.
* `fL`, `fR`, `pL`: the fields with the external fields of one piece, as sums of the fields of
  the pieces; `dsum` is the disjoint union of two permutations and `sign_dsum` its sign.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction)
open QED.Graded

variable {N N₁ N₂ : ℕ} (κ : Fin N → Wick.VertexKind) (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N)

/-- The kinds of the left piece of the split `e`. -/
abbrev leftKinds : Fin N₁ → Wick.VertexKind := fun t => κ (e (.inl t))

/-- The kinds of the right piece of the split `e`. -/
abbrev rightKinds : Fin N₂ → Wick.VertexKind := fun t => κ (e (.inr t))

/-! ### The fields of the pieces -/

/-- The fermion vertices of `κ` are those of the two pieces. -/
def fvSplit : Wick.FermionVertex (leftKinds κ e) ⊕ Wick.FermionVertex (rightKinds κ e) ≃
    Wick.FermionVertex κ :=
  (Equiv.subtypeSum (p := fun x => κ (e x) ≠ .photonCt)).symm.trans
    (e.subtypeEquiv (q := fun t => κ t ≠ .photonCt) fun _ => Iff.rfl)

/-- The photon fields of `κ` are those of the two pieces. -/
def psSplit : Wick.PhotonSlot (leftKinds κ e) ⊕ Wick.PhotonSlot (rightKinds κ e) ≃
    Wick.PhotonSlot κ :=
  (Equiv.sumSigmaDistrib fun x => Fin (κ (e x)).photonSlots).symm.trans
    (Equiv.sigmaCongrLeft (β := fun t => Fin (κ t).photonSlots) e)

/-- The counterterm vertices of `κ` are those of the two pieces. -/
def ctSplit : CtVertex (leftKinds κ e) ⊕ CtVertex (rightKinds κ e) ≃ CtVertex κ :=
  (Equiv.subtypeSum (p := fun x => κ (e x) ≠ .gauge)).symm.trans
    (e.subtypeEquiv (q := fun t => κ t ≠ .gauge) fun _ => Iff.rfl)

variable {κ e}

@[simp] theorem fvSplit_inl (t : Wick.FermionVertex (leftKinds κ e)) :
    fvSplit κ e (.inl t) = ⟨e (.inl t.1), t.2⟩ := rfl

@[simp] theorem fvSplit_inr (t : Wick.FermionVertex (rightKinds κ e)) :
    fvSplit κ e (.inr t) = ⟨e (.inr t.1), t.2⟩ := rfl

@[simp] theorem psSplit_inl (a : Wick.PhotonSlot (leftKinds κ e)) :
    psSplit κ e (.inl a) = ⟨e (.inl a.1), a.2⟩ := rfl

@[simp] theorem psSplit_inr (a : Wick.PhotonSlot (rightKinds κ e)) :
    psSplit κ e (.inr a) = ⟨e (.inr a.1), a.2⟩ := rfl

@[simp] theorem ctSplit_inl (t : CtVertex (leftKinds κ e)) :
    ctSplit κ e (.inl t) = ⟨e (.inl t.1), t.2⟩ := rfl

@[simp] theorem ctSplit_inr (t : CtVertex (rightKinds κ e)) :
    ctSplit κ e (.inr t) = ⟨e (.inr t.1), t.2⟩ := rfl

variable (κ e)

theorem card_fermionVertex_split :
    Fintype.card (Wick.FermionVertex κ) = Fintype.card (Wick.FermionVertex (leftKinds κ e)) +
      Fintype.card (Wick.FermionVertex (rightKinds κ e)) := by
  rw [← Fintype.card_sum, Fintype.card_congr (fvSplit κ e)]

/-! ### Gradings -/

/-- The grading of the left piece induced by a grading of `κ`. -/
def gradL (g : Grading κ) : Grading (leftKinds κ e) := fun t => g (ctSplit κ e (.inl t))

/-- The grading of the right piece induced by a grading of `κ`. -/
def gradR (g : Grading κ) : Grading (rightKinds κ e) := fun t => g (ctSplit κ e (.inr t))

/-- **The graded order is additive** over the two pieces. -/
theorem gradedOrder_split (g : Grading κ) :
    gradedOrder κ g = gradedOrder (leftKinds κ e) (gradL κ e g) +
      gradedOrder (rightKinds κ e) (gradR κ e g) := by
  unfold gradedOrder
  rw [← e.sum_comp (fun t => (κ t).order), Fintype.sum_sum_type,
    ← (ctSplit κ e).sum_comp (fun t => 2 * g t), Fintype.sum_sum_type]
  simp only [gradL, gradR, ctSplit_inl, ctSplit_inr]
  ring

/-! ### The fields with the externals of one piece -/

/-- The fermion fields of `κ` with `n` external fields, those of the left piece. -/
def fL (n : ℕ) : (Fin n ⊕ Wick.FermionVertex (leftKinds κ e)) ⊕
    (Fin 0 ⊕ Wick.FermionVertex (rightKinds κ e)) ≃ Fin n ⊕ Wick.FermionVertex κ :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.emptySum (Fin 0) _)).trans
    ((Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _) (fvSplit κ e)))

/-- The fermion fields of `κ` with `n` external fields, those of the right piece. -/
def fR (n : ℕ) : (Fin 0 ⊕ Wick.FermionVertex (leftKinds κ e)) ⊕
    (Fin n ⊕ Wick.FermionVertex (rightKinds κ e)) ≃ Fin n ⊕ Wick.FermionVertex κ :=
  (Equiv.sumComm _ _).trans (((Equiv.sumCongr (Equiv.refl _) (Equiv.emptySum (Fin 0) _)).trans
    ((Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _)
      ((Equiv.sumComm _ _).trans (fvSplit κ e))))))

/-- The photon fields of `κ` with `n` external fields, those of the left piece. -/
def pL (n : ℕ) : (Fin n ⊕ Wick.PhotonSlot (leftKinds κ e)) ⊕
    (Fin 0 ⊕ Wick.PhotonSlot (rightKinds κ e)) ≃ Fin n ⊕ Wick.PhotonSlot κ :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.emptySum (Fin 0) _)).trans
    ((Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _) (psSplit κ e)))

variable {κ e} {n : ℕ}

@[simp] theorem fL_inl_inl (i : Fin n) : fL κ e n (.inl (.inl i)) = .inl i := rfl
@[simp] theorem fL_inl_inr (t : Wick.FermionVertex (leftKinds κ e)) :
    fL κ e n (.inl (.inr t)) = .inr (fvSplit κ e (.inl t)) := rfl
@[simp] theorem fL_inr_inr (t : Wick.FermionVertex (rightKinds κ e)) :
    fL κ e n (.inr (.inr t)) = .inr (fvSplit κ e (.inr t)) := rfl
@[simp] theorem fR_inr_inl (i : Fin n) : fR κ e n (.inr (.inl i)) = .inl i := rfl
@[simp] theorem fR_inl_inr (t : Wick.FermionVertex (leftKinds κ e)) :
    fR κ e n (.inl (.inr t)) = .inr (fvSplit κ e (.inl t)) := rfl
@[simp] theorem fR_inr_inr (t : Wick.FermionVertex (rightKinds κ e)) :
    fR κ e n (.inr (.inr t)) = .inr (fvSplit κ e (.inr t)) := rfl
@[simp] theorem pL_inl_inl (i : Fin n) : pL κ e n (.inl (.inl i)) = .inl i := rfl
@[simp] theorem pL_inl_inr (a : Wick.PhotonSlot (leftKinds κ e)) :
    pL κ e n (.inl (.inr a)) = .inr (psSplit κ e (.inl a)) := rfl
@[simp] theorem pL_inr_inr (a : Wick.PhotonSlot (rightKinds κ e)) :
    pL κ e n (.inr (.inr a)) = .inr (psSplit κ e (.inr a)) := rfl

/-! ### Disjoint unions of permutations -/

/-- The disjoint union of permutations of the two summands, transported along `E`. -/
def dsum {α β γ : Type*} (E : α ⊕ β ≃ γ) (σ₁ : Equiv.Perm α) (σ₂ : Equiv.Perm β) :
    Equiv.Perm γ :=
  E.permCongr (Equiv.sumCongr σ₁ σ₂)

theorem dsum_apply_inl {α β γ : Type*} (E : α ⊕ β ≃ γ) (σ₁ : Equiv.Perm α)
    (σ₂ : Equiv.Perm β) (x : α) : dsum E σ₁ σ₂ (E (.inl x)) = E (.inl (σ₁ x)) := by
  simp [dsum, Equiv.permCongr_apply]

theorem dsum_apply_inr {α β γ : Type*} (E : α ⊕ β ≃ γ) (σ₁ : Equiv.Perm α)
    (σ₂ : Equiv.Perm β) (x : β) : dsum E σ₁ σ₂ (E (.inr x)) = E (.inr (σ₂ x)) := by
  simp [dsum, Equiv.permCongr_apply]

theorem sign_dsum {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] (E : α ⊕ β ≃ γ) (σ₁ : Equiv.Perm α) (σ₂ : Equiv.Perm β) :
    Equiv.Perm.sign (dsum E σ₁ σ₂) = Equiv.Perm.sign σ₁ * Equiv.Perm.sign σ₂ := by
  rw [dsum, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]

end QED.GradedProof.X1C

end
