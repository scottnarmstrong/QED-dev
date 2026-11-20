/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CSplit
public import QED.Frozen.WickModel.FermionSign

/-!
# (X₁) piece C: gluing a self-energy onto a fermion leg

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C1. Let `C₁` be a contraction with one fermion pair and `nA`
photons on the left piece of a split `e` (`QED/GradedProof/X1CSplit.lean`) and `C₂` a
contraction with one fermion pair and no photon (a self-energy) on the right piece. Write `σ̂₁`
for the pairing `σ₁` of `C₁` extended by the identity on the fields of the right piece, and `σ̂₂`
likewise, both with the external field shared.

* `glueIn e C₁ C₂` has pairing `σ̂₂ σ̂₁`: the `Ψ` of the vertex `a` of `C₁` that was contracted
  with the incoming external `Ψ̄(y)` is now contracted with the `Ψ̄` of the vertex `c` of `C₂`
  contracted with the outgoing external `Ψ(x)` of `C₂` (the bridge `c → a`), and `Ψ̄(y)` is
  contracted with the vertex of `C₂` that it was contracted with in `C₂`. So `C₂` sits on the
  incoming leg of `C₁`.
* `glueOut e C₁ C₂` has pairing `σ̂₁ σ̂₂`: `C₂` sits on the outgoing leg of `C₁`.

In both the photon pairing is the disjoint union. Writing the pairing as a product of the two
extended pairings gives the fermionic sign at once: `fermionSign_glueIn`, `fermionSign_glueOut`
(the sign (X₅) is multiplicative).
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction fermionSign)

variable {N N₁ N₂ nA : ℕ} {κ : Fin N → Wick.VertexKind} (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N)

/-- The disjoint union of fixed-point-free involutions is one. -/
theorem dsum_invol {α β γ : Type*} (E : α ⊕ β ≃ γ) {τ₁ : Equiv.Perm α} {τ₂ : Equiv.Perm β}
    (h₁ : ∀ b, τ₁ (τ₁ b) = b ∧ τ₁ b ≠ b) (h₂ : ∀ b, τ₂ (τ₂ b) = b ∧ τ₂ b ≠ b) (b : γ) :
    dsum E τ₁ τ₂ (dsum E τ₁ τ₂ b) = b ∧ dsum E τ₁ τ₂ b ≠ b := by
  obtain ⟨x, rfl⟩ := E.surjective b
  rcases x with x | x
  · rw [dsum_apply_inl, dsum_apply_inl, (h₁ x).1]
    exact ⟨rfl, fun h => (h₁ x).2 (Sum.inl_injective (E.injective h))⟩
  · rw [dsum_apply_inr, dsum_apply_inr, (h₂ x).1]
    exact ⟨rfl, fun h => (h₂ x).2 (Sum.inr_injective (E.injective h))⟩

/-- The photon pairing of a glued contraction: the disjoint union, with the photon externals of
the left piece. -/
def gluePhotons (τ₁ : Equiv.Perm (Fin nA ⊕ Wick.PhotonSlot (leftKinds κ e)))
    (τ₂ : Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot (rightKinds κ e))) :
    Equiv.Perm (Fin nA ⊕ Wick.PhotonSlot κ) :=
  dsum (pL κ e nA) τ₁ τ₂

/-- The fermion pairing of the left piece, extended by the identity. -/
def hatL (σ₁ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e))) :
    Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex κ) :=
  dsum (fL κ e 1) σ₁ 1

/-- The fermion pairing of the right piece, extended by the identity. -/
def hatR (σ₂ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e))) :
    Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex κ) :=
  dsum (fR κ e 1) 1 σ₂

/-- **Gluing a self-energy `C₂` onto the incoming leg of `C₁`.** -/
def glueIn (C₁ : Contraction 1 nA (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e)) :
    Contraction 1 nA κ :=
  ⟨(hatR e C₂.1.1 * hatL e C₁.1.1, gluePhotons e C₁.1.2 C₂.1.2), dsum_invol _ C₁.2 C₂.2⟩

/-- **Gluing a self-energy `C₂` onto the outgoing leg of `C₁`.** -/
def glueOut (C₁ : Contraction 1 nA (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e)) :
    Contraction 1 nA κ :=
  ⟨(hatL e C₁.1.1 * hatR e C₂.1.1, gluePhotons e C₁.1.2 C₂.1.2), dsum_invol _ C₁.2 C₂.2⟩

/-! ### The fermionic sign -/

theorem sign_hatL (σ₁ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e))) :
    Equiv.Perm.sign (hatL e σ₁) = Equiv.Perm.sign σ₁ := by
  rw [hatL, sign_dsum, Equiv.Perm.sign_one, mul_one]

theorem sign_hatR (σ₂ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e))) :
    Equiv.Perm.sign (hatR e σ₂) = Equiv.Perm.sign σ₂ := by
  rw [hatR, sign_dsum, Equiv.Perm.sign_one, one_mul]

variable (C₁ : Contraction 1 nA (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e))

theorem fermionSign_glue_aux (s : ℤˣ) (hs : s = Equiv.Perm.sign C₁.1.1 * Equiv.Perm.sign C₂.1.1) :
    (-1) ^ Fintype.card (Wick.FermionVertex κ) * (s : ℤ) = fermionSign C₁ * fermionSign C₂ := by
  rw [hs, card_fermionVertex_split κ e, fermionSign, fermionSign, pow_add, Units.val_mul]
  ring

/-- **The fermionic sign is multiplicative** under gluing onto the incoming leg. -/
theorem fermionSign_glueIn : fermionSign (glueIn e C₁ C₂) = fermionSign C₁ * fermionSign C₂ := by
  refine fermionSign_glue_aux e C₁ C₂ _ ?_
  change Equiv.Perm.sign (hatR e C₂.1.1 * hatL e C₁.1.1) = _
  rw [Equiv.Perm.sign_mul, sign_hatL, sign_hatR, mul_comm]

/-- **The fermionic sign is multiplicative** under gluing onto the outgoing leg. -/
theorem fermionSign_glueOut :
    fermionSign (glueOut e C₁ C₂) = fermionSign C₁ * fermionSign C₂ := by
  refine fermionSign_glue_aux e C₁ C₂ _ ?_
  change Equiv.Perm.sign (hatL e C₁.1.1 * hatR e C₂.1.1) = _
  rw [Equiv.Perm.sign_mul, sign_hatL, sign_hatR]

/-! ### The pairings of the glued contractions -/

variable {e}

theorem hatL_left (σ₁ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)))
    (x : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)) :
    hatL e σ₁ (fL κ e 1 (.inl x)) = fL κ e 1 (.inl (σ₁ x)) := dsum_apply_inl _ _ _ _

theorem hatL_right (σ₁ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)))
    (t : Wick.FermionVertex (rightKinds κ e)) :
    hatL e σ₁ (.inr (fvSplit κ e (.inr t))) = .inr (fvSplit κ e (.inr t)) :=
  dsum_apply_inr (fL κ e 1) σ₁ 1 (.inr t)

theorem hatR_right (σ₂ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e)))
    (x : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e)) :
    hatR e σ₂ (fR κ e 1 (.inr x)) = fR κ e 1 (.inr (σ₂ x)) := dsum_apply_inr _ _ _ _

theorem hatR_left (σ₂ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e)))
    (t : Wick.FermionVertex (leftKinds κ e)) :
    hatR e σ₂ (.inr (fvSplit κ e (.inl t))) = .inr (fvSplit κ e (.inl t)) :=
  dsum_apply_inl (fR κ e 1) 1 σ₂ (.inr t)

theorem fL_inl_eq_fR (i : Fin 1) : fL κ e 1 (.inl (.inl i)) = fR κ e 1 (.inr (.inl i)) := rfl

/-- The pairing of `glueIn` on a field of the left piece contracted (in `C₁`) with a vertex. -/
theorem glueIn_left {x : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)}
    {t : Wick.FermionVertex (leftKinds κ e)} (h : C₁.1.1 x = .inr t) :
    (glueIn e C₁ C₂).1.1 (fL κ e 1 (.inl x)) = .inr (fvSplit κ e (.inl t)) := by
  change hatR e C₂.1.1 (hatL e C₁.1.1 _) = _
  rw [hatL_left, h, fL_inl_inr, hatR_left]

/-- The pairing of `glueIn` on the field of the left piece contracted (in `C₁`) with the
incoming external: it is contracted with what that external is contracted with in `C₂`. -/
theorem glueIn_left_ext {x : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)} {i : Fin 1}
    (h : C₁.1.1 x = .inl i) :
    (glueIn e C₁ C₂).1.1 (fL κ e 1 (.inl x)) = fR κ e 1 (.inr (C₂.1.1 (.inl i))) := by
  change hatR e C₂.1.1 (hatL e C₁.1.1 _) = _
  rw [hatL_left, h, fL_inl_eq_fR, hatR_right]

/-- The pairing of `glueIn` on a vertex field of the right piece. -/
theorem glueIn_right (t : Wick.FermionVertex (rightKinds κ e)) :
    (glueIn e C₁ C₂).1.1 (.inr (fvSplit κ e (.inr t))) = fR κ e 1 (.inr (C₂.1.1 (.inr t))) := by
  change hatR e C₂.1.1 (hatL e C₁.1.1 _) = _
  rw [hatL_right, ← fR_inr_inr, hatR_right]

/-- The pairing of `glueOut` on a field of the right piece contracted (in `C₂`) with a vertex. -/
theorem glueOut_right {x : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e)}
    {t : Wick.FermionVertex (rightKinds κ e)} (h : C₂.1.1 x = .inr t) :
    (glueOut e C₁ C₂).1.1 (fR κ e 1 (.inr x)) = .inr (fvSplit κ e (.inr t)) := by
  change hatL e C₁.1.1 (hatR e C₂.1.1 _) = _
  rw [hatR_right, h, fR_inr_inr, hatL_right]

/-- The pairing of `glueOut` on the field of the right piece contracted (in `C₂`) with the
incoming external: it is contracted with what the outgoing external is contracted with in `C₁`. -/
theorem glueOut_right_ext {x : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e)} {i : Fin 1}
    (h : C₂.1.1 x = .inl i) :
    (glueOut e C₁ C₂).1.1 (fR κ e 1 (.inr x)) = fL κ e 1 (.inl (C₁.1.1 (.inl i))) := by
  change hatL e C₁.1.1 (hatR e C₂.1.1 _) = _
  rw [hatR_right, h, ← fL_inl_eq_fR, hatL_left]

/-- The pairing of `glueOut` on a vertex field of the left piece. -/
theorem glueOut_left (t : Wick.FermionVertex (leftKinds κ e)) :
    (glueOut e C₁ C₂).1.1 (.inr (fvSplit κ e (.inl t))) = fL κ e 1 (.inl (C₁.1.1 (.inr t))) := by
  change hatL e C₁.1.1 (hatR e C₂.1.1 _) = _
  rw [hatR_left, ← fL_inl_inr, hatL_left]

/-- The photon pairing of a glued contraction on the fields of the left piece. -/
theorem gluePhotons_left (x : Fin nA ⊕ Wick.PhotonSlot (leftKinds κ e)) :
    gluePhotons e C₁.1.2 C₂.1.2 (pL κ e nA (.inl x)) = pL κ e nA (.inl (C₁.1.2 x)) :=
  dsum_apply_inl _ _ _ _

/-- The photon pairing of a glued contraction on the fields of the right piece. -/
theorem gluePhotons_right (a : Wick.PhotonSlot (rightKinds κ e)) :
    gluePhotons e C₁.1.2 C₂.1.2 (.inr (psSplit κ e (.inr a))) =
      pL κ e nA (.inr (C₂.1.2 (.inr a))) :=
  dsum_apply_inr (pL κ e nA) _ _ (.inr a)

end QED.GradedProof.X1C

end
