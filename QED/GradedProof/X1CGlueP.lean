/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CGlueF

/-!
# (X₁) piece C: gluing a vacuum polarization onto the photon leg

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C1. Let `C₁` be a contraction with one fermion pair and one photon
on the left piece of a split `e` and `C₂` a contraction with two photons and no fermion pair (a
vacuum polarization) on the right piece. In `C₁` the external photon `A(z)` is contracted with
the field `extSlot C₁` (it is never contracted with itself). `glueP e C₁ C₂` contracts `A(z)` with
what the first external photon `A(z₁)` of `C₂` is contracted with, and `extSlot C₁` with what the
second external photon `A(z₂)` of `C₂` is contracted with (the bridge); all other pairs are those
of `C₁` and `C₂`, and the fermion pairing is the disjoint union. The momentum `k` of the
vacuum polarization `Π(k)` enters through `z₁` and leaves through `z₂`, so the external photon of
the glued contraction is the first index of `Π`, as in `QED.GradedProof.X1C.photonLeg`.

The photon pairing is built on the model `Fin 1 ⊕ (PhotonSlot L ⊕ PhotonSlot R)` as the map
`photonModel`, which agrees with `τ₂` (read through the embedding `liftR`) on the fields
`z, extSlot C₁` and those of `C₂`, and with `τ₁` on the other fields of `C₁`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction fermionSign)

variable {N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind} (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N)

/-- The field contracted with the external photon of a contraction with one photon. -/
def extSlot {M : ℕ} {κ' : Fin M → Wick.VertexKind} {nf : ℕ} (C : Contraction nf 1 κ') :
    Wick.PhotonSlot κ' :=
  (C.1.2 (.inl 0)).getRight (by
    rcases h : C.1.2 (.inl 0) with i | a
    · exact absurd (h.trans (congrArg Sum.inl (Subsingleton.elim i 0))) (C.2 _).2
    · rfl)

theorem extSlot_spec {M : ℕ} {κ' : Fin M → Wick.VertexKind} {nf : ℕ} (C : Contraction nf 1 κ') :
    C.1.2 (.inl 0) = .inr (extSlot C) := by
  simp [extSlot]

theorem extSlot_spec' {M : ℕ} {κ' : Fin M → Wick.VertexKind} {nf : ℕ}
    (C : Contraction nf 1 κ') : C.1.2 (.inr (extSlot C)) = .inl 0 := by
  rw [← extSlot_spec, (C.2 _).1]

/-- The model of the photon fields of the glued contraction. -/
abbrev PModel (κ : Fin N → Wick.VertexKind) (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N) : Type :=
  Fin 1 ⊕ (Wick.PhotonSlot (leftKinds κ e) ⊕ Wick.PhotonSlot (rightKinds κ e))

/-- The model of the photon fields is the photon fields of `κ`. -/
def pModelEquiv : PModel κ e ≃ Fin 1 ⊕ Wick.PhotonSlot κ :=
  Equiv.sumCongr (Equiv.refl _) (psSplit κ e)

/-- The fields of `C₂` with its externals read as `z` and the field `a` of `C₁`. -/
def liftR (a : Wick.PhotonSlot (leftKinds κ e)) :
    Fin 2 ⊕ Wick.PhotonSlot (rightKinds κ e) → PModel κ e
  | .inl i => if i = 0 then .inl 0 else .inr (.inl a)
  | .inr s => .inr (.inr s)

/-- The fields of `C₁` in the model (its external read as `z`). -/
def liftL : Fin 1 ⊕ Wick.PhotonSlot (leftKinds κ e) → PModel κ e
  | .inl _ => .inl 0
  | .inr s => .inr (.inl s)

theorem liftR_injective (a : Wick.PhotonSlot (leftKinds κ e)) :
    Function.Injective (liftR e a) := by
  rintro (i | s) (j | s') h
  · fin_cases i <;> fin_cases j <;> simp_all [liftR]
  · fin_cases i <;> simp_all [liftR]
  · fin_cases j <;> simp_all [liftR]
  · simpa [liftR] using h

variable (C₁ : Contraction 1 1 (leftKinds κ e)) (C₂ : Contraction 0 2 (rightKinds κ e))

/-- The photon pairing of the glued contraction, on the model. -/
def photonModel : PModel κ e → PModel κ e
  | .inl _ => liftR e (extSlot C₁) (C₂.1.2 (.inl 0))
  | .inr (.inl s) => if s = extSlot C₁ then liftR e (extSlot C₁) (C₂.1.2 (.inl 1))
      else liftL e (C₁.1.2 (.inr s))
  | .inr (.inr s) => liftR e (extSlot C₁) (C₂.1.2 (.inr s))

theorem photonModel_liftR (y : Fin 2 ⊕ Wick.PhotonSlot (rightKinds κ e)) :
    photonModel e C₁ C₂ (liftR e (extSlot C₁) y) = liftR e (extSlot C₁) (C₂.1.2 y) := by
  rcases y with i | s
  · fin_cases i <;> simp [liftR, photonModel]
  · rfl

/-- The fields of `C₁` other than its external photon and `extSlot C₁` are moved by `τ₁` to
fields of the same kind. -/
theorem photonPair_left {s : Wick.PhotonSlot (leftKinds κ e)} (hs : s ≠ extSlot C₁) :
    ∃ s', C₁.1.2 (.inr s) = .inr s' ∧ s' ≠ extSlot C₁ ∧ s' ≠ s := by
  rcases h : C₁.1.2 (.inr s) with i | s'
  · refine absurd ?_ hs
    have h' := congrArg C₁.1.2 h
    rw [(C₁.2 _).1, Subsingleton.elim i 0, extSlot_spec] at h'
    exact Sum.inr_injective h'
  · refine ⟨s', rfl, fun hs' => ?_, fun hs' => (C₁.2 (.inr s)).2 (h.trans (by rw [hs']))⟩
    have h' := congrArg C₁.1.2 h
    rw [(C₁.2 _).1, hs', extSlot_spec'] at h'
    exact Sum.inr_ne_inl h'

theorem photonModel_left {s : Wick.PhotonSlot (leftKinds κ e)} (hs : s ≠ extSlot C₁)
    {s' : Wick.PhotonSlot (leftKinds κ e)} (h : C₁.1.2 (.inr s) = .inr s') :
    photonModel e C₁ C₂ (.inr (.inl s)) = .inr (.inl s') := by
  simp [photonModel, hs, h, liftL]

/-- Every field of the model is a field of `C₂` read through `liftR`, or another field of `C₁`. -/
theorem pModel_cases (x : PModel κ e) :
    (∃ y, x = liftR e (extSlot C₁) y) ∨
      ∃ s, s ≠ extSlot C₁ ∧ x = .inr (.inl s) := by
  rcases x with i | s | s
  · exact .inl ⟨.inl 0, by simp [liftR, Subsingleton.elim i 0]⟩
  · by_cases hs : s = extSlot C₁
    · exact .inl ⟨.inl 1, by simp [liftR, hs]⟩
    · exact .inr ⟨s, hs, rfl⟩
  · exact .inl ⟨.inr s, rfl⟩

theorem photonModel_invol (x : PModel κ e) :
    photonModel e C₁ C₂ (photonModel e C₁ C₂ x) = x ∧ photonModel e C₁ C₂ x ≠ x := by
  rcases pModel_cases e C₁ x with ⟨y, rfl⟩ | ⟨s, hs, rfl⟩
  · rw [photonModel_liftR, photonModel_liftR, (C₂.2 y).1]
    exact ⟨rfl, fun h => (C₂.2 y).2 (liftR_injective e _ h)⟩
  · obtain ⟨s', h, hs', hne⟩ := photonPair_left e C₁ hs
    have h2 : C₁.1.2 (.inr s') = .inr s := by rw [← h, (C₁.2 _).1]
    rw [photonModel_left e C₁ C₂ hs h, photonModel_left e C₁ C₂ hs' h2]
    exact ⟨rfl, fun h' => hne (Sum.inl_injective (Sum.inr_injective h'))⟩

/-- The photon pairing of the glued contraction. -/
def gluePPhotons : Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot κ) :=
  (pModelEquiv e).permCongr
    (Function.Involutive.toPerm (photonModel e C₁ C₂) fun x => (photonModel_invol e C₁ C₂ x).1)

theorem gluePPhotons_apply (x : PModel κ e) :
    gluePPhotons e C₁ C₂ (pModelEquiv e x) = pModelEquiv e (photonModel e C₁ C₂ x) := by
  simp only [gluePPhotons, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rfl

theorem gluePPhotons_invol (b : Fin 1 ⊕ Wick.PhotonSlot κ) :
    gluePPhotons e C₁ C₂ (gluePPhotons e C₁ C₂ b) = b ∧ gluePPhotons e C₁ C₂ b ≠ b := by
  obtain ⟨x, rfl⟩ := (pModelEquiv e).surjective b
  rw [gluePPhotons_apply, gluePPhotons_apply, (photonModel_invol e C₁ C₂ x).1]
  exact ⟨rfl, fun h => (photonModel_invol e C₁ C₂ x).2 ((pModelEquiv e).injective h)⟩

/-- **Gluing a vacuum polarization `C₂` onto the photon leg of `C₁`.** -/
def glueP : Contraction 1 1 κ :=
  ⟨(dsum (fL κ e 1) C₁.1.1 C₂.1.1, gluePPhotons e C₁ C₂), gluePPhotons_invol e C₁ C₂⟩

/-- **The fermionic sign is multiplicative** under gluing onto the photon leg. -/
theorem fermionSign_glueP : fermionSign (glueP e C₁ C₂) = fermionSign C₁ * fermionSign C₂ := by
  simp only [fermionSign, glueP, sign_dsum, card_fermionVertex_split κ e, pow_add,
    Units.val_mul]
  ring

/-! ### The pairings of the glued contraction -/

theorem glueP_fermion_left (x : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)) :
    (glueP e C₁ C₂).1.1 (fL κ e 1 (.inl x)) = fL κ e 1 (.inl (C₁.1.1 x)) :=
  dsum_apply_inl _ _ _ _

theorem glueP_fermion_right (t : Wick.FermionVertex (rightKinds κ e)) :
    (glueP e C₁ C₂).1.1 (.inr (fvSplit κ e (.inr t))) = fL κ e 1 (.inr (C₂.1.1 (.inr t))) :=
  dsum_apply_inr (fL κ e 1) _ _ (.inr t)

/-- The external photon of the glued contraction is contracted with what `z₁` is contracted with
in `C₂`. -/
theorem glueP_photon_ext :
    (glueP e C₁ C₂).1.2 (.inl 0) = pModelEquiv e (liftR e (extSlot C₁) (C₂.1.2 (.inl 0))) :=
  gluePPhotons_apply e C₁ C₂ (.inl 0)

/-- The field `extSlot C₁` is contracted with what `z₂` is contracted with in `C₂`. -/
theorem glueP_photon_extSlot :
    (glueP e C₁ C₂).1.2 (.inr (psSplit κ e (.inl (extSlot C₁)))) =
      pModelEquiv e (liftR e (extSlot C₁) (C₂.1.2 (.inl 1))) := by
  have := gluePPhotons_apply e C₁ C₂ (.inr (.inl (extSlot C₁)))
  simp only [photonModel, ite_true] at this
  exact this

theorem glueP_photon_left {s s' : Wick.PhotonSlot (leftKinds κ e)} (hs : s ≠ extSlot C₁)
    (h : C₁.1.2 (.inr s) = .inr s') :
    (glueP e C₁ C₂).1.2 (.inr (psSplit κ e (.inl s))) = .inr (psSplit κ e (.inl s')) := by
  have := gluePPhotons_apply e C₁ C₂ (.inr (.inl s))
  rw [photonModel_left e C₁ C₂ hs h] at this
  exact this

theorem glueP_photon_right (s : Wick.PhotonSlot (rightKinds κ e)) :
    (glueP e C₁ C₂).1.2 (.inr (psSplit κ e (.inr s))) =
      pModelEquiv e (liftR e (extSlot C₁) (C₂.1.2 (.inr s))) :=
  gluePPhotons_apply e C₁ C₂ (.inr (.inr s))

end QED.GradedProof.X1C

end
