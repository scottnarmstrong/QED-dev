/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CLinesIn
public import QED.GradedProof.X1CGlueP

/-!
# (X₁) piece C: the lines of a vacuum polarization glued onto the photon leg

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C2. For a shuffle `e`, the internal lines of `glueP e C₁ C₂` are
those of `C₁`, those of `C₂`, and the bridge: the photon line joining `extSlot C₁` and the field
`w₂` of `C₂` contracted with its second external photon. Its orientation (from the smaller photon
key) depends on how the two pieces interleave, so the bridge is any photon line `b` of the glued
contraction starting at one of the two fields (`exists_bridgeP`).

* `fermionLineP`: the fermion lines of `glueP e C₁ C₂` are those of the pieces.
* `photonLineP`: its photon lines are those of the pieces and the bridge.
* `lineSplitP`: the `LineSplit` of `glueP e C₁ C₂`, with the bridge `b` from its first field to
  its head.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line FermionLine PhotonLine)
open QED.TwoLoop.Enumeration (tail_eq head_eq)
open QED.TwoLoop.LoopBound (apply_inr_photonLine photonKey_lt_head)

variable {N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}
  (C₁ : Contraction 1 1 (leftKinds κ e)) (C₂ : Contraction 0 2 (rightKinds κ e))

@[simp] theorem pModelEquiv_inl (i : Fin 1) : pModelEquiv e (.inl i : PModel κ e) = .inl i := rfl

@[simp] theorem pModelEquiv_inr (x : Wick.PhotonSlot (leftKinds κ e) ⊕
    Wick.PhotonSlot (rightKinds κ e)) :
    pModelEquiv e (.inr x : PModel κ e) = .inr (psSplit κ e x) := rfl

/-! ### The fermion lines -/

theorem glueP_left' {t s : Wick.FermionVertex (leftKinds κ e)} (h : C₁.1.1 (.inr t) = .inr s) :
    (glueP e C₁ C₂).1.1 (.inr (fvSplit κ e (.inl t))) = .inr (fvSplit κ e (.inl s)) := by
  rw [← fL_inl_inr, glueP_fermion_left, h]
  rfl

theorem glueP_right' {t s : Wick.FermionVertex (rightKinds κ e)} (h : C₂.1.1 (.inr t) = .inr s) :
    (glueP e C₁ C₂).1.1 (.inr (fvSplit κ e (.inr t))) = .inr (fvSplit κ e (.inr s)) := by
  rw [glueP_fermion_right, h]
  rfl

theorem exists_right_pair (t : Wick.FermionVertex (rightKinds κ e)) :
    ∃ s, C₂.1.1 (.inr t) = .inr s := by
  rcases h : C₂.1.1 (.inr t) with i | s
  · exact i.elim0
  · exact ⟨s, rfl⟩

/-- The fermion lines of the pieces, as fermion lines of `glueP e C₁ C₂`. -/
def fermionLineP : FermionLine C₁ ⊕ FermionLine C₂ → FermionLine (glueP e C₁ C₂)
  | .inl f => ⟨fvSplit κ e (.inl f.1), by
      obtain ⟨s, hs⟩ := Sum.isRight_iff.mp f.2
      rw [glueP_left' C₁ C₂ hs]; rfl⟩
  | .inr f => ⟨fvSplit κ e (.inr f.1), by
      obtain ⟨s, hs⟩ := exists_right_pair C₂ f.1
      rw [glueP_right' C₁ C₂ hs]; rfl⟩

theorem fermionLineP_bijective : Function.Bijective (fermionLineP C₁ C₂) := by
  constructor
  · rintro (f | f) (f' | f') h <;>
      have h' := congrArg (fun x : FermionLine (glueP e C₁ C₂) => (fvSplit κ e).symm x.1) h <;>
      simp [fermionLineP] at h'
    · exact congrArg Sum.inl (Subtype.ext (Subtype.ext h'))
    · exact congrArg Sum.inr (Subtype.ext (Subtype.ext h'))
  · intro f
    obtain ⟨x, hx⟩ := (fvSplit κ e).surjective f.1
    rcases x with t | t
    · have hf := f.2
      rw [← hx, ← fL_inl_inr, glueP_fermion_left] at hf
      rcases h2 : C₁.1.1 (.inr t) with i | s
      · rw [h2] at hf
        exact absurd hf (by simp [fL])
      · exact ⟨.inl ⟨t, by rw [h2]; rfl⟩, Subtype.ext hx⟩
    · obtain ⟨s, hs⟩ := exists_right_pair C₂ t
      exact ⟨.inr ⟨t, by rw [hs]; rfl⟩, Subtype.ext hx⟩

/-- **The fermion lines of `glueP e C₁ C₂`** are those of the pieces. -/
noncomputable def fermionLinePEquiv :
    FermionLine C₁ ⊕ FermionLine C₂ ≃ FermionLine (glueP e C₁ C₂) :=
  Equiv.ofBijective _ (fermionLineP_bijective C₁ C₂)

theorem fermionLineP_left_tail (f : FermionLine C₁) :
    (fermionLineP C₁ C₂ (.inl f)).tail = fvSplit κ e (.inl f.tail) := by
  obtain ⟨s, hs⟩ := Sum.isRight_iff.mp f.2
  rw [tail_eq _ (glueP_left' C₁ C₂ hs), tail_eq _ hs]

theorem fermionLineP_right_tail (f : FermionLine C₂) :
    (fermionLineP C₁ C₂ (.inr f)).tail = fvSplit κ e (.inr f.tail) := by
  obtain ⟨s, hs⟩ := exists_right_pair C₂ f.1
  rw [tail_eq _ (glueP_right' C₁ C₂ hs), tail_eq _ hs]

/-! ### The photon lines -/

variable {w₂ : Wick.PhotonSlot (rightKinds κ e)} (hw : C₂.1.2 (.inl 1) = .inr w₂)

theorem glueP_photon_right' {s s' : Wick.PhotonSlot (rightKinds κ e)}
    (h : C₂.1.2 (.inr s) = .inr s') :
    (glueP e C₁ C₂).1.2 (.inr (psSplit κ e (.inr s))) = .inr (psSplit κ e (.inr s')) := by
  rw [glueP_photon_right, h]
  rfl

include hw in
theorem glueP_ext_w₂ :
    (glueP e C₁ C₂).1.2 (.inr (psSplit κ e (.inl (extSlot C₁)))) =
      .inr (psSplit κ e (.inr w₂)) := by
  rw [glueP_photon_extSlot, hw]
  rfl

include hw in
theorem glueP_w₂_ext :
    (glueP e C₁ C₂).1.2 (.inr (psSplit κ e (.inr w₂))) =
      .inr (psSplit κ e (.inl (extSlot C₁))) := by
  have h : C₂.1.2 (.inr w₂) = .inl 1 := by rw [← hw, (C₂.2 _).1]
  rw [glueP_photon_right, h]
  simp [liftR]

theorem ne_extSlot (g : PhotonLine C₁) : g.1 ≠ extSlot C₁ := fun h => by
  have h1 := apply_inr_photonLine g
  rw [h, extSlot_spec'] at h1
  exact Sum.inl_ne_inr h1

include hw in
theorem ne_w₂ (g : PhotonLine C₂) : g.1 ≠ w₂ := fun h => by
  have h1 := apply_inr_photonLine g
  rw [h, show C₂.1.2 (.inr w₂) = .inl 1 by rw [← hw, (C₂.2 _).1]] at h1
  exact Sum.inl_ne_inr h1

include hw in
/-- **The bridge exists**: one of `extSlot C₁`, `w₂` starts a photon line of `glueP e C₁ C₂`. -/
theorem exists_bridgeP : ∃ b : PhotonLine (glueP e C₁ C₂),
    b.1 = psSplit κ e (.inl (extSlot C₁)) ∨ b.1 = psSplit κ e (.inr w₂) := by
  have hne : Wick.photonKey (psSplit κ e (.inl (extSlot C₁))) ≠
      Wick.photonKey (psSplit κ e (.inr w₂)) := fun h => by
    have := QED.TwoLoop.Chord.photonKey_injective h
    simp at this
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨⟨_, _, glueP_ext_w₂ C₁ C₂ hw, h⟩, .inl rfl⟩
  · exact ⟨⟨_, _, glueP_w₂_ext C₁ C₂ hw, h⟩, .inr rfl⟩

variable (he : IsShuffle e)

/-- The photon lines of the pieces and the bridge `b`, as photon lines of `glueP e C₁ C₂`. -/
def photonLineP (b : PhotonLine (glueP e C₁ C₂)) :
    PhotonLine C₁ ⊕ PhotonLine C₂ ⊕ Unit → PhotonLine (glueP e C₁ C₂)
  | .inl g => ⟨psSplit κ e (.inl g.1), ⟨psSplit κ e (.inl g.head),
      glueP_photon_left e C₁ C₂ (ne_extSlot C₁ g) (apply_inr_photonLine g),
      (key_inl_lt_iff he _ _).2 (photonKey_lt_head g)⟩⟩
  | .inr (.inl g) => ⟨psSplit κ e (.inr g.1), ⟨psSplit κ e (.inr g.head),
      glueP_photon_right' C₁ C₂ (apply_inr_photonLine g),
      (key_inr_lt_iff he _ _).2 (photonKey_lt_head g)⟩⟩
  | .inr (.inr _) => b

include hw in
/-- A photon line starting at `extSlot C₁` or `w₂` is the bridge `b`. -/
theorem eq_bridge {b s : PhotonLine (glueP e C₁ C₂)}
    (hb : b.1 = psSplit κ e (.inl (extSlot C₁)) ∨ b.1 = psSplit κ e (.inr w₂))
    (hs : s.1 = psSplit κ e (.inl (extSlot C₁)) ∨ s.1 = psSplit κ e (.inr w₂)) : s = b := by
  have kb := photonKey_lt_head b
  have ks := photonKey_lt_head s
  rcases hb with hb | hb <;> rcases hs with hs | hs
  · exact Subtype.ext (hs.trans hb.symm)
  · rw [head_eq b (hb ▸ glueP_ext_w₂ C₁ C₂ hw), hb] at kb
    rw [head_eq s (hs ▸ glueP_w₂_ext C₁ C₂ hw), hs] at ks
    omega
  · rw [head_eq b (hb ▸ glueP_w₂_ext C₁ C₂ hw), hb] at kb
    rw [head_eq s (hs ▸ glueP_ext_w₂ C₁ C₂ hw), hs] at ks
    omega
  · exact Subtype.ext (hs.trans hb.symm)

include hw in
theorem photonLineP_bijective {b : PhotonLine (glueP e C₁ C₂)}
    (hb : b.1 = psSplit κ e (.inl (extSlot C₁)) ∨ b.1 = psSplit κ e (.inr w₂)) :
    Function.Bijective (photonLineP C₁ C₂ he b) := by
  constructor
  · have h1 : ∀ g : PhotonLine C₁, psSplit κ e (.inl g.1) ≠ b.1 := fun g h => by
      rcases hb with hb | hb <;> rw [hb] at h
      · exact ne_extSlot C₁ g (Sum.inl_injective ((psSplit κ e).injective h))
      · exact Sum.inl_ne_inr ((psSplit κ e).injective h)
    have h2 : ∀ g : PhotonLine C₂, psSplit κ e (.inr g.1) ≠ b.1 := fun g h => by
      rcases hb with hb | hb <;> rw [hb] at h
      · exact Sum.inr_ne_inl ((psSplit κ e).injective h)
      · exact ne_w₂ C₂ hw g (Sum.inr_injective ((psSplit κ e).injective h))
    rintro (g | g | ⟨⟩) (g' | g' | ⟨⟩) h <;>
      have h' := congrArg Subtype.val h <;> simp only [photonLineP] at h'
    · exact congrArg Sum.inl (Subtype.ext (Sum.inl_injective ((psSplit κ e).injective h')))
    · exact absurd ((psSplit κ e).injective h') Sum.inl_ne_inr
    · exact absurd h' (h1 g)
    · exact absurd ((psSplit κ e).injective h') Sum.inr_ne_inl
    · exact congrArg (Sum.inr ∘ Sum.inl)
        (Subtype.ext (Sum.inr_injective ((psSplit κ e).injective h')))
    · exact absurd h' (h2 g)
    · exact absurd h'.symm (h1 g')
    · exact absurd h'.symm (h2 g')
    · rfl
  · intro s
    obtain ⟨y, hy⟩ := (psSplit κ e).surjective s.1
    obtain ⟨b', hb', hk⟩ := s.2
    rcases y with t | t
    · by_cases ht : t = extSlot C₁
      · subst ht
        exact ⟨.inr (.inr ()), (eq_bridge C₁ C₂ hw hb (.inl hy.symm)).symm⟩
      · rcases h2 : C₁.1.2 (.inr t) with i | t'
        · refine absurd ?_ ht
          have h' := congrArg C₁.1.2 h2
          rw [(C₁.2 _).1, Subsingleton.elim i 0, extSlot_spec] at h'
          exact Sum.inr_injective h'
        · rw [← hy, glueP_photon_left e C₁ C₂ ht h2] at hb'
          rw [← hy, ← Sum.inr_injective hb', key_inl_lt_iff he] at hk
          exact ⟨.inl ⟨t, t', h2, hk⟩, Subtype.ext hy⟩
    · rcases h2 : C₂.1.2 (.inr t) with i | t'
      · fin_cases i
        · rw [← hy, glueP_photon_right, h2] at hb'
          simp [liftR] at hb'
        · have ht : t = w₂ := by
            have h' := congrArg C₂.1.2 h2
            rw [(C₂.2 _).1] at h'
            exact Sum.inr_injective (h'.trans hw)
          subst ht
          exact ⟨.inr (.inr ()), (eq_bridge C₁ C₂ hw hb (.inr hy.symm)).symm⟩
      · rw [← hy, glueP_photon_right' C₁ C₂ h2] at hb'
        rw [← hy, ← Sum.inr_injective hb', key_inr_lt_iff he] at hk
        exact ⟨.inr (.inl ⟨t, t', h2, hk⟩), Subtype.ext hy⟩

/-- **The photon lines of `glueP e C₁ C₂`** are those of the pieces and the bridge. -/
noncomputable def photonLinePEquiv {b : PhotonLine (glueP e C₁ C₂)}
    (hb : b.1 = psSplit κ e (.inl (extSlot C₁)) ∨ b.1 = psSplit κ e (.inr w₂)) :
    PhotonLine C₁ ⊕ PhotonLine C₂ ⊕ Unit ≃ PhotonLine (glueP e C₁ C₂) :=
  Equiv.ofBijective _ (photonLineP_bijective C₁ C₂ hw he hb)

/-! ### The line split of `glueP` -/

/-- Combining a split of the fermion lines with a split of the photon lines and a bridge. -/
def sumBridgeP {F₁ F₂ P₁ P₂ F P : Type*} (fE : F₁ ⊕ F₂ ≃ F) (pE : P₁ ⊕ P₂ ⊕ Unit ≃ P) :
    (F₁ ⊕ P₁) ⊕ (F₂ ⊕ P₂) ⊕ Unit ≃ F ⊕ P where
  toFun
    | .inl (.inl f) => .inl (fE (.inl f))
    | .inl (.inr g) => .inr (pE (.inl g))
    | .inr (.inl (.inl f)) => .inl (fE (.inr f))
    | .inr (.inl (.inr g)) => .inr (pE (.inr (.inl g)))
    | .inr (.inr u) => .inr (pE (.inr (.inr u)))
  invFun
    | .inl f => match fE.symm f with
      | .inl f => .inl (.inl f)
      | .inr f => .inr (.inl (.inl f))
    | .inr g => match pE.symm g with
      | .inl g => .inl (.inr g)
      | .inr (.inl g) => .inr (.inl (.inr g))
      | .inr (.inr u) => .inr (.inr u)
  left_inv := by
    rintro ((f | g) | (f | g) | u) <;> simp
  right_inv := by
    rintro (f | g)
    · rcases h : fE.symm f with f' | f' <;> simp only [h] <;> rw [← h, Equiv.apply_symm_apply]
    · rcases h : pE.symm g with g' | g' | u <;> simp only [h] <;>
        rw [← h, Equiv.apply_symm_apply]

/-- **The lines of `glueP e C₁ C₂`**: those of `C₁`, those of `C₂`, and the bridge `b`. -/
noncomputable def lineSplitP {b : PhotonLine (glueP e C₁ C₂)}
    (hb : b.1 = psSplit κ e (.inl (extSlot C₁)) ∨ b.1 = psSplit κ e (.inr w₂)) :
    LineSplit (glueP e C₁ C₂) C₁ C₂ b.1.1 b.head.1 where
  equiv := sumBridgeP (fermionLinePEquiv C₁ C₂) (photonLinePEquiv C₁ C₂ hw he hb)
  ends_left := by
    rintro (f | g)
    · simp only [sumBridgeP, Equiv.coe_fn_mk, Line.ends, fermionLinePEquiv,
        Equiv.ofBijective_apply, fermionLineP_left_tail]
      rfl
    · simp only [sumBridgeP, Equiv.coe_fn_mk, Line.ends, photonLinePEquiv,
        Equiv.ofBijective_apply, photonLineP]
      rw [head_eq _ (glueP_photon_left e C₁ C₂ (ne_extSlot C₁ g) (apply_inr_photonLine g))]
      rfl
  ends_right := by
    rintro (f | g)
    · simp only [sumBridgeP, Equiv.coe_fn_mk, Line.ends, fermionLinePEquiv,
        Equiv.ofBijective_apply, fermionLineP_right_tail]
      rfl
    · simp only [sumBridgeP, Equiv.coe_fn_mk, Line.ends, photonLinePEquiv,
        Equiv.ofBijective_apply, photonLineP]
      rw [head_eq _ (glueP_photon_right' C₁ C₂ (apply_inr_photonLine g))]
      rfl
  ends_bridge := rfl

end QED.GradedProof.X1C

end
