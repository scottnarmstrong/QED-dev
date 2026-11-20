/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CGlueF
public import QED.GradedProof.X1CSplitRoute
public import QED.TwoLoop.EnumerationRelabel
public import QED.TwoLoop.ChordLoopLine

/-!
# (X₁) piece C: the lines of a self-energy glued onto the incoming leg

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C2. For a split `e` that is increasing on each piece (a shuffle),
the internal lines of `glueIn e C₁ C₂` are those of `C₁`, those of `C₂`, and the bridge: the
fermion line from the vertex `c` of `C₂` contracted with its outgoing external to the vertex `a`
of `C₁` contracted with its incoming external.

* `key_lt_iff`: an increasing map of the vertices keeps the order of the photon keys (V₈), so a
  photon line of a piece keeps its orientation.
* `photonLineSplit`: the photon lines of a contraction with the photon pairing `gluePhotons` (the
  two leg gluings) are those of the pieces.
* `fermionLineIn`: the fermion lines of `glueIn e C₁ C₂` are those of the pieces and the bridge.
* `lineSplitIn`: the `LineSplit` of `glueIn e C₁ C₂`, with the bridge from `c` to `a`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line FermionLine PhotonLine)
open QED.TwoLoop.Enumeration (tail_eq head_eq)
open QED.TwoLoop.LoopBound (apply_inr_photonLine photonKey_lt_head)

/-! ### Photon keys under increasing maps -/

theorem key_lt_iff_of_strictMono {M N : ℕ} {f : Fin M → Fin N} (hf : StrictMono f)
    (x y : Fin M) {i j : ℕ} (hi : i < 2) (hj : j < 2) :
    2 * (f x).val + i < 2 * (f y).val + j ↔ 2 * x.val + i < 2 * y.val + j := by
  rcases lt_trichotomy x y with h | rfl | h
  · have h' := hf h
    rw [Fin.lt_def] at h h'
    constructor <;> intro <;> omega
  · constructor <;> intro <;> omega
  · have h' := hf h
    rw [Fin.lt_def] at h h'
    constructor <;> intro <;> omega

variable {N N₁ N₂ nA : ℕ} {κ : Fin N → Wick.VertexKind} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}

/-- The split `e` is increasing on each piece. -/
structure IsShuffle (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N) : Prop where
  left : StrictMono fun t => e (.inl t)
  right : StrictMono fun t => e (.inr t)

theorem key_inl_lt_iff (he : IsShuffle e) (a b : Wick.PhotonSlot (leftKinds κ e)) :
    Wick.photonKey (psSplit κ e (.inl a)) < Wick.photonKey (psSplit κ e (.inl b)) ↔
      Wick.photonKey a < Wick.photonKey b :=
  key_lt_iff_of_strictMono he.left a.1 b.1
    (lt_of_lt_of_le a.2.2 (QED.TwoLoop.Chord.photonSlots_le_two _))
    (lt_of_lt_of_le b.2.2 (QED.TwoLoop.Chord.photonSlots_le_two _))

theorem key_inr_lt_iff (he : IsShuffle e) (a b : Wick.PhotonSlot (rightKinds κ e)) :
    Wick.photonKey (psSplit κ e (.inr a)) < Wick.photonKey (psSplit κ e (.inr b)) ↔
      Wick.photonKey a < Wick.photonKey b :=
  key_lt_iff_of_strictMono he.right a.1 b.1
    (lt_of_lt_of_le a.2.2 (QED.TwoLoop.Chord.photonSlots_le_two _))
    (lt_of_lt_of_le b.2.2 (QED.TwoLoop.Chord.photonSlots_le_two _))

/-! ### The photon lines of a leg gluing -/

section Photon

variable {nf₁ nf₂ nf : ℕ} {C₁ : Contraction nf₁ nA (leftKinds κ e)}
  {C₂ : Contraction nf₂ 0 (rightKinds κ e)} {C : Contraction nf nA κ}
  (hC : C.1.2 = dsum (pL κ e nA) C₁.1.2 C₂.1.2)

include hC

theorem photon_left (a : Wick.PhotonSlot (leftKinds κ e)) :
    C.1.2 (.inr (psSplit κ e (.inl a))) = pL κ e nA (.inl (C₁.1.2 (.inr a))) := by
  rw [hC]
  exact dsum_apply_inl (pL κ e nA) C₁.1.2 C₂.1.2 (.inr a)

theorem photon_right (a : Wick.PhotonSlot (rightKinds κ e)) :
    C.1.2 (.inr (psSplit κ e (.inr a))) = pL κ e nA (.inr (C₂.1.2 (.inr a))) := by
  rw [hC]
  exact dsum_apply_inr (pL κ e nA) C₁.1.2 C₂.1.2 (.inr a)

variable (he : IsShuffle e)

theorem photon_left_line (g : PhotonLine C₁) :
    C.1.2 (.inr (psSplit κ e (.inl g.1))) = .inr (psSplit κ e (.inl g.head)) := by
  rw [photon_left hC, apply_inr_photonLine, pL_inl_inr]

theorem photon_right_line (g : PhotonLine C₂) :
    C.1.2 (.inr (psSplit κ e (.inr g.1))) = .inr (psSplit κ e (.inr g.head)) := by
  rw [photon_right hC, apply_inr_photonLine, pL_inr_inr]

/-- The photon lines of the pieces, as photon lines of `C`. -/
def photonLineMap : PhotonLine C₁ ⊕ PhotonLine C₂ → PhotonLine C
  | .inl g => ⟨psSplit κ e (.inl g.1), ⟨psSplit κ e (.inl g.head), photon_left_line hC g,
      (key_inl_lt_iff he _ _).2 (photonKey_lt_head g)⟩⟩
  | .inr g => ⟨psSplit κ e (.inr g.1), ⟨psSplit κ e (.inr g.head), photon_right_line hC g,
      (key_inr_lt_iff he _ _).2 (photonKey_lt_head g)⟩⟩

theorem photonLineMap_left (g : PhotonLine C₁) :
    (photonLineMap hC he (.inl g)).1 = psSplit κ e (.inl g.1) ∧
      (photonLineMap hC he (.inl g)).head = psSplit κ e (.inl g.head) :=
  ⟨rfl, head_eq _ (photon_left_line hC g)⟩

theorem photonLineMap_right (g : PhotonLine C₂) :
    (photonLineMap hC he (.inr g)).1 = psSplit κ e (.inr g.1) ∧
      (photonLineMap hC he (.inr g)).head = psSplit κ e (.inr g.head) :=
  ⟨rfl, head_eq _ (photon_right_line hC g)⟩

theorem photonLineMap_bijective : Function.Bijective (photonLineMap hC he) := by
  constructor
  · rintro (g | g) (g' | g') h <;>
      have h' := congrArg (fun x : PhotonLine C => (psSplit κ e).symm x.1) h <;>
      simp [photonLineMap] at h'
    · exact congrArg Sum.inl (Subtype.ext (Sigma.ext h'.1 h'.2))
    · exact congrArg Sum.inr (Subtype.ext (Sigma.ext h'.1 h'.2))
  · intro s
    obtain ⟨b, hb, hk⟩ := s.2
    obtain ⟨x, hx⟩ := (psSplit κ e).surjective s.1
    rcases x with a | a
    · have h1 := photon_left hC a
      rw [hx, hb] at h1
      rcases h2 : C₁.1.2 (.inr a) with j | a'
      · rw [h2] at h1
        exact absurd h1 (by simp)
      · rw [h2] at h1
        have hb' : b = psSplit κ e (.inl a') := Sum.inr_injective h1
        rw [← hx, hb', key_inl_lt_iff he] at hk
        exact ⟨.inl ⟨a, a', h2, hk⟩, Subtype.ext hx⟩
    · have h1 := photon_right hC a
      rw [hx, hb] at h1
      rcases h2 : C₂.1.2 (.inr a) with j | a'
      · exact j.elim0
      · rw [h2] at h1
        have hb' : b = psSplit κ e (.inr a') := Sum.inr_injective h1
        rw [← hx, hb', key_inr_lt_iff he] at hk
        exact ⟨.inr ⟨a, a', h2, hk⟩, Subtype.ext hx⟩

/-- **The photon lines of a leg gluing** are those of the pieces. -/
noncomputable def photonLineSplit : PhotonLine C₁ ⊕ PhotonLine C₂ ≃ PhotonLine C :=
  Equiv.ofBijective _ (photonLineMap_bijective hC he)

theorem photonLineSplit_apply (x : PhotonLine C₁ ⊕ PhotonLine C₂) :
    photonLineSplit hC he x = photonLineMap hC he x := rfl

end Photon

/-! ### The fermion lines of `glueIn` -/

section FermionIn

variable (C₁ : Contraction 1 nA (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e))
  {a : Wick.FermionVertex (leftKinds κ e)} {c : Wick.FermionVertex (rightKinds κ e)}
  (ha : C₁.1.1 (.inr a) = .inl 0) (hc : C₂.1.1 (.inl 0) = .inr c)

theorem glueIn_bridge (ha : C₁.1.1 (.inr a) = .inl 0) (hc : C₂.1.1 (.inl 0) = .inr c) :
    (glueIn e C₁ C₂).1.1 (.inr (fvSplit κ e (.inl a))) = .inr (fvSplit κ e (.inr c)) := by
  rw [← fL_inl_inr, glueIn_left_ext C₁ C₂ ha, hc]
  rfl

theorem glueIn_left' {t s : Wick.FermionVertex (leftKinds κ e)} (h : C₁.1.1 (.inr t) = .inr s) :
    (glueIn e C₁ C₂).1.1 (.inr (fvSplit κ e (.inl t))) = .inr (fvSplit κ e (.inl s)) := by
  rw [← fL_inl_inr, glueIn_left C₁ C₂ h]

theorem glueIn_right' {t s : Wick.FermionVertex (rightKinds κ e)} (h : C₂.1.1 (.inr t) = .inr s) :
    (glueIn e C₁ C₂).1.1 (.inr (fvSplit κ e (.inr t))) = .inr (fvSplit κ e (.inr s)) := by
  rw [glueIn_right, h]
  rfl

include ha hc in
/-- The fermion lines of the pieces and the bridge, as fermion lines of `glueIn e C₁ C₂`. -/
def fermionLineIn : FermionLine C₁ ⊕ FermionLine C₂ ⊕ Unit → FermionLine (glueIn e C₁ C₂)
  | .inl f => ⟨fvSplit κ e (.inl f.1), by
      obtain ⟨s, hs⟩ := Sum.isRight_iff.mp f.2
      rw [glueIn_left' C₁ C₂ hs]; rfl⟩
  | .inr (.inl f) => ⟨fvSplit κ e (.inr f.1), by
      obtain ⟨s, hs⟩ := Sum.isRight_iff.mp f.2
      rw [glueIn_right' C₁ C₂ hs]; rfl⟩
  | .inr (.inr _) => ⟨fvSplit κ e (.inl a), by rw [glueIn_bridge C₁ C₂ ha hc]; rfl⟩

theorem fermionLineIn_bijective : Function.Bijective (fermionLineIn C₁ C₂ ha hc) := by
  constructor
  · have hne : ∀ f : FermionLine C₁, f.1 ≠ a := fun f hf => by
      have := f.2
      rw [hf, ha] at this
      exact absurd this (by simp)
    rintro (f | f | ⟨⟩) (f' | f' | ⟨⟩) h <;>
      have h' := congrArg (fun x : FermionLine (glueIn e C₁ C₂) => (fvSplit κ e).symm x.1) h <;>
      simp [fermionLineIn] at h'
    · exact congrArg Sum.inl (Subtype.ext (Subtype.ext h'))
    · exact absurd (Subtype.ext h') (hne f)
    · exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext (Subtype.ext h'))
    · exact absurd (Subtype.ext h'.symm) (hne f')
    · rfl
  · intro f
    obtain ⟨x, hx⟩ := (fvSplit κ e).surjective f.1
    rcases x with t | t
    · by_cases ht : (C₁.1.1 (.inr t)).isRight
      · exact ⟨.inl ⟨t, ht⟩, Subtype.ext hx⟩
      · obtain ⟨i, hi⟩ := Sum.isLeft_iff.mp (Sum.not_isRight.mp ht)
        have : t = a := by
          have h2 := hi.trans ((congrArg Sum.inl (Subsingleton.elim i 0)).trans ha.symm)
          exact Sum.inr_injective (C₁.1.1.injective h2)
        subst this
        exact ⟨.inr (.inr ()), Subtype.ext hx⟩
    · have hf := f.2
      rw [← hx, glueIn_right] at hf
      rcases h2 : C₂.1.1 (.inr t) with i | s
      · rw [h2] at hf
        exact absurd hf (by simp [fR])
      · exact ⟨.inr (.inl ⟨t, by rw [h2]; rfl⟩), Subtype.ext hx⟩

/-- **The fermion lines of `glueIn e C₁ C₂`** are those of the pieces and the bridge. -/
noncomputable def fermionLineInEquiv :
    FermionLine C₁ ⊕ FermionLine C₂ ⊕ Unit ≃ FermionLine (glueIn e C₁ C₂) :=
  Equiv.ofBijective _ (fermionLineIn_bijective C₁ C₂ ha hc)

theorem fermionLineIn_left_tail (f : FermionLine C₁) :
    (fermionLineIn C₁ C₂ ha hc (.inl f)).tail = fvSplit κ e (.inl f.tail) := by
  obtain ⟨s, hs⟩ := Sum.isRight_iff.mp f.2
  rw [tail_eq _ (glueIn_left' C₁ C₂ hs), tail_eq _ hs]

theorem fermionLineIn_right_tail (f : FermionLine C₂) :
    (fermionLineIn C₁ C₂ ha hc (.inr (.inl f))).tail = fvSplit κ e (.inr f.tail) := by
  obtain ⟨s, hs⟩ := Sum.isRight_iff.mp f.2
  rw [tail_eq _ (glueIn_right' C₁ C₂ hs), tail_eq _ hs]

theorem fermionLineIn_bridge_tail :
    (fermionLineIn C₁ C₂ ha hc (.inr (.inr ()))).tail = fvSplit κ e (.inr c) :=
  tail_eq _ (glueIn_bridge C₁ C₂ ha hc)

end FermionIn

/-! ### The line split of `glueIn` -/

/-- Combining a split of the fermion lines with a bridge and a split of the photon lines. -/
def sumBridgeF {F₁ F₂ P₁ P₂ F P : Type*} (fE : F₁ ⊕ F₂ ⊕ Unit ≃ F) (pE : P₁ ⊕ P₂ ≃ P) :
    (F₁ ⊕ P₁) ⊕ (F₂ ⊕ P₂) ⊕ Unit ≃ F ⊕ P where
  toFun
    | .inl (.inl f) => .inl (fE (.inl f))
    | .inl (.inr g) => .inr (pE (.inl g))
    | .inr (.inl (.inl f)) => .inl (fE (.inr (.inl f)))
    | .inr (.inl (.inr g)) => .inr (pE (.inr g))
    | .inr (.inr u) => .inl (fE (.inr (.inr u)))
  invFun
    | .inl f => match fE.symm f with
      | .inl f => .inl (.inl f)
      | .inr (.inl f) => .inr (.inl (.inl f))
      | .inr (.inr u) => .inr (.inr u)
    | .inr g => match pE.symm g with
      | .inl g => .inl (.inr g)
      | .inr g => .inr (.inl (.inr g))
  left_inv := by
    rintro ((f | g) | (f | g) | u) <;> simp
  right_inv := by
    rintro (f | g)
    · rcases h : fE.symm f with f' | f' | u <;> simp only [h] <;> rw [← h, Equiv.apply_symm_apply]
    · rcases h : pE.symm g with g' | g' <;> simp only [h] <;> rw [← h, Equiv.apply_symm_apply]

variable (C₁ : Contraction 1 nA (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e))
  {a : Wick.FermionVertex (leftKinds κ e)} {c : Wick.FermionVertex (rightKinds κ e)}
  (ha : C₁.1.1 (.inr a) = .inl 0) (hc : C₂.1.1 (.inl 0) = .inr c) (he : IsShuffle e)

/-- **The lines of `glueIn e C₁ C₂`**: those of `C₁`, those of `C₂`, and the bridge from the
vertex of `c` to the vertex of `a`. -/
noncomputable def lineSplitIn :
    LineSplit (glueIn e C₁ C₂) C₁ C₂ (e (.inr c.1)) (e (.inl a.1)) where
  equiv := sumBridgeF (fermionLineInEquiv C₁ C₂ ha hc) (photonLineSplit (C := glueIn e C₁ C₂)
    (C₁ := C₁) (C₂ := C₂) rfl he)
  ends_left := by
    rintro (f | g)
    · simp only [sumBridgeF, Equiv.coe_fn_mk, Line.ends, fermionLineInEquiv,
        Equiv.ofBijective_apply, fermionLineIn_left_tail]
      rfl
    · have h := photonLineMap_left (C := glueIn e C₁ C₂) (C₁ := C₁) (C₂ := C₂) rfl he g
      simp only [sumBridgeF, Equiv.coe_fn_mk, Line.ends]
      exact Prod.ext (congrArg Sigma.fst h.1) (congrArg Sigma.fst h.2)
  ends_right := by
    rintro (f | g)
    · simp only [sumBridgeF, Equiv.coe_fn_mk, Line.ends, fermionLineInEquiv,
        Equiv.ofBijective_apply, fermionLineIn_right_tail]
      rfl
    · have h := photonLineMap_right (C := glueIn e C₁ C₂) (C₁ := C₁) (C₂ := C₂) rfl he g
      simp only [sumBridgeF, Equiv.coe_fn_mk, Line.ends]
      exact Prod.ext (congrArg Sigma.fst h.1) (congrArg Sigma.fst h.2)
  ends_bridge := by
    simp only [sumBridgeF, Equiv.coe_fn_mk, Line.ends, fermionLineInEquiv,
      Equiv.ofBijective_apply, fermionLineIn_bridge_tail]
    rfl

end QED.GradedProof.X1C

end
