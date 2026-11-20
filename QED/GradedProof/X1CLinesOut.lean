/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CLinesIn

/-!
# (X₁) piece C: the lines of a self-energy glued onto the outgoing leg

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C2; the mirror of `QED/GradedProof/X1CLinesIn.lean`. For a shuffle
`e`, the internal lines of `glueOut e C₁ C₂` are those of `C₁`, those of `C₂`, and the bridge: the
fermion line from the vertex `a` of `C₁` contracted with its outgoing external to the vertex `c`
of `C₂` contracted with its incoming external.

* `fermionLineOut`: the fermion lines of `glueOut e C₁ C₂` are those of the pieces and the bridge.
* `lineSplitOut`: the `LineSplit` of `glueOut e C₁ C₂`, with the bridge from `a` to `c`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line FermionLine PhotonLine)
open QED.TwoLoop.Enumeration (tail_eq head_eq)

variable {N N₁ N₂ nA : ℕ} {κ : Fin N → Wick.VertexKind} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}

/-! ### The fermion lines of `glueOut` -/

section FermionOut

variable (C₁ : Contraction 1 nA (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e))
  {a : Wick.FermionVertex (leftKinds κ e)} {c : Wick.FermionVertex (rightKinds κ e)}
  (ha : C₁.1.1 (.inl 0) = .inr a) (hc : C₂.1.1 (.inr c) = .inl 0)

theorem glueOut_bridge (ha : C₁.1.1 (.inl 0) = .inr a) (hc : C₂.1.1 (.inr c) = .inl 0) :
    (glueOut e C₁ C₂).1.1 (.inr (fvSplit κ e (.inr c))) = .inr (fvSplit κ e (.inl a)) := by
  rw [← fR_inr_inr, glueOut_right_ext C₁ C₂ hc, ha]
  rfl

theorem glueOut_left' {t s : Wick.FermionVertex (leftKinds κ e)}
    (h : C₁.1.1 (.inr t) = .inr s) :
    (glueOut e C₁ C₂).1.1 (.inr (fvSplit κ e (.inl t))) = .inr (fvSplit κ e (.inl s)) := by
  rw [glueOut_left, h]
  rfl

theorem glueOut_right' {t s : Wick.FermionVertex (rightKinds κ e)}
    (h : C₂.1.1 (.inr t) = .inr s) :
    (glueOut e C₁ C₂).1.1 (.inr (fvSplit κ e (.inr t))) = .inr (fvSplit κ e (.inr s)) := by
  rw [← fR_inr_inr, glueOut_right C₁ C₂ h]

include ha hc in
/-- The fermion lines of the pieces and the bridge, as fermion lines of `glueOut e C₁ C₂`. -/
def fermionLineOut : FermionLine C₁ ⊕ FermionLine C₂ ⊕ Unit → FermionLine (glueOut e C₁ C₂)
  | .inl f => ⟨fvSplit κ e (.inl f.1), by
      obtain ⟨s, hs⟩ := Sum.isRight_iff.mp f.2
      rw [glueOut_left' C₁ C₂ hs]; rfl⟩
  | .inr (.inl f) => ⟨fvSplit κ e (.inr f.1), by
      obtain ⟨s, hs⟩ := Sum.isRight_iff.mp f.2
      rw [glueOut_right' C₁ C₂ hs]; rfl⟩
  | .inr (.inr _) => ⟨fvSplit κ e (.inr c), by rw [glueOut_bridge C₁ C₂ ha hc]; rfl⟩

theorem fermionLineOut_bijective : Function.Bijective (fermionLineOut C₁ C₂ ha hc) := by
  constructor
  · have hne : ∀ f : FermionLine C₂, f.1 ≠ c := fun f hf => by
      have := f.2
      rw [hf, hc] at this
      exact absurd this (by simp)
    rintro (f | f | ⟨⟩) (f' | f' | ⟨⟩) h <;>
      have h' := congrArg (fun x : FermionLine (glueOut e C₁ C₂) => (fvSplit κ e).symm x.1) h <;>
      simp [fermionLineOut] at h'
    · exact congrArg Sum.inl (Subtype.ext (Subtype.ext h'))
    · exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext (Subtype.ext h'))
    · exact absurd (Subtype.ext h') (hne f)
    · exact absurd (Subtype.ext h'.symm) (hne f')
    · rfl
  · intro f
    obtain ⟨x, hx⟩ := (fvSplit κ e).surjective f.1
    rcases x with t | t
    · have hf := f.2
      rw [← hx, glueOut_left] at hf
      rcases h2 : C₁.1.1 (.inr t) with i | s
      · rw [h2] at hf
        exact absurd hf (by simp [fL])
      · exact ⟨.inl ⟨t, by rw [h2]; rfl⟩, Subtype.ext hx⟩
    · by_cases ht : (C₂.1.1 (.inr t)).isRight
      · exact ⟨.inr (.inl ⟨t, ht⟩), Subtype.ext hx⟩
      · obtain ⟨i, hi⟩ := Sum.isLeft_iff.mp (Sum.not_isRight.mp ht)
        have : t = c := by
          have h2 := hi.trans ((congrArg Sum.inl (Subsingleton.elim i 0)).trans hc.symm)
          exact Sum.inr_injective (C₂.1.1.injective h2)
        subst this
        exact ⟨.inr (.inr ()), Subtype.ext hx⟩

/-- **The fermion lines of `glueOut e C₁ C₂`** are those of the pieces and the bridge. -/
noncomputable def fermionLineOutEquiv :
    FermionLine C₁ ⊕ FermionLine C₂ ⊕ Unit ≃ FermionLine (glueOut e C₁ C₂) :=
  Equiv.ofBijective _ (fermionLineOut_bijective C₁ C₂ ha hc)

theorem fermionLineOut_left_tail (f : FermionLine C₁) :
    (fermionLineOut C₁ C₂ ha hc (.inl f)).tail = fvSplit κ e (.inl f.tail) := by
  obtain ⟨s, hs⟩ := Sum.isRight_iff.mp f.2
  rw [tail_eq _ (glueOut_left' C₁ C₂ hs), tail_eq _ hs]

theorem fermionLineOut_right_tail (f : FermionLine C₂) :
    (fermionLineOut C₁ C₂ ha hc (.inr (.inl f))).tail = fvSplit κ e (.inr f.tail) := by
  obtain ⟨s, hs⟩ := Sum.isRight_iff.mp f.2
  rw [tail_eq _ (glueOut_right' C₁ C₂ hs), tail_eq _ hs]

theorem fermionLineOut_bridge_tail :
    (fermionLineOut C₁ C₂ ha hc (.inr (.inr ()))).tail = fvSplit κ e (.inl a) :=
  tail_eq _ (glueOut_bridge C₁ C₂ ha hc)

end FermionOut

/-! ### The line split of `glueOut` -/

variable (C₁ : Contraction 1 nA (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e))
  {a : Wick.FermionVertex (leftKinds κ e)} {c : Wick.FermionVertex (rightKinds κ e)}
  (ha : C₁.1.1 (.inl 0) = .inr a) (hc : C₂.1.1 (.inr c) = .inl 0) (he : IsShuffle e)

/-- **The lines of `glueOut e C₁ C₂`**: those of `C₁`, those of `C₂`, and the bridge from the
vertex of `a` to the vertex of `c`. -/
noncomputable def lineSplitOut :
    LineSplit (glueOut e C₁ C₂) C₁ C₂ (e (.inl a.1)) (e (.inr c.1)) where
  equiv := sumBridgeF (fermionLineOutEquiv C₁ C₂ ha hc) (photonLineSplit
    (C := glueOut e C₁ C₂) (C₁ := C₁) (C₂ := C₂) rfl he)
  ends_left := by
    rintro (f | g)
    · simp only [sumBridgeF, Equiv.coe_fn_mk, Line.ends, fermionLineOutEquiv,
        Equiv.ofBijective_apply, fermionLineOut_left_tail]
      rfl
    · have h := photonLineMap_left (C := glueOut e C₁ C₂) (C₁ := C₁) (C₂ := C₂) rfl he g
      simp only [sumBridgeF, Equiv.coe_fn_mk, Line.ends]
      exact Prod.ext (congrArg Sigma.fst h.1) (congrArg Sigma.fst h.2)
  ends_right := by
    rintro (f | g)
    · simp only [sumBridgeF, Equiv.coe_fn_mk, Line.ends, fermionLineOutEquiv,
        Equiv.ofBijective_apply, fermionLineOut_right_tail]
      rfl
    · have h := photonLineMap_right (C := glueOut e C₁ C₂) (C₁ := C₁) (C₂ := C₂) rfl he g
      simp only [sumBridgeF, Equiv.coe_fn_mk, Line.ends]
      exact Prod.ext (congrArg Sigma.fst h.1) (congrArg Sigma.fst h.2)
  ends_bridge := by
    simp only [sumBridgeF, Equiv.coe_fn_mk, Line.ends, fermionLineOutEquiv,
      Equiv.ofBijective_apply, fermionLineOut_bridge_tail]
    rfl

end QED.GradedProof.X1C

end
