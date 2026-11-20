/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CPeelDefs

/-!
# (X₁) piece C: cutting a contraction at an in-leg cut

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (the graph theory of the in-leg peel). Let `f` be a fermion line
of `C` and `T` a set of vertices such that every other line has both ends in `T` or both out of
`T`, the tail of `f` is in `T` and its head is not, the in-vertex is in `T` and the out-vertex
and the photon externals are not (`PeelCutData`, for a split `e` with right image `T`). Then the
restrictions `PeelCutData.peelC₁` (vertices out of `T`, the field `Ψ` of the head of `f` contracted
with the incoming external) and `PeelCutData.peelC₂` (vertices in `T`, the outgoing external
contracted with the `Ψ̄` of the tail of `f`) glue back to `C`: **`PeelCutData.glueIn_peelC`**.
**`peel_exists_glueIn`**: such a split, increasing on each piece, exists for every such `T`.

The pairings of the pieces are read off from those of `C` (`peelσ₁fun`, `peelσ₂fun`,
`peelτ₁fun`, `peelτ₂fun`): every field of a piece is contracted, in `C`, with a field of the same
piece (`PeelCutData.peel_left_field`, `peel_right_field`, `peel_photon_left`,
`peel_photon_right`), except the two fields of `f`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line FermionLine PhotonLine Joined IsBridge)
open QED.TwoLoop.Enumeration (tail_eq)
open Relation Finset

variable {nA N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind}

/-- **The data of a cut** of `C` at the fermion line `f` with tail side `T`, the right image of
`e`. -/
structure PeelCutData (C : Contraction 1 nA κ) (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N)
    (f : FermionLine C) (T : Fin N → Prop) : Prop where
  lines : ∀ l : Line C, l ≠ .inl f → (T l.ends.1 ↔ T l.ends.2)
  tail : T f.tail.1
  head : ¬ T f.1.1
  inV : ∀ y, C.1.1 (.inr y) = .inl 0 → T y.1
  out : ∀ x, C.1.1 (.inl 0) = .inr x → ¬ T x.1
  photon : ∀ j a, C.1.2 (.inl j) = .inr a → ¬ T a.1
  attached : ∀ i, C.1.1 (.inl 0) ≠ .inl i
  left : ∀ s, ¬ T (e (.inl s))
  right : ∀ r, T (e (.inr r))

/-! ### Decoding fields -/

section Dec

variable {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}

/-- A fermion field of `κ` as a field of the left piece (the right vertices to the external). -/
def peelDecL (w : Fin 1 ⊕ Wick.FermionVertex κ) : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e) :=
  Sum.elim id (fun _ => .inl 0) ((fL κ e 1).symm w)

/-- A fermion field of `κ` as a field of the right piece (the left vertices to the external). -/
def peelDecR (w : Fin 1 ⊕ Wick.FermionVertex κ) :
    Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e) :=
  Sum.elim (fun _ => .inl 0) id ((fR κ e 1).symm w)

theorem peelDecL_fL_inl (z : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)) :
    peelDecL (e := e) (fL κ e 1 (.inl z)) = z := by
  simp [peelDecL]

theorem peelDecL_fL_inr (q : Fin 0 ⊕ Wick.FermionVertex (rightKinds κ e)) :
    peelDecL (e := e) (fL κ e 1 (.inr q)) = .inl 0 := by
  simp [peelDecL]

theorem peelDecR_fR_inr (z : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e)) :
    peelDecR (e := e) (fR κ e 1 (.inr z)) = z := by
  simp [peelDecR]

end Dec

variable (C : Contraction 1 nA κ) (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N) (f : FermionLine C)

/-- The fermion pairing of the left piece. -/
def peelσ₁fun (z : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)) :
    Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e) :=
  peelDecL (C.1.1 (fL κ e 1 (.inl z)))

/-- The fermion pairing of the right piece. -/
def peelσ₂fun (z : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e)) :
    Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e) :=
  Sum.elim (fun _ => peelDecR (C.1.1 (.inr f.1)))
    (fun r => peelDecR (C.1.1 (.inr (fvSplit κ e (.inr r))))) z

/-- The photon pairing of the left piece. -/
def peelτ₁fun (z : Fin nA ⊕ Wick.PhotonSlot (leftKinds κ e)) :
    Fin nA ⊕ Wick.PhotonSlot (leftKinds κ e) :=
  Sum.elim id (fun _ => z) ((pL κ e nA).symm (C.1.2 (pL κ e nA (.inl z))))

/-- The photon pairing of the right piece. -/
def peelτ₂fun (z : Fin 0 ⊕ Wick.PhotonSlot (rightKinds κ e)) :
    Fin 0 ⊕ Wick.PhotonSlot (rightKinds κ e) :=
  Sum.elim (fun _ => z) id ((pL κ e nA).symm (C.1.2 (pL κ e nA (.inr z))))

variable {C e f}

theorem peelσ₁fun_eq {z : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)}
    {t : Wick.FermionVertex (leftKinds κ e)}
    (h : C.1.1 (fL κ e 1 (.inl z)) = .inr (fvSplit κ e (.inl t))) : peelσ₁fun C e z = .inr t := by
  rw [peelσ₁fun, h, ← fL_inl_inr, peelDecL_fL_inl]

theorem peelσ₂fun_inr {r : Wick.FermionVertex (rightKinds κ e)}
    {z : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e)}
    (h : C.1.1 (.inr (fvSplit κ e (.inr r))) = fR κ e 1 (.inr z)) :
    peelσ₂fun C e f (.inr r) = z := by
  rw [peelσ₂fun, Sum.elim_inr, h, peelDecR_fR_inr]

theorem peelτ₁fun_eq {z z' : Fin nA ⊕ Wick.PhotonSlot (leftKinds κ e)}
    (h : C.1.2 (pL κ e nA (.inl z)) = pL κ e nA (.inl z')) : peelτ₁fun C e z = z' := by
  simp [peelτ₁fun, h]

theorem peelτ₂fun_eq {z z' : Fin 0 ⊕ Wick.PhotonSlot (rightKinds κ e)}
    (h : C.1.2 (pL κ e nA (.inr z)) = pL κ e nA (.inr z')) : peelτ₂fun C e z = z' := by
  simp [peelτ₂fun, h]

namespace PeelCutData

variable {T : Fin N → Prop} (H : PeelCutData C e f T)
include H

theorem peel_fv_left {t : Wick.FermionVertex κ} (ht : ¬ T t.1) : ∃ s, t = fvSplit κ e (.inl s) := by
  obtain ⟨x, rfl⟩ := (fvSplit κ e).surjective t
  rcases x with s | r
  · exact ⟨s, rfl⟩
  · exact absurd (H.right r.1) ht

theorem peel_fv_right {t : Wick.FermionVertex κ} (ht : T t.1) : ∃ r, t = fvSplit κ e (.inr r) := by
  obtain ⟨x, rfl⟩ := (fvSplit κ e).surjective t
  rcases x with s | r
  · exact absurd ht (H.left s.1)
  · exact ⟨r, rfl⟩

theorem peel_ps_left {a : Wick.PhotonSlot κ} (ha : ¬ T a.1) : ∃ s, a = psSplit κ e (.inl s) := by
  obtain ⟨x, rfl⟩ := (psSplit κ e).surjective a
  rcases x with s | r
  · exact ⟨s, rfl⟩
  · exact absurd (H.right r.1) ha

theorem peel_ps_right {a : Wick.PhotonSlot κ} (ha : T a.1) : ∃ r, a = psSplit κ e (.inr r) := by
  obtain ⟨x, rfl⟩ := (psSplit κ e).surjective a
  rcases x with s | r
  · exact absurd ha (H.left s.1)
  · exact ⟨r, rfl⟩

/-- The ends of a fermion line other than `f` are on the same side. -/
theorem peel_fermion_cross {v t : Wick.FermionVertex κ} (h : C.1.1 (.inr v) = .inr t)
    (hv : v ≠ f.1) : T t.1 ↔ T v.1 := by
  have := H.lines (.inl (peelFLine h))
    (fun hl => hv (congrArg Subtype.val (Sum.inl_injective hl)))
  simp only [Line.ends] at this
  rw [show (peelFLine h).tail = t from tail_eq _ h] at this
  exact this

/-- The ends of a photon line are on the same side. -/
theorem peel_photon_pair {a b : Wick.PhotonSlot κ} (h : C.1.2 (.inr a) = .inr b) :
    T a.1 ↔ T b.1 := by
  obtain ⟨l, hl⟩ := tadSide_photon_pair h
  have := H.lines (.inr l) Sum.inr_ne_inl
  simp only [Line.ends] at this
  rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at this
  · exact this
  · exact this.symm

theorem peel_tail_right : ∃ c, f.tail = fvSplit κ e (.inr c) := H.peel_fv_right H.tail

theorem peel_head_left : ∃ a, f.1 = fvSplit κ e (.inl a) := H.peel_fv_left H.head

/-- A field of the left piece is the field of `f` or is contracted with the left piece. -/
theorem peel_left_field (z : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)) :
    fL κ e 1 (.inl z) = .inr f.1 ∨
      ∃ t, C.1.1 (fL κ e 1 (.inl z)) = .inr (fvSplit κ e (.inl t)) := by
  rcases z with i | s
  · right
    rw [Subsingleton.elim i 0, fL_inl_inl]
    rcases h : C.1.1 (.inl 0) with j | x
    · exact absurd h (H.attached j)
    · obtain ⟨t, rfl⟩ := H.peel_fv_left (H.out x h)
      exact ⟨t, rfl⟩
  · rw [fL_inl_inr]
    have hv : ¬ T (fvSplit κ e (.inl s)).1 := H.left s.1
    rcases h : C.1.1 (.inr (fvSplit κ e (.inl s))) with j | t
    · exact absurd (H.inV _ (by rw [h, Subsingleton.elim j 0])) hv
    · by_cases hvf : fvSplit κ e (.inl s) = f.1
      · exact .inl (by rw [hvf])
      · obtain ⟨t', rfl⟩ := H.peel_fv_left fun ht => hv ((H.peel_fermion_cross h hvf).1 ht)
        exact .inr ⟨t', rfl⟩

/-- A vertex field of the right piece is contracted with the right piece or the external. -/
theorem peel_right_field (r : Wick.FermionVertex (rightKinds κ e)) :
    ∃ z, C.1.1 (.inr (fvSplit κ e (.inr r))) = fR κ e 1 (.inr z) := by
  have hv : T (fvSplit κ e (.inr r)).1 := H.right r.1
  rcases h : C.1.1 (.inr (fvSplit κ e (.inr r))) with j | t
  · exact ⟨.inl j, rfl⟩
  · have hvf : fvSplit κ e (.inr r) ≠ f.1 := fun hvf => H.head (hvf ▸ hv)
    obtain ⟨t', rfl⟩ := H.peel_fv_right ((H.peel_fermion_cross h hvf).2 hv)
    exact ⟨.inr t', rfl⟩

theorem peel_photon_left (z : Fin nA ⊕ Wick.PhotonSlot (leftKinds κ e)) :
    ∃ z', C.1.2 (pL κ e nA (.inl z)) = pL κ e nA (.inl z') := by
  rcases z with j | s
  · rw [pL_inl_inl]
    rcases h : C.1.2 (.inl j) with j' | b
    · exact ⟨.inl j', rfl⟩
    · obtain ⟨b', rfl⟩ := H.peel_ps_left (H.photon j b h)
      exact ⟨.inr b', rfl⟩
  · rw [pL_inl_inr]
    rcases h : C.1.2 (.inr (psSplit κ e (.inl s))) with j' | b
    · exact ⟨.inl j', rfl⟩
    · obtain ⟨b', rfl⟩ := H.peel_ps_left fun hb => H.left s.1 ((H.peel_photon_pair h).2 hb)
      exact ⟨.inr b', rfl⟩

theorem peel_photon_right (z : Fin 0 ⊕ Wick.PhotonSlot (rightKinds κ e)) :
    ∃ z', C.1.2 (pL κ e nA (.inr z)) = pL κ e nA (.inr z') := by
  rcases z with i | s
  · exact i.elim0
  · rw [pL_inr_inr]
    rcases h : C.1.2 (.inr (psSplit κ e (.inr s))) with j | b
    · have h' : C.1.2 (.inl j) = .inr (psSplit κ e (.inr s)) := by rw [← h, (C.2 _).1]
      exact absurd (H.right s.1) (H.photon j _ h')
    · obtain ⟨b', rfl⟩ := H.peel_ps_right ((H.peel_photon_pair h).1 (H.right s.1))
      exact ⟨.inr b', rfl⟩

/-! ### The pairings of the pieces -/

theorem peelσ₁fun_cross {z : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)}
    (hz : fL κ e 1 (.inl z) = .inr f.1) : peelσ₁fun C e z = .inl 0 := by
  obtain ⟨c, hc⟩ := H.peel_tail_right
  rw [peelσ₁fun, hz, peel_fermion_tail, hc, ← fL_inr_inr, peelDecL_fL_inr]

omit H in
theorem peelσ₂fun_inl {c : Wick.FermionVertex (rightKinds κ e)}
    (hc : f.tail = fvSplit κ e (.inr c)) (i : Fin 1) : peelσ₂fun C e f (.inl i) = .inr c := by
  rw [peelσ₂fun, Sum.elim_inl, peel_fermion_tail, hc, ← fR_inr_inr, peelDecR_fR_inr]

theorem peelσ₁fun_injective : Function.Injective (peelσ₁fun C e) := by
  intro z z' h
  rcases H.peel_left_field z with hz | ⟨t, ht⟩ <;> rcases H.peel_left_field z' with hz' | ⟨t', ht'⟩
  · exact Sum.inl_injective ((fL κ e 1).injective (hz.trans hz'.symm))
  · rw [H.peelσ₁fun_cross hz, peelσ₁fun_eq ht'] at h
    exact absurd h Sum.inl_ne_inr
  · rw [peelσ₁fun_eq ht, H.peelσ₁fun_cross hz'] at h
    exact absurd h Sum.inr_ne_inl
  · rw [peelσ₁fun_eq ht, peelσ₁fun_eq ht'] at h
    cases Sum.inr_injective h
    exact Sum.inl_injective ((fL κ e 1).injective (C.1.1.injective (ht.trans ht'.symm)))

theorem peelσ₂fun_injective : Function.Injective (peelσ₂fun C e f) := by
  obtain ⟨c, hc⟩ := H.peel_tail_right
  have key : ∀ r, peelσ₂fun C e f (.inr r) ≠ .inr c := by
    intro r h
    obtain ⟨z, hz⟩ := H.peel_right_field r
    rw [peelσ₂fun_inr hz] at h
    subst h
    have h1 : fvSplit κ e (.inr r) = f.1 := Sum.inr_injective (C.1.1.injective
      (hz.trans (by rw [fR_inr_inr, ← hc, peel_fermion_tail])))
    have h2 : T (fvSplit κ e (.inr r)).1 := H.right r.1
    rw [h1] at h2
    exact H.head h2
  rintro (i | r) (i' | r') h
  · rw [Subsingleton.elim i i']
  · rw [peelσ₂fun_inl hc] at h
    exact absurd h.symm (key r')
  · rw [peelσ₂fun_inl hc] at h
    exact absurd h (key r)
  · obtain ⟨z, hz⟩ := H.peel_right_field r
    obtain ⟨z', hz'⟩ := H.peel_right_field r'
    rw [peelσ₂fun_inr hz, peelσ₂fun_inr hz'] at h
    subst h
    have := C.1.1.injective (hz.trans hz'.symm)
    exact congrArg Sum.inr (Sum.inr_injective ((fvSplit κ e).injective (Sum.inr_injective this)))

theorem peelτ₁fun_invol (z : Fin nA ⊕ Wick.PhotonSlot (leftKinds κ e)) :
    peelτ₁fun C e (peelτ₁fun C e z) = z ∧ peelτ₁fun C e z ≠ z := by
  obtain ⟨z', hz'⟩ := H.peel_photon_left z
  rw [peelτ₁fun_eq hz']
  refine ⟨peelτ₁fun_eq (by rw [← hz', (C.2 _).1]), fun h => ?_⟩
  subst h
  exact (C.2 _).2 hz'

theorem peelτ₂fun_invol (z : Fin 0 ⊕ Wick.PhotonSlot (rightKinds κ e)) :
    peelτ₂fun C e z = z → False := by
  obtain ⟨z', hz'⟩ := H.peel_photon_right z
  rw [peelτ₂fun_eq hz']
  intro h
  subst h
  exact (C.2 _).2 hz'

theorem peelτ₂fun_invol' (z : Fin 0 ⊕ Wick.PhotonSlot (rightKinds κ e)) :
    peelτ₂fun C e (peelτ₂fun C e z) = z := by
  obtain ⟨z', hz'⟩ := H.peel_photon_right z
  rw [peelτ₂fun_eq hz']
  exact peelτ₂fun_eq (by rw [← hz', (C.2 _).1])

omit H in
/-- **The left piece of the cut.** -/
noncomputable def peelC₁ (H : PeelCutData C e f T) : Contraction 1 nA (leftKinds κ e) :=
  ⟨(Equiv.ofBijective _ (Finite.injective_iff_bijective.1 H.peelσ₁fun_injective),
    Function.Involutive.toPerm _ fun z => (H.peelτ₁fun_invol z).1),
    fun b => H.peelτ₁fun_invol b⟩

omit H in
/-- **The right piece of the cut.** -/
noncomputable def peelC₂ (H : PeelCutData C e f T) : Contraction 1 0 (rightKinds κ e) :=
  ⟨(Equiv.ofBijective _ (Finite.injective_iff_bijective.1 H.peelσ₂fun_injective),
    Function.Involutive.toPerm _ H.peelτ₂fun_invol'),
    fun b => ⟨H.peelτ₂fun_invol' b, H.peelτ₂fun_invol b⟩⟩

theorem peelC₁_fermion (z : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)) :
    H.peelC₁.1.1 z = peelσ₁fun C e z := rfl

theorem peelC₂_fermion (z : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e)) :
    H.peelC₂.1.1 z = peelσ₂fun C e f z := rfl

/-- **The pieces of the cut glue back to `C`.** -/
theorem glueIn_peelC : glueIn e H.peelC₁ H.peelC₂ = C := by
  obtain ⟨c, hc⟩ := H.peel_tail_right
  refine Subtype.ext (Prod.ext (Equiv.ext fun p => ?_) (Equiv.ext fun p => ?_))
  · obtain ⟨x, rfl⟩ := (fL κ e 1).surjective p
    rcases x with z | (i | r)
    · rcases H.peel_left_field z with hz | ⟨t, ht⟩
      · rw [glueIn_left_ext _ _ (H.peelσ₁fun_cross hz), H.peelC₂_fermion,
          peelσ₂fun_inl hc, hz, peel_fermion_tail, hc]
        rfl
      · rw [glueIn_left _ _ (peelσ₁fun_eq ht), ht]
    · exact i.elim0
    · obtain ⟨z, hz⟩ := H.peel_right_field r
      rw [fL_inr_inr, glueIn_right, H.peelC₂_fermion, peelσ₂fun_inr hz, hz]
  · obtain ⟨x, rfl⟩ := (pL κ e nA).surjective p
    change dsum (pL κ e nA) _ _ (pL κ e nA x) = _
    rcases x with z | z
    · obtain ⟨z', hz'⟩ := H.peel_photon_left z
      rw [dsum_apply_inl, hz']
      exact congrArg (fun y => pL κ e nA (.inl y)) (peelτ₁fun_eq hz')
    · obtain ⟨z', hz'⟩ := H.peel_photon_right z
      rw [dsum_apply_inr, hz']
      exact congrArg (fun y => pL κ e nA (.inr y)) (peelτ₂fun_eq hz')

theorem peelC₁_in {a : Wick.FermionVertex (leftKinds κ e)} (ha : f.1 = fvSplit κ e (.inl a)) :
    H.peelC₁.1.1 (.inr a) = .inl 0 :=
  H.peelσ₁fun_cross (by rw [fL_inl_inr, ha])

theorem peelC₂_out {c : Wick.FermionVertex (rightKinds κ e)}
    (hc : f.tail = fvSplit κ e (.inr c)) : H.peelC₂.1.1 (.inl 0) = .inr c :=
  peelσ₂fun_inl hc 0

end PeelCutData

/-- **Cutting a contraction**: for a cut `f` with tail side `T`, there are a split `e`,
increasing on each piece and with right image `T`, and pieces that glue back to `C`. -/
theorem peel_exists_glueIn (C : Contraction 1 nA κ) (f : FermionLine C) (T : Fin N → Prop)
    (lines : ∀ l : Line C, l ≠ .inl f → (T l.ends.1 ↔ T l.ends.2)) (htail : T f.tail.1)
    (hhead : ¬ T f.1.1) (hinV : ∀ y, C.1.1 (.inr y) = .inl 0 → T y.1)
    (hout : ∀ x, C.1.1 (.inl 0) = .inr x → ¬ T x.1)
    (hph : ∀ j a, C.1.2 (.inl j) = .inr a → ¬ T a.1) (hatt : ∀ i, C.1.1 (.inl 0) ≠ .inl i) :
    ∃ (N₁ N₂ : ℕ) (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N) (C₁ : Contraction 1 nA (leftKinds κ e))
      (C₂ : Contraction 1 0 (rightKinds κ e)) (a : Wick.FermionVertex (leftKinds κ e))
      (c : Wick.FermionVertex (rightKinds κ e)), N₁ + N₂ = N ∧ IsShuffle e ∧
      glueIn e C₁ C₂ = C ∧ C₁.1.1 (.inr a) = .inl 0 ∧ C₂.1.1 (.inl 0) = .inr c ∧
      ∀ v, T v ↔ ∃ r, e (.inr r) = v := by
  classical
  set s : Finset (Fin N) := univ.filter fun v => ¬ T v
  set e := finSumEquivOfFinset (s := s) rfl rfl
  have hL : ∀ t, ¬ T (e (.inl t)) := fun t => by
    have h1 : e (.inl t) ∈ s := s.orderEmbOfFin_mem rfl t
    exact (mem_filter.1 h1).2
  have hR : ∀ t, T (e (.inr t)) := fun t => by
    have h1 : e (.inr t) ∈ sᶜ := sᶜ.orderEmbOfFin_mem rfl t
    by_contra hT
    exact mem_compl.1 h1 (mem_filter.2 ⟨mem_univ _, hT⟩)
  have H : PeelCutData C e f T := ⟨lines, htail, hhead, hinV, hout, hph, hatt, hL, hR⟩
  obtain ⟨a, ha⟩ := H.peel_head_left
  obtain ⟨c, hc⟩ := H.peel_tail_right
  refine ⟨_, _, e, H.peelC₁, H.peelC₂, a, c, ?_, ⟨(s.orderEmbOfFin rfl).strictMono,
    (sᶜ.orderEmbOfFin rfl).strictMono⟩, H.glueIn_peelC, H.peelC₁_in ha, H.peelC₂_out hc,
    fun v => ⟨fun hv => ?_, ?_⟩⟩
  · rw [card_add_card_compl, Fintype.card_fin]
  · obtain ⟨x, rfl⟩ := e.surjective v
    rcases x with t | t
    · exact absurd hv (hL t)
    · exact ⟨t, rfl⟩
  · rintro ⟨r, rfl⟩
    exact hR r

end QED.GradedProof.X1C

end
