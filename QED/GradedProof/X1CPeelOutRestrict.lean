/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CPeelRestrict

/-!
# (X₁) piece C: cutting a contraction at an out-leg cut

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (the graph theory of the out-leg peel); the mirror of
`X1CPeelRestrict`. Let `f` be a fermion line of `C` and `T` a set of vertices such that every
other line has both ends in `T` or both out of `T`, the head of `f` is in `T` and its tail is
not, the out-vertex is in `T` and the in-vertex and the photon externals are not
(`PeelOutCutData`, for a split `e` with right image `T`). Then the restrictions
`PeelOutCutData.peelOutC₁` (vertices out of `T`, the outgoing external contracted with the `Ψ̄` of
the tail of `f`) and `PeelOutCutData.peelOutC₂` (vertices in `T`, the field `Ψ` of the head of `f`
contracted with the incoming external) glue back to `C`: **`PeelOutCutData.glueOut_peelOutC`**.
**`peelOut_exists_glueOut`**: such a split, increasing on each piece, exists for every such `T`.

The fermion pairings of the pieces are `peelOutσ₁fun` (special at the external, read off at the
head of `f`) and `peelOutσ₂fun` (read off from `C` on the fields of the right piece); the photon
pairings are those of the in-leg cut, `peelτ₁fun`, `peelτ₂fun`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line FermionLine PhotonLine Joined IsBridge)
open QED.TwoLoop.Enumeration (tail_eq)
open Relation Finset

variable {nA N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind}

/-- **The data of an out-leg cut** of `C` at the fermion line `f` with head side `T`, the right
image of `e`. -/
structure PeelOutCutData (C : Contraction 1 nA κ) (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N)
    (f : FermionLine C) (T : Fin N → Prop) : Prop where
  lines : ∀ l : Line C, l ≠ .inl f → (T l.ends.1 ↔ T l.ends.2)
  head : T f.1.1
  tail : ¬ T f.tail.1
  out : ∀ x, C.1.1 (.inl 0) = .inr x → T x.1
  inV : ∀ y, C.1.1 (.inr y) = .inl 0 → ¬ T y.1
  photon : ∀ j a, C.1.2 (.inl j) = .inr a → ¬ T a.1
  attached : ∀ i, C.1.1 (.inl 0) ≠ .inl i
  left : ∀ s, ¬ T (e (.inl s))
  right : ∀ r, T (e (.inr r))

theorem peelOut_decR_left {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N} (s : Wick.FermionVertex (leftKinds κ e)) :
    peelDecR (e := e) (.inr (fvSplit κ e (.inl s))) = .inl 0 := by
  have h : (Sum.inr (fvSplit κ e (.inl s)) : Fin 1 ⊕ Wick.FermionVertex κ) =
      fR κ e 1 (.inl (.inr s)) := rfl
  rw [h, peelDecR, Equiv.symm_apply_apply]
  rfl

variable (C : Contraction 1 nA κ) (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N) (f : FermionLine C)

/-- The fermion pairing of the left piece of an out-leg cut. -/
def peelOutσ₁fun (z : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)) :
    Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e) :=
  Sum.elim (fun _ => peelDecL (C.1.1 (.inr f.1)))
    (fun t => peelDecL (C.1.1 (.inr (fvSplit κ e (.inl t))))) z

/-- The fermion pairing of the right piece of an out-leg cut. -/
def peelOutσ₂fun (z : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e)) :
    Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e) :=
  peelDecR (C.1.1 (fR κ e 1 (.inr z)))

variable {C e f}

theorem peelOutσ₁fun_inr {t : Wick.FermionVertex (leftKinds κ e)}
    {z : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)}
    (h : C.1.1 (.inr (fvSplit κ e (.inl t))) = fL κ e 1 (.inl z)) :
    peelOutσ₁fun C e f (.inr t) = z := by
  rw [peelOutσ₁fun, Sum.elim_inr, h, peelDecL_fL_inl]

theorem peelOutσ₁fun_inl {a : Wick.FermionVertex (leftKinds κ e)}
    (ha : f.tail = fvSplit κ e (.inl a)) (i : Fin 1) : peelOutσ₁fun C e f (.inl i) = .inr a := by
  rw [peelOutσ₁fun, Sum.elim_inl, peel_fermion_tail, ha, ← fL_inl_inr, peelDecL_fL_inl]

theorem peelOutσ₂fun_eq {z : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e)}
    {r : Wick.FermionVertex (rightKinds κ e)}
    (h : C.1.1 (fR κ e 1 (.inr z)) = .inr (fvSplit κ e (.inr r))) :
    peelOutσ₂fun C e z = .inr r := by
  rw [peelOutσ₂fun, h, ← fR_inr_inr, peelDecR_fR_inr]

namespace PeelOutCutData

variable {T : Fin N → Prop} (H : PeelOutCutData C e f T)
include H

theorem peelOut_fv_left {t : Wick.FermionVertex κ} (ht : ¬ T t.1) :
    ∃ s, t = fvSplit κ e (.inl s) := by
  obtain ⟨x, rfl⟩ := (fvSplit κ e).surjective t
  rcases x with s | r
  · exact ⟨s, rfl⟩
  · exact absurd (H.right r.1) ht

theorem peelOut_fv_right {t : Wick.FermionVertex κ} (ht : T t.1) :
    ∃ r, t = fvSplit κ e (.inr r) := by
  obtain ⟨x, rfl⟩ := (fvSplit κ e).surjective t
  rcases x with s | r
  · exact absurd ht (H.left s.1)
  · exact ⟨r, rfl⟩

theorem peelOut_ps_left {a : Wick.PhotonSlot κ} (ha : ¬ T a.1) : ∃ s, a = psSplit κ e (.inl s) := by
  obtain ⟨x, rfl⟩ := (psSplit κ e).surjective a
  rcases x with s | r
  · exact ⟨s, rfl⟩
  · exact absurd (H.right r.1) ha

theorem peelOut_ps_right {a : Wick.PhotonSlot κ} (ha : T a.1) : ∃ r, a = psSplit κ e (.inr r) := by
  obtain ⟨x, rfl⟩ := (psSplit κ e).surjective a
  rcases x with s | r
  · exact absurd ha (H.left s.1)
  · exact ⟨r, rfl⟩

/-- The ends of a fermion line other than `f` are on the same side. -/
theorem peelOut_fermion_cross {v t : Wick.FermionVertex κ} (h : C.1.1 (.inr v) = .inr t)
    (hv : v ≠ f.1) : T t.1 ↔ T v.1 := by
  have := H.lines (.inl (peelFLine h))
    (fun hl => hv (congrArg Subtype.val (Sum.inl_injective hl)))
  simp only [Line.ends] at this
  rw [show (peelFLine h).tail = t from tail_eq _ h] at this
  exact this

/-- The ends of a photon line are on the same side. -/
theorem peelOut_photon_pair {a b : Wick.PhotonSlot κ} (h : C.1.2 (.inr a) = .inr b) :
    T a.1 ↔ T b.1 := by
  obtain ⟨l, hl⟩ := tadSide_photon_pair h
  have := H.lines (.inr l) Sum.inr_ne_inl
  simp only [Line.ends] at this
  rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at this
  · exact this
  · exact this.symm

theorem peelOut_tail_left : ∃ a, f.tail = fvSplit κ e (.inl a) := H.peelOut_fv_left H.tail

theorem peelOut_head_right : ∃ c, f.1 = fvSplit κ e (.inr c) := H.peelOut_fv_right H.head

/-- A vertex field of the left piece is contracted with the left piece or the external. -/
theorem peelOut_left_field (t : Wick.FermionVertex (leftKinds κ e)) :
    ∃ z, C.1.1 (.inr (fvSplit κ e (.inl t))) = fL κ e 1 (.inl z) := by
  have hv : ¬ T (fvSplit κ e (.inl t)).1 := H.left t.1
  rcases h : C.1.1 (.inr (fvSplit κ e (.inl t))) with j | s
  · exact ⟨.inl j, rfl⟩
  · have hvf : fvSplit κ e (.inl t) ≠ f.1 := fun hvf => hv (hvf ▸ H.head)
    obtain ⟨s', rfl⟩ := H.peelOut_fv_left fun hs => hv ((H.peelOut_fermion_cross h hvf).1 hs)
    exact ⟨.inr s', rfl⟩

/-- A field of the right piece is the field of `f` or is contracted with the right piece. -/
theorem peelOut_right_field (z : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e)) :
    fR κ e 1 (.inr z) = .inr f.1 ∨
      ∃ r, C.1.1 (fR κ e 1 (.inr z)) = .inr (fvSplit κ e (.inr r)) := by
  rcases z with i | r
  · right
    rw [Subsingleton.elim i 0, fR_inr_inl]
    rcases h : C.1.1 (.inl 0) with j | x
    · exact absurd h (H.attached j)
    · obtain ⟨r, rfl⟩ := H.peelOut_fv_right (H.out x h)
      exact ⟨r, rfl⟩
  · rw [fR_inr_inr]
    have hv : T (fvSplit κ e (.inr r)).1 := H.right r.1
    rcases h : C.1.1 (.inr (fvSplit κ e (.inr r))) with j | t
    · exact absurd hv (H.inV _ (by rw [h, Subsingleton.elim j 0]))
    · by_cases hvf : fvSplit κ e (.inr r) = f.1
      · exact .inl (by rw [hvf])
      · obtain ⟨t', rfl⟩ := H.peelOut_fv_right ((H.peelOut_fermion_cross h hvf).2 hv)
        exact .inr ⟨t', rfl⟩

theorem peelOut_photon_left (z : Fin nA ⊕ Wick.PhotonSlot (leftKinds κ e)) :
    ∃ z', C.1.2 (pL κ e nA (.inl z)) = pL κ e nA (.inl z') := by
  rcases z with j | s
  · rw [pL_inl_inl]
    rcases h : C.1.2 (.inl j) with j' | b
    · exact ⟨.inl j', rfl⟩
    · obtain ⟨b', rfl⟩ := H.peelOut_ps_left (H.photon j b h)
      exact ⟨.inr b', rfl⟩
  · rw [pL_inl_inr]
    rcases h : C.1.2 (.inr (psSplit κ e (.inl s))) with j' | b
    · exact ⟨.inl j', rfl⟩
    · obtain ⟨b', rfl⟩ := H.peelOut_ps_left fun hb => H.left s.1 ((H.peelOut_photon_pair h).2 hb)
      exact ⟨.inr b', rfl⟩

theorem peelOut_photon_right (z : Fin 0 ⊕ Wick.PhotonSlot (rightKinds κ e)) :
    ∃ z', C.1.2 (pL κ e nA (.inr z)) = pL κ e nA (.inr z') := by
  rcases z with i | s
  · exact i.elim0
  · rw [pL_inr_inr]
    rcases h : C.1.2 (.inr (psSplit κ e (.inr s))) with j | b
    · have h' : C.1.2 (.inl j) = .inr (psSplit κ e (.inr s)) := by rw [← h, (C.2 _).1]
      exact absurd (H.right s.1) (H.photon j _ h')
    · obtain ⟨b', rfl⟩ := H.peelOut_ps_right ((H.peelOut_photon_pair h).1 (H.right s.1))
      exact ⟨.inr b', rfl⟩

/-! ### The pairings of the pieces -/

theorem peelOutσ₂fun_cross {z : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e)}
    (hz : fR κ e 1 (.inr z) = .inr f.1) : peelOutσ₂fun C e z = .inl 0 := by
  obtain ⟨a, ha⟩ := H.peelOut_tail_left
  rw [peelOutσ₂fun, hz, peel_fermion_tail, ha, peelOut_decR_left]

theorem peelOutσ₁fun_injective : Function.Injective (peelOutσ₁fun C e f) := by
  obtain ⟨a, ha⟩ := H.peelOut_tail_left
  have key : ∀ t, peelOutσ₁fun C e f (.inr t) ≠ .inr a := by
    intro t h
    obtain ⟨z, hz⟩ := H.peelOut_left_field t
    rw [peelOutσ₁fun_inr hz] at h
    subst h
    have h1 : fvSplit κ e (.inl t) = f.1 := Sum.inr_injective (C.1.1.injective
      (hz.trans (by rw [fL_inl_inr, ← ha, peel_fermion_tail])))
    have h2 : ¬ T (fvSplit κ e (.inl t)).1 := H.left t.1
    rw [h1] at h2
    exact h2 H.head
  rintro (i | t) (i' | t') h
  · rw [Subsingleton.elim i i']
  · rw [peelOutσ₁fun_inl ha] at h
    exact absurd h.symm (key t')
  · rw [peelOutσ₁fun_inl ha] at h
    exact absurd h (key t)
  · obtain ⟨z, hz⟩ := H.peelOut_left_field t
    obtain ⟨z', hz'⟩ := H.peelOut_left_field t'
    rw [peelOutσ₁fun_inr hz, peelOutσ₁fun_inr hz'] at h
    subst h
    have := C.1.1.injective (hz.trans hz'.symm)
    exact congrArg Sum.inr (Sum.inl_injective ((fvSplit κ e).injective (Sum.inr_injective this)))

theorem peelOutσ₂fun_injective : Function.Injective (peelOutσ₂fun C e) := by
  intro z z' h
  rcases H.peelOut_right_field z with hz | ⟨r, hr⟩ <;>
    rcases H.peelOut_right_field z' with hz' | ⟨r', hr'⟩
  · exact Sum.inr_injective ((fR κ e 1).injective (hz.trans hz'.symm))
  · rw [H.peelOutσ₂fun_cross hz, peelOutσ₂fun_eq hr'] at h
    exact absurd h Sum.inl_ne_inr
  · rw [peelOutσ₂fun_eq hr, H.peelOutσ₂fun_cross hz'] at h
    exact absurd h Sum.inr_ne_inl
  · rw [peelOutσ₂fun_eq hr, peelOutσ₂fun_eq hr'] at h
    cases Sum.inr_injective h
    exact Sum.inr_injective ((fR κ e 1).injective (C.1.1.injective (hr.trans hr'.symm)))

theorem peelOutτ₁_invol (z : Fin nA ⊕ Wick.PhotonSlot (leftKinds κ e)) :
    peelτ₁fun C e (peelτ₁fun C e z) = z ∧ peelτ₁fun C e z ≠ z := by
  obtain ⟨z', hz'⟩ := H.peelOut_photon_left z
  rw [peelτ₁fun_eq hz']
  refine ⟨peelτ₁fun_eq (by rw [← hz', (C.2 _).1]), fun h => ?_⟩
  subst h
  exact (C.2 _).2 hz'

theorem peelOutτ₂_invol (z : Fin 0 ⊕ Wick.PhotonSlot (rightKinds κ e)) :
    peelτ₂fun C e z = z → False := by
  obtain ⟨z', hz'⟩ := H.peelOut_photon_right z
  rw [peelτ₂fun_eq hz']
  intro h
  subst h
  exact (C.2 _).2 hz'

theorem peelOutτ₂_invol' (z : Fin 0 ⊕ Wick.PhotonSlot (rightKinds κ e)) :
    peelτ₂fun C e (peelτ₂fun C e z) = z := by
  obtain ⟨z', hz'⟩ := H.peelOut_photon_right z
  rw [peelτ₂fun_eq hz']
  exact peelτ₂fun_eq (by rw [← hz', (C.2 _).1])

omit H in
/-- **The left piece of the out-leg cut.** -/
noncomputable def peelOutC₁ (H : PeelOutCutData C e f T) : Contraction 1 nA (leftKinds κ e) :=
  ⟨(Equiv.ofBijective _ (Finite.injective_iff_bijective.1 H.peelOutσ₁fun_injective),
    Function.Involutive.toPerm _ fun z => (H.peelOutτ₁_invol z).1),
    fun b => H.peelOutτ₁_invol b⟩

omit H in
/-- **The right piece of the out-leg cut.** -/
noncomputable def peelOutC₂ (H : PeelOutCutData C e f T) : Contraction 1 0 (rightKinds κ e) :=
  ⟨(Equiv.ofBijective _ (Finite.injective_iff_bijective.1 H.peelOutσ₂fun_injective),
    Function.Involutive.toPerm _ H.peelOutτ₂_invol'),
    fun b => ⟨H.peelOutτ₂_invol' b, H.peelOutτ₂_invol b⟩⟩

theorem peelOutC₁_fermion (z : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)) :
    H.peelOutC₁.1.1 z = peelOutσ₁fun C e f z := rfl

theorem peelOutC₂_fermion (z : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e)) :
    H.peelOutC₂.1.1 z = peelOutσ₂fun C e z := rfl

/-- **The pieces of the out-leg cut glue back to `C`.** -/
theorem glueOut_peelOutC : glueOut e H.peelOutC₁ H.peelOutC₂ = C := by
  obtain ⟨a, ha⟩ := H.peelOut_tail_left
  refine Subtype.ext (Prod.ext (Equiv.ext fun p => ?_) (Equiv.ext fun p => ?_))
  · obtain ⟨x, rfl⟩ := (fR κ e 1).surjective p
    rcases x with (i | t) | z
    · exact i.elim0
    · obtain ⟨z, hz⟩ := H.peelOut_left_field t
      rw [fR_inl_inr, glueOut_left, H.peelOutC₁_fermion, peelOutσ₁fun_inr hz, hz]
    · rcases H.peelOut_right_field z with hz | ⟨r, hr⟩
      · rw [glueOut_right_ext _ _ (H.peelOutσ₂fun_cross hz), H.peelOutC₁_fermion,
          peelOutσ₁fun_inl ha, hz, peel_fermion_tail, ha]
        rfl
      · rw [glueOut_right _ _ (peelOutσ₂fun_eq hr), hr]
  · obtain ⟨x, rfl⟩ := (pL κ e nA).surjective p
    change dsum (pL κ e nA) _ _ (pL κ e nA x) = _
    rcases x with z | z
    · obtain ⟨z', hz'⟩ := H.peelOut_photon_left z
      rw [dsum_apply_inl, hz']
      exact congrArg (fun y => pL κ e nA (.inl y)) (peelτ₁fun_eq hz')
    · obtain ⟨z', hz'⟩ := H.peelOut_photon_right z
      rw [dsum_apply_inr, hz']
      exact congrArg (fun y => pL κ e nA (.inr y)) (peelτ₂fun_eq hz')

theorem peelOutC₁_out {a : Wick.FermionVertex (leftKinds κ e)}
    (ha : f.tail = fvSplit κ e (.inl a)) : H.peelOutC₁.1.1 (.inl 0) = .inr a :=
  peelOutσ₁fun_inl ha 0

theorem peelOutC₂_in {c : Wick.FermionVertex (rightKinds κ e)} (hc : f.1 = fvSplit κ e (.inr c)) :
    H.peelOutC₂.1.1 (.inr c) = .inl 0 :=
  H.peelOutσ₂fun_cross (by rw [fR_inr_inr, hc])

end PeelOutCutData

/-- **Cutting a contraction at an out-leg cut**: for a cut `f` with head side `T`, there are a
split `e`, increasing on each piece and with right image `T`, and pieces that glue back to
`C`. -/
theorem peelOut_exists_glueOut (C : Contraction 1 nA κ) (f : FermionLine C) (T : Fin N → Prop)
    (lines : ∀ l : Line C, l ≠ .inl f → (T l.ends.1 ↔ T l.ends.2)) (hhead : T f.1.1)
    (htail : ¬ T f.tail.1) (hout : ∀ x, C.1.1 (.inl 0) = .inr x → T x.1)
    (hinV : ∀ y, C.1.1 (.inr y) = .inl 0 → ¬ T y.1)
    (hph : ∀ j a, C.1.2 (.inl j) = .inr a → ¬ T a.1) (hatt : ∀ i, C.1.1 (.inl 0) ≠ .inl i) :
    ∃ (N₁ N₂ : ℕ) (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N) (C₁ : Contraction 1 nA (leftKinds κ e))
      (C₂ : Contraction 1 0 (rightKinds κ e)) (a : Wick.FermionVertex (leftKinds κ e))
      (c : Wick.FermionVertex (rightKinds κ e)), N₁ + N₂ = N ∧ IsShuffle e ∧
      glueOut e C₁ C₂ = C ∧ C₁.1.1 (.inl 0) = .inr a ∧ C₂.1.1 (.inr c) = .inl 0 ∧
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
  have H : PeelOutCutData C e f T := ⟨lines, hhead, htail, hout, hinV, hph, hatt, hL, hR⟩
  obtain ⟨a, ha⟩ := H.peelOut_tail_left
  obtain ⟨c, hc⟩ := H.peelOut_head_right
  refine ⟨_, _, e, H.peelOutC₁, H.peelOutC₂, a, c, ?_, ⟨(s.orderEmbOfFin rfl).strictMono,
    (sᶜ.orderEmbOfFin rfl).strictMono⟩, H.glueOut_peelOutC, H.peelOutC₁_out ha, H.peelOutC₂_in hc,
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
