/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CLinesIn

/-!
# (X₁) piece C: reachability in a contraction and in a glued contraction

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (the graph theory of the peels). Reachability is
`Relation.ReflTransGen (Joined C S)`: paths along internal lines outside a set `S`.

* Generalities: `peel_reach_symm`, `peel_reach_mono`, `peel_reach_sides` (in a connected
  contraction every vertex lies on the side of one end of any line).
* `peel_orbit`: an induction principle along a cycle of a permutation, used for the open fermion
  line: `peel_reach_out_in` (the out-vertex reaches the in-vertex along fermion lines),
  `peel_tail_reach_in`, `peel_head_reach_out` (the tail side of a fermion bridge holds the
  in-vertex, its head side the out-vertex).
* For a `LineSplit` (the lines of `C` are those of the pieces and one bridge between them):
  `peel_proj_left`, `peel_proj_right` (a path from a vertex of one piece projects to a path in
  that piece; it leaves the piece only through the bridge), the lifts `peel_lift_left`,
  `peel_lift_right`, and the consequences `peel_isBridge_left_iff`, `peel_isBridge_right_iff`,
  `peel_isBridge_bridge`, `peel_connected_left`, `peel_connected_right`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line FermionLine PhotonLine Joined IsBridge VerticesConnected)
open QED.TwoLoop.Enumeration (tail_eq)
open Relation

section Reach

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}

theorem peel_joined_symm {S : Set (Line C)} {a b : Fin N} (h : Joined C S a b) :
    Joined C S b a := by
  obtain ⟨f, hf, h | h⟩ := h
  · exact ⟨f, hf, .inr h⟩
  · exact ⟨f, hf, .inl h⟩

theorem peel_reach_symm {S : Set (Line C)} {a b : Fin N} (h : ReflTransGen (Joined C S) a b) :
    ReflTransGen (Joined C S) b a := by
  induction h with
  | refl => exact .refl
  | tail _ hJ ih => exact (ReflTransGen.single (peel_joined_symm hJ)).trans ih

theorem peel_reach_mono {S S' : Set (Line C)} (hS : S ⊆ S') {a b : Fin N}
    (h : ReflTransGen (Joined C S') a b) : ReflTransGen (Joined C S) a b :=
  ReflTransGen.lift id (fun _ _ ⟨f, hf, he⟩ => ⟨f, fun h => hf (hS h), he⟩) _ _ h

theorem peel_joined_ends {S : Set (Line C)} (f : Line C) (hf : f ∉ S) :
    Joined C S f.ends.1 f.ends.2 :=
  ⟨f, hf, .inl rfl⟩

/-- **The two sides of a line cover a connected contraction.** -/
theorem peel_reach_sides (hV : VerticesConnected C) (l : Line C) (v : Fin N) :
    ReflTransGen (Joined C {l}) l.ends.1 v ∨ ReflTransGen (Joined C {l}) l.ends.2 v := by
  induction hV l.ends.1 v with
  | refl => exact .inl .refl
  | tail _ hJ ih =>
    obtain ⟨f, -, hfe⟩ := hJ
    by_cases hf : f = l
    · subst hf
      rcases hfe with hfe | hfe <;> rw [hfe]
      · exact .inr .refl
      · exact .inl .refl
    · have hJ : Joined C {l} _ _ := ⟨f, hf, hfe⟩
      exact ih.imp (fun h => h.tail hJ) (fun h => h.tail hJ)

/-- The two sides of a bridge are disjoint. -/
theorem peel_sides_disjoint {l : Line C} (hl : IsBridge l) {v : Fin N}
    (h₁ : ReflTransGen (Joined C {l}) l.ends.1 v) (h₂ : ReflTransGen (Joined C {l}) l.ends.2 v) :
    False :=
  hl (h₁.trans (peel_reach_symm h₂))

end Reach

/-! ### Cycles of a permutation -/

/-- **Induction along a cycle**: a property of `a` that propagates along `σ` until `σ⁻¹ a` holds
at `σ⁻¹ a`. -/
theorem peel_orbit {α : Type*} [Finite α] (σ : Equiv.Perm α) (a : α) (Q : α → Prop) (ha : Q a)
    (hstep : ∀ z, Q z → z ≠ σ.symm a → Q (σ z)) : Q (σ.symm a) := by
  by_contra hn
  have hall : ∀ k : ℕ, Q ((σ ^ k) a) := by
    intro k
    induction k with
    | zero => simpa using ha
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hstep _ ih fun h => hn (h ▸ ih)
  have hpos := orderOf_pos σ
  have h1 : σ ^ (orderOf σ - 1) * σ = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  have h2 : σ ^ (orderOf σ - 1) = σ⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 := hall (orderOf σ - 1)
  rw [h2] at h3
  exact hn h3

/-! ### The open fermion line -/

section OpenLine

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 1 nA κ}

/-- The fermion line indexed by the vertex `v` whose `Ψ` is contracted with the `Ψ̄` of `s`. -/
def peelFLine {v s : Wick.FermionVertex κ} (h : C.1.1 (.inr v) = .inr s) : FermionLine C :=
  ⟨v, by rw [h]; rfl⟩

theorem peel_joined_fermion {S : Set (Line C)} {v s : Wick.FermionVertex κ}
    (h : C.1.1 (.inr v) = .inr s) (hS : (.inl (peelFLine h) : Line C) ∉ S) :
    Joined C S v.1 s.1 := by
  refine ⟨.inl (peelFLine h), hS, .inr ?_⟩
  simp only [Line.ends, tail_eq (peelFLine h) h]
  rfl

theorem peel_fermion_tail (f : FermionLine C) : C.1.1 (.inr f.1) = .inr f.tail := by
  obtain ⟨s, hs⟩ := Sum.isRight_iff.mp f.2
  rw [hs, tail_eq f hs]

/-- **The out-vertex reaches the in-vertex along the open fermion line.** -/
theorem peel_reach_out_in {x y : Wick.FermionVertex κ} (hx : C.1.1 (.inl 0) = .inr x)
    (hy : C.1.1 (.inr y) = .inl 0) {S : Set (Line C)}
    (hS : ∀ f : FermionLine C, (.inl f : Line C) ∉ S) :
    ReflTransGen (Joined C S) x.1 y.1 := by
  have hy' : C.1.1.symm (.inl 0) = .inr y := by rw [← hy, Equiv.symm_apply_apply]
  have key := peel_orbit C.1.1 (.inl 0)
    (fun z => z = .inl 0 ∨ ∃ v, z = .inr v ∧ ReflTransGen (Joined C S) x.1 v.1) (.inl rfl) ?_
  · rw [hy'] at key
    rcases key with h | ⟨v, hv, h⟩
    · exact absurd h Sum.inr_ne_inl
    · rwa [Sum.inr_injective hv]
  · rintro z (rfl | ⟨v, rfl, hv⟩) hne
    · exact .inr ⟨x, hx, .refl⟩
    · rw [hy'] at hne
      rcases h : C.1.1 (.inr v) with i | s
      · exact absurd (C.1.1.injective (h.trans ((congrArg Sum.inl
          (Subsingleton.elim i 0)).trans hy.symm))) hne
      · exact .inr ⟨s, rfl, hv.tail (peel_joined_fermion h (hS _))⟩

/-- **The tail side of a fermion bridge holds the in-vertex.** -/
theorem peel_tail_reach_in (f : FermionLine C) (hf : IsBridge (.inl f : Line C))
    {y : Wick.FermionVertex κ} (hy : C.1.1 (.inr y) = .inl 0) :
    ReflTransGen (Joined C {.inl f}) f.tail.1 y.1 := by
  have hs' : C.1.1.symm (.inr f.tail) = .inr f.1 := by
    rw [← peel_fermion_tail f, Equiv.symm_apply_apply]
  have key := peel_orbit C.1.1 (.inr f.tail)
    (fun z => ReflTransGen (Joined C {.inl f}) f.tail.1 y.1 ∨
      ∃ v, z = .inr v ∧ ReflTransGen (Joined C {.inl f}) f.tail.1 v.1)
    (.inr ⟨_, rfl, .refl⟩) ?_
  · rw [hs'] at key
    rcases key with h | ⟨v, hv, h⟩
    · exact h
    · cases Sum.inr_injective hv
      exact absurd h hf
  · rintro z (h | ⟨v, rfl, hv⟩) hne
    · exact .inl h
    · rw [hs'] at hne
      rcases h : C.1.1 (.inr v) with i | s'
      · have hvy : v = y := Sum.inr_injective (C.1.1.injective (h.trans ((congrArg Sum.inl
          (Subsingleton.elim i 0)).trans hy.symm)))
        exact .inl (hvy ▸ hv)
      · refine .inr ⟨s', rfl, hv.tail (peel_joined_fermion h fun hm => hne ?_)⟩
        exact congrArg Sum.inr (congrArg Subtype.val (Sum.inl_injective
          (Set.mem_singleton_iff.1 hm)))

/-- **The head side of a fermion bridge holds the out-vertex.** -/
theorem peel_head_reach_out (f : FermionLine C) (hf : IsBridge (.inl f : Line C))
    {x : Wick.FermionVertex κ} (hx : C.1.1 (.inl 0) = .inr x) :
    ReflTransGen (Joined C {.inl f}) f.1.1 x.1 := by
  have hs := peel_fermion_tail f
  have key := peel_orbit C.1.1.symm (.inr f.1)
    (fun z => ReflTransGen (Joined C {.inl f}) f.1.1 x.1 ∨
      ∃ v, z = .inr v ∧ ReflTransGen (Joined C {.inl f}) f.1.1 v.1)
    (.inr ⟨_, rfl, .refl⟩) ?_
  · rw [Equiv.symm_symm, hs] at key
    rcases key with h | ⟨v, hv, h⟩
    · exact h
    · cases Sum.inr_injective hv
      exact absurd (peel_reach_symm h) hf
  · rintro z (h | ⟨v, rfl, hv⟩) hne
    · exact .inl h
    · rw [Equiv.symm_symm, hs] at hne
      rcases h : C.1.1.symm (.inr v) with i | s'
      · have h' : C.1.1 (.inl i) = .inr v := by rw [← h, Equiv.apply_symm_apply]
        rw [Subsingleton.elim i 0, hx] at h'
        exact .inl (Sum.inr_injective h' ▸ hv)
      · have h' : C.1.1 (.inr s') = .inr v := by rw [← h, Equiv.apply_symm_apply]
        refine .inr ⟨s', rfl, hv.tail (peel_joined_symm (peel_joined_fermion h' fun hm => ?_))⟩
        have hsf : s' = f.1 := congrArg Subtype.val (Sum.inl_injective
          (Set.mem_singleton_iff.1 hm))
        apply hne
        rw [← h', hsf, hs]

end OpenLine

/-! ### Paths in a split contraction -/

namespace LineSplit

variable {nf nA N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}
  {nf₁ nA₁ nf₂ nA₂ : ℕ} {C : Contraction nf nA κ} {C₁ : Contraction nf₁ nA₁ (leftKinds κ e)}
  {C₂ : Contraction nf₂ nA₂ (rightKinds κ e)} {u w : Fin N} (L : LineSplit C C₁ C₂ u w)

/-- The bridge line of a split. -/
def peelBridge : Line C := L.equiv (.inr (.inr ()))

/-- The lines of the left piece in a set of lines of `C`. -/
def peelSet₁ (S : Set (Line C)) : Set (Line C₁) := (fun g => L.equiv (.inl g)) ⁻¹' S

/-- The lines of the right piece in a set of lines of `C`. -/
def peelSet₂ (S : Set (Line C)) : Set (Line C₂) := (fun g => L.equiv (.inr (.inl g))) ⁻¹' S

theorem peelSet₁_singleton (g : Line C₁) : L.peelSet₁ {L.equiv (.inl g)} = {g} := by
  ext g'
  simp [peelSet₁]

theorem peelSet₂_singleton (g : Line C₂) : L.peelSet₂ {L.equiv (.inr (.inl g))} = {g} := by
  ext g'
  simp [peelSet₂]

theorem peelSet₁_bridge : L.peelSet₁ {L.peelBridge} = ∅ := by
  ext g'
  simp [peelSet₁, peelBridge]

theorem peelSet₂_bridge : L.peelSet₂ {L.peelBridge} = ∅ := by
  ext g'
  simp [peelSet₂, peelBridge]

theorem peel_lift_left {S : Set (Line C)} {s t : Fin N₁}
    (h : ReflTransGen (Joined C₁ (L.peelSet₁ S)) s t) :
    ReflTransGen (Joined C S) (e (.inl s)) (e (.inl t)) := by
  refine ReflTransGen.lift (fun s => e (.inl s)) (fun a b hab => ?_) _ _ h
  obtain ⟨f, hf, hfe⟩ := hab
  refine ⟨L.equiv (.inl f), hf, ?_⟩
  rw [L.ends_left]
  rcases hfe with hfe | hfe <;> rw [hfe]
  · exact .inl rfl
  · exact .inr rfl

theorem peel_lift_right {S : Set (Line C)} {s t : Fin N₂}
    (h : ReflTransGen (Joined C₂ (L.peelSet₂ S)) s t) :
    ReflTransGen (Joined C S) (e (.inr s)) (e (.inr t)) := by
  refine ReflTransGen.lift (fun s => e (.inr s)) (fun a b hab => ?_) _ _ h
  obtain ⟨f, hf, hfe⟩ := hab
  refine ⟨L.equiv (.inr (.inl f)), hf, ?_⟩
  rw [L.ends_right]
  rcases hfe with hfe | hfe <;> rw [hfe]
  · exact .inl rfl
  · exact .inr rfl

/-- Lifting a path of the left piece, when no line of the left piece is removed. -/
theorem peel_lift_left' {S : Set (Line C)} (hS : ∀ g, L.equiv (.inl g) ∉ S) {s t : Fin N₁}
    (h : ReflTransGen (Joined C₁ ∅) s t) : ReflTransGen (Joined C S) (e (.inl s)) (e (.inl t)) :=
  L.peel_lift_left (peel_reach_mono (fun g hg => hS g hg) h)

/-- Lifting a path of the right piece, when no line of the right piece is removed. -/
theorem peel_lift_right' {S : Set (Line C)} (hS : ∀ g, L.equiv (.inr (.inl g)) ∉ S)
    {s t : Fin N₂} (h : ReflTransGen (Joined C₂ ∅) s t) :
    ReflTransGen (Joined C S) (e (.inr s)) (e (.inr t)) :=
  L.peel_lift_right (peel_reach_mono (fun g hg => hS g hg) h)

variable {a : Fin N₁} {c : Fin N₂}

/-- **Projection of a path from a vertex of the left piece**: it stays in the left piece except
through the bridge (left end `a`), and projects to a path of the left piece. -/
theorem peel_proj_left
    (hb : (u = e (.inl a) ∧ w = e (.inr c)) ∨ (u = e (.inr c) ∧ w = e (.inl a)))
    {S : Set (Line C)} {s : Fin N₁} {v : Fin N} (h : ReflTransGen (Joined C S) (e (.inl s)) v) :
    Sum.elim (fun s' => ReflTransGen (Joined C₁ (L.peelSet₁ S)) s s')
      (fun _ => L.peelBridge ∉ S ∧ ReflTransGen (Joined C₁ (L.peelSet₁ S)) s a) (e.symm v) := by
  induction h with
  | refl => simpa using ReflTransGen.refl
  | @tail v v' _ hJ ih =>
    obtain ⟨l, hl, hends⟩ := hJ
    obtain ⟨x, rfl⟩ := L.equiv.surjective l
    rcases x with g | g | ⟨⟩
    · rw [L.ends_left] at hends
      rcases hends with hends | hends <;> simp only [Prod.mk.injEq] at hends <;>
        obtain ⟨rfl, rfl⟩ := hends <;>
        simp only [Equiv.symm_apply_apply, Sum.elim_inl] at ih ⊢
      · exact ih.tail ⟨g, hl, .inl rfl⟩
      · exact ih.tail ⟨g, hl, .inr rfl⟩
    · rw [L.ends_right] at hends
      rcases hends with hends | hends <;> simp only [Prod.mk.injEq] at hends <;>
        obtain ⟨rfl, rfl⟩ := hends <;>
        simp only [Equiv.symm_apply_apply, Sum.elim_inr] at ih ⊢ <;> exact ih
    · rw [L.ends_bridge] at hends
      rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hends with hends | hends <;> simp only [Prod.mk.injEq] at hends <;>
        obtain ⟨rfl, rfl⟩ := hends <;>
        simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr] at ih ⊢ <;>
        first | exact ⟨hl, ih⟩ | exact ih.2

/-- **Projection of a path from a vertex of the right piece** (right end `c` of the bridge). -/
theorem peel_proj_right
    (hb : (u = e (.inl a) ∧ w = e (.inr c)) ∨ (u = e (.inr c) ∧ w = e (.inl a)))
    {S : Set (Line C)} {s : Fin N₂} {v : Fin N} (h : ReflTransGen (Joined C S) (e (.inr s)) v) :
    Sum.elim (fun _ => L.peelBridge ∉ S ∧ ReflTransGen (Joined C₂ (L.peelSet₂ S)) s c)
      (fun s' => ReflTransGen (Joined C₂ (L.peelSet₂ S)) s s') (e.symm v) := by
  induction h with
  | refl => simpa using ReflTransGen.refl
  | @tail v v' _ hJ ih =>
    obtain ⟨l, hl, hends⟩ := hJ
    obtain ⟨x, rfl⟩ := L.equiv.surjective l
    rcases x with g | g | ⟨⟩
    · rw [L.ends_left] at hends
      rcases hends with hends | hends <;> simp only [Prod.mk.injEq] at hends <;>
        obtain ⟨rfl, rfl⟩ := hends <;>
        simp only [Equiv.symm_apply_apply, Sum.elim_inl] at ih ⊢ <;> exact ih
    · rw [L.ends_right] at hends
      rcases hends with hends | hends <;> simp only [Prod.mk.injEq] at hends <;>
        obtain ⟨rfl, rfl⟩ := hends <;>
        simp only [Equiv.symm_apply_apply, Sum.elim_inr] at ih ⊢
      · exact ih.tail ⟨g, hl, .inl rfl⟩
      · exact ih.tail ⟨g, hl, .inr rfl⟩
    · rw [L.ends_bridge] at hends
      rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hends with hends | hends <;> simp only [Prod.mk.injEq] at hends <;>
        obtain ⟨rfl, rfl⟩ := hends <;>
        simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr] at ih ⊢ <;>
        first | exact ⟨hl, ih⟩ | exact ih.2

variable (hb : (u = e (.inl a) ∧ w = e (.inr c)) ∨ (u = e (.inr c) ∧ w = e (.inl a)))
include hb

theorem peel_proj_left_left {S : Set (Line C)} {s s' : Fin N₁}
    (h : ReflTransGen (Joined C S) (e (.inl s)) (e (.inl s'))) :
    ReflTransGen (Joined C₁ (L.peelSet₁ S)) s s' := by
  simpa using L.peel_proj_left hb h

theorem peel_proj_right_right {S : Set (Line C)} {s s' : Fin N₂}
    (h : ReflTransGen (Joined C S) (e (.inr s)) (e (.inr s'))) :
    ReflTransGen (Joined C₂ (L.peelSet₂ S)) s s' := by
  simpa using L.peel_proj_right hb h

/-- Without the bridge, a path from the left piece stays in the left piece. -/
theorem peel_proj_left_mem {S : Set (Line C)} (hS : L.peelBridge ∈ S) {s : Fin N₁} {v : Fin N}
    (h : ReflTransGen (Joined C S) (e (.inl s)) v) : ∃ s', v = e (.inl s') := by
  have h' := L.peel_proj_left hb h
  rcases hx : e.symm v with s' | s'
  · exact ⟨s', by rw [← hx, Equiv.apply_symm_apply]⟩
  · rw [hx] at h'
    exact absurd hS h'.1

/-- Without the bridge, a path from the right piece stays in the right piece. -/
theorem peel_proj_right_mem {S : Set (Line C)} (hS : L.peelBridge ∈ S) {s : Fin N₂} {v : Fin N}
    (h : ReflTransGen (Joined C S) (e (.inr s)) v) : ∃ s', v = e (.inr s') := by
  have h' := L.peel_proj_right hb h
  rcases hx : e.symm v with s' | s'
  · rw [hx] at h'
    exact absurd hS h'.1
  · exact ⟨s', by rw [← hx, Equiv.apply_symm_apply]⟩

/-- **The bridge of a split is a bridge.** -/
theorem peel_isBridge_bridge : IsBridge L.peelBridge := by
  intro h
  have hends : L.peelBridge.ends = (u, w) := L.ends_bridge
  rw [hends] at h
  rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨s', hs'⟩ := L.peel_proj_left_mem (.inl ⟨rfl, rfl⟩) (S := {L.peelBridge})
      (Set.mem_singleton _) h
    exact Sum.inr_ne_inl (e.injective hs')
  · obtain ⟨s', hs'⟩ := L.peel_proj_right_mem (.inr ⟨rfl, rfl⟩) (S := {L.peelBridge})
      (Set.mem_singleton _) h
    exact Sum.inl_ne_inr (e.injective hs')

/-- **A line of the left piece is a bridge of `C` iff it is one of the left piece.** -/
theorem peel_isBridge_left_iff (g : Line C₁) : IsBridge (L.equiv (.inl g)) ↔ IsBridge g := by
  have hends := L.ends_left g
  unfold IsBridge
  rw [hends]
  constructor
  · intro h h₁
    apply h
    exact L.peel_lift_left (S := {L.equiv (.inl g)}) (s := g.ends.1) (t := g.ends.2)
      (by rwa [L.peelSet₁_singleton])
  · intro h h₁
    apply h
    have := L.peel_proj_left_left hb h₁
    rwa [L.peelSet₁_singleton] at this

/-- **A line of the right piece is a bridge of `C` iff it is one of the right piece.** -/
theorem peel_isBridge_right_iff (g : Line C₂) :
    IsBridge (L.equiv (.inr (.inl g))) ↔ IsBridge g := by
  have hends := L.ends_right g
  unfold IsBridge
  rw [hends]
  constructor
  · intro h h₁
    apply h
    exact L.peel_lift_right (S := {L.equiv (.inr (.inl g))}) (s := g.ends.1) (t := g.ends.2)
      (by rwa [L.peelSet₂_singleton])
  · intro h h₁
    apply h
    have := L.peel_proj_right_right hb h₁
    rwa [L.peelSet₂_singleton] at this

include L in
theorem peel_connected_left (hV : VerticesConnected C) : VerticesConnected C₁ :=
  fun _ _ => peel_reach_mono (Set.empty_subset _) (L.peel_proj_left_left hb (hV _ _))

include L in
theorem peel_connected_right (hV : VerticesConnected C) : VerticesConnected C₂ :=
  fun _ _ => peel_reach_mono (Set.empty_subset _) (L.peel_proj_right_right hb (hV _ _))

end LineSplit

end QED.GradedProof.X1C

end
