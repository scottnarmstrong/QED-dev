/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CLinesP
public import QED.GradedProof.X1CPeelRestrict

/-!
# (X₁) piece C: cutting a contraction at a photon-leg cut

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (the graph theory of the photon-leg peel). Let `p, q` be photon
fields of `C` contracted with each other, `p` on the left and `q` on the right piece of a split
`e` with right image `T`, such that every other pair of fields has both members in `T` or both out
of `T`, the fermion externals are out of `T` and the photon external is in `T`
(`PeelPCutData`). Then the restrictions glue back to `C` (**`PeelPCutData.exists_glueP`**): the
vertex piece `C₁` (vertices out of `T`, its external photon contracted with `p`) and the vacuum
polarization `C₂` (vertices in `T`, its first external photon contracted with what the photon
external of `C` is contracted with, its second with `q`).

The pairings of the pieces are the restrictions of those of `C` along injective encodings of the
fields of the pieces as fields of `C` whose images are closed under the pairings of `C`
(`peelP_perm_restrict`, `peelP_invol_restrict`). **`peelP_exists_glueP`**: for every such `T` a
split, increasing on each piece, with right image `T` exists.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction)
open Finset

/-! ### Restricting pairings -/

/-- **A permutation restricted to a closed set**, along an injective encoding. -/
theorem peelP_perm_restrict {α β : Type*} [Finite α] (enc : α → β)
    (henc : Function.Injective enc) (σ : Equiv.Perm β) (h : ∀ x, ∃ y, σ (enc x) = enc y) :
    ∃ τ : Equiv.Perm α, ∀ x, enc (τ x) = σ (enc x) := by
  choose f hf using h
  have hinj : Function.Injective f := fun x x' hxx => by
    have := (hf x).trans ((congrArg enc hxx).trans (hf x').symm)
    exact henc (σ.injective this)
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), fun x => (hf x).symm⟩

/-- **A fixed-point-free involution restricted to a closed set**, along an injective encoding. -/
theorem peelP_invol_restrict {α β : Type*} [Finite α] (enc : α → β)
    (henc : Function.Injective enc) (σ : Equiv.Perm β) (hσ : ∀ b, σ (σ b) = b ∧ σ b ≠ b)
    (h : ∀ x, ∃ y, σ (enc x) = enc y) :
    ∃ τ : Equiv.Perm α, (∀ x, enc (τ x) = σ (enc x)) ∧ ∀ x, τ (τ x) = x ∧ τ x ≠ x := by
  obtain ⟨τ, hτ⟩ := peelP_perm_restrict enc henc σ h
  refine ⟨τ, hτ, fun x => ⟨henc ?_, fun hx => (hσ (enc x)).2 ?_⟩⟩
  · rw [hτ, hτ, (hσ _).1]
  · rw [← hτ, hx]

/-! ### The data of a photon-leg cut -/

variable {N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}

/-- The photon fields of the vertex piece in `C`: its external photon is the field `q` of the
right piece. -/
def peelPEnc₁ (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N) (q' : Wick.PhotonSlot (rightKinds κ e)) :
    Fin 1 ⊕ Wick.PhotonSlot (leftKinds κ e) → Fin 1 ⊕ Wick.PhotonSlot κ :=
  Sum.elim (fun _ => .inr (psSplit κ e (.inr q'))) fun s => .inr (psSplit κ e (.inl s))

theorem peelPEnc₁_injective (q' : Wick.PhotonSlot (rightKinds κ e)) :
    Function.Injective (peelPEnc₁ e q') := by
  rintro (i | s) (i' | s') h <;> simp only [peelPEnc₁, Sum.elim_inl, Sum.elim_inr,
    Sum.inr.injEq, EmbeddingLike.apply_eq_iff_eq, reduceCtorEq] at h
  · rw [Subsingleton.elim i i']
  · cases h
    rfl

/-- **The data of a photon-leg cut** at the pair `(p, q) = (p' on the left, q' on the right)`
with cut side `T`, the right image of `e`. -/
structure PeelPCutData (C : Contraction 1 1 κ) (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N)
    (p' : Wick.PhotonSlot (leftKinds κ e)) (q' : Wick.PhotonSlot (rightKinds κ e))
    (T : Fin N → Prop) : Prop where
  pq : C.1.2 (.inr (psSplit κ e (.inl p'))) = .inr (psSplit κ e (.inr q'))
  fermion : ∀ v t, C.1.1 (.inr v) = .inr t → (T v.1 ↔ T t.1)
  photon : ∀ s t, C.1.2 (.inr s) = .inr t → s ≠ psSplit κ e (.inl p') →
    s ≠ psSplit κ e (.inr q') → (T s.1 ↔ T t.1)
  out : ∀ x, C.1.1 (.inl 0) = .inr x → ¬ T x.1
  inV : ∀ y, C.1.1 (.inr y) = .inl 0 → ¬ T y.1
  ext : ∀ a, C.1.2 (.inl 0) = .inr a → T a.1
  left : ∀ s, ¬ T (e (.inl s))
  right : ∀ r, T (e (.inr r))

namespace PeelPCutData

variable {C : Contraction 1 1 κ} {p' : Wick.PhotonSlot (leftKinds κ e)}
  {q' : Wick.PhotonSlot (rightKinds κ e)} {T : Fin N → Prop} (H : PeelPCutData C e p' q' T)
include H

theorem fv_left {t : Wick.FermionVertex κ} (ht : ¬ T t.1) : ∃ s, t = fvSplit κ e (.inl s) := by
  obtain ⟨x, rfl⟩ := (fvSplit κ e).surjective t
  rcases x with s | r
  · exact ⟨s, rfl⟩
  · exact absurd (H.right r.1) ht

theorem fv_right {t : Wick.FermionVertex κ} (ht : T t.1) : ∃ r, t = fvSplit κ e (.inr r) := by
  obtain ⟨x, rfl⟩ := (fvSplit κ e).surjective t
  rcases x with s | r
  · exact absurd ht (H.left s.1)
  · exact ⟨r, rfl⟩

theorem ps_left {a : Wick.PhotonSlot κ} (ha : ¬ T a.1) : ∃ s, a = psSplit κ e (.inl s) := by
  obtain ⟨x, rfl⟩ := (psSplit κ e).surjective a
  rcases x with s | r
  · exact ⟨s, rfl⟩
  · exact absurd (H.right r.1) ha

theorem ps_right {a : Wick.PhotonSlot κ} (ha : T a.1) : ∃ r, a = psSplit κ e (.inr r) := by
  obtain ⟨x, rfl⟩ := (psSplit κ e).surjective a
  rcases x with s | r
  · exact absurd ha (H.left s.1)
  · exact ⟨r, rfl⟩

theorem qp : C.1.2 (.inr (psSplit κ e (.inr q'))) = .inr (psSplit κ e (.inl p')) := by
  rw [← H.pq, (C.2 _).1]

omit H in
theorem ext_eq : ∃ a, C.1.2 (.inl 0) = .inr a := by
  rcases h : C.1.2 (.inl 0) with j | a
  · refine absurd ?_ (C.2 (.inl 0)).2
    rw [h, Subsingleton.elim j 0]
  · exact ⟨a, rfl⟩

/-! ### Closedness of the fields of the pieces -/

theorem closF₁ (z : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)) :
    ∃ z', C.1.1 (fL κ e 1 (.inl z)) = fL κ e 1 (.inl z') := by
  rcases z with i | t
  · rw [Subsingleton.elim i 0, fL_inl_inl]
    rcases h : C.1.1 (.inl 0) with j | x
    · exact ⟨.inl j, rfl⟩
    · obtain ⟨s, rfl⟩ := H.fv_left (H.out x h)
      exact ⟨.inr s, rfl⟩
  · rw [fL_inl_inr]
    rcases h : C.1.1 (.inr (fvSplit κ e (.inl t))) with j | x
    · exact ⟨.inl j, rfl⟩
    · obtain ⟨s, rfl⟩ := H.fv_left fun hx => H.left t.1 ((H.fermion _ _ h).2 hx)
      exact ⟨.inr s, rfl⟩

theorem closF₂ (z : Fin 0 ⊕ Wick.FermionVertex (rightKinds κ e)) :
    ∃ z', C.1.1 (fL κ e 1 (.inr z)) = fL κ e 1 (.inr z') := by
  rcases z with i | t
  · exact i.elim0
  · rw [fL_inr_inr]
    rcases h : C.1.1 (.inr (fvSplit κ e (.inr t))) with j | x
    · exact absurd (H.right t.1) (H.inV _ (by rw [h, Subsingleton.elim j 0]))
    · obtain ⟨s, rfl⟩ := H.fv_right ((H.fermion _ _ h).1 (H.right t.1))
      exact ⟨.inr s, rfl⟩

theorem closP₁ (z : Fin 1 ⊕ Wick.PhotonSlot (leftKinds κ e)) :
    ∃ z', C.1.2 (peelPEnc₁ e q' z) = peelPEnc₁ e q' z' := by
  rcases z with i | s
  · exact ⟨.inr p', H.qp⟩
  · simp only [peelPEnc₁, Sum.elim_inr]
    by_cases hs : s = p'
    · subst hs
      exact ⟨.inl 0, H.pq⟩
    · rcases h : C.1.2 (.inr (psSplit κ e (.inl s))) with j | t
      · have h' : C.1.2 (.inl j) = .inr (psSplit κ e (.inl s)) := by rw [← h, (C.2 _).1]
        rw [Subsingleton.elim j 0] at h'
        exact absurd (H.ext _ h') (H.left s.1)
      · have hne₁ : psSplit κ e (.inl s) ≠ psSplit κ e (.inl p') := fun h' =>
          hs (Sum.inl_injective ((psSplit κ e).injective h'))
        have hne₂ : psSplit κ e (.inl s) ≠ psSplit κ e (.inr q') := fun h' =>
          Sum.inl_ne_inr ((psSplit κ e).injective h')
        obtain ⟨t', rfl⟩ := H.ps_left fun ht => H.left s.1 ((H.photon _ _ h hne₁ hne₂).2 ht)
        exact ⟨.inr t', rfl⟩

omit H in
theorem liftR_inl_zero : pModelEquiv e (liftR e p' (.inl 0)) = .inl 0 := by
  simp [liftR]

omit H in
theorem liftR_inl_one :
    pModelEquiv e (liftR e p' (.inl 1)) = .inr (psSplit κ e (.inl p')) := by
  simp [liftR]

omit H in
theorem liftR_inr (s : Wick.PhotonSlot (rightKinds κ e)) :
    pModelEquiv e (liftR e p' (.inr s)) = .inr (psSplit κ e (.inr s)) := rfl

theorem closP₂ (y : Fin 2 ⊕ Wick.PhotonSlot (rightKinds κ e)) :
    ∃ y', C.1.2 (pModelEquiv e (liftR e p' y)) = pModelEquiv e (liftR e p' y') := by
  rcases y with i | s
  · fin_cases i
    · rw [show ((⟨0, by omega⟩ : Fin 2)) = 0 from rfl, liftR_inl_zero]
      obtain ⟨a, ha⟩ := ext_eq (C := C)
      obtain ⟨a', rfl⟩ := H.ps_right (H.ext a ha)
      exact ⟨.inr a', ha⟩
    · rw [show ((⟨1, by omega⟩ : Fin 2)) = 1 from rfl, liftR_inl_one]
      exact ⟨.inr q', H.pq⟩
  · rw [liftR_inr]
    by_cases hs : s = q'
    · subst hs
      exact ⟨.inl 1, by rw [liftR_inl_one, H.qp]⟩
    · rcases h : C.1.2 (.inr (psSplit κ e (.inr s))) with j | t
      · exact ⟨.inl 0, by rw [liftR_inl_zero, Subsingleton.elim j 0]⟩
      · have hne₁ : psSplit κ e (.inr s) ≠ psSplit κ e (.inl p') := fun h' =>
          Sum.inr_ne_inl ((psSplit κ e).injective h')
        have hne₂ : psSplit κ e (.inr s) ≠ psSplit κ e (.inr q') := fun h' =>
          hs (Sum.inr_injective ((psSplit κ e).injective h'))
        obtain ⟨t', rfl⟩ := H.ps_right ((H.photon _ _ h hne₁ hne₂).1 (H.right s.1))
        exact ⟨.inr t', rfl⟩

/-! ### The pieces -/

/-- **The pieces of the cut glue back to `C`.** -/
theorem exists_glueP : ∃ (C₁ : Contraction 1 1 (leftKinds κ e))
    (C₂ : Contraction 0 2 (rightKinds κ e)) (w₁ : Wick.PhotonSlot (rightKinds κ e)),
    glueP e C₁ C₂ = C ∧ extSlot C₁ = p' ∧ C₂.1.2 (.inl 0) = .inr w₁ ∧
      C₂.1.2 (.inl 1) = .inr q' := by
  obtain ⟨σ₁, hσ₁⟩ := peelP_perm_restrict (fun z => fL κ e 1 (.inl z))
    (fun z z' h => Sum.inl_injective ((fL κ e 1).injective h)) C.1.1 H.closF₁
  obtain ⟨σ₂, hσ₂⟩ := peelP_perm_restrict (fun z => fL κ e 1 (.inr z))
    (fun z z' h => Sum.inr_injective ((fL κ e 1).injective h)) C.1.1 H.closF₂
  obtain ⟨τ₁, hτ₁, hτ₁'⟩ := peelP_invol_restrict (peelPEnc₁ e q') (peelPEnc₁_injective q')
    C.1.2 C.2 H.closP₁
  obtain ⟨τ₂, hτ₂, hτ₂'⟩ := peelP_invol_restrict (fun y => pModelEquiv e (liftR e p' y))
    (fun y y' h => liftR_injective e p' ((pModelEquiv e).injective h)) C.1.2 C.2 H.closP₂
  set C₁ : Contraction 1 1 (leftKinds κ e) := ⟨(σ₁, τ₁), hτ₁'⟩
  set C₂ : Contraction 0 2 (rightKinds κ e) := ⟨(σ₂, τ₂), hτ₂'⟩
  have h₁ : C₁.1.2 (.inl 0) = .inr p' := peelPEnc₁_injective q' ((hτ₁ _).trans H.qp)
  have hext : extSlot C₁ = p' := Sum.inr_injective ((extSlot_spec C₁).symm.trans h₁)
  obtain ⟨a, ha⟩ := ext_eq (C := C)
  obtain ⟨a', rfl⟩ := H.ps_right (H.ext a ha)
  have hw₁ : C₂.1.2 (.inl 0) = .inr a' := liftR_injective e p' ((pModelEquiv e).injective
    ((hτ₂ _).trans (by rw [liftR_inl_zero]; exact ha)))
  have hw₂ : C₂.1.2 (.inl 1) = .inr q' := liftR_injective e p' ((pModelEquiv e).injective
    ((hτ₂ _).trans (by rw [liftR_inl_one]; exact H.pq)))
  refine ⟨C₁, C₂, a', Subtype.ext (Prod.ext (Equiv.ext fun x => ?_) (Equiv.ext fun x => ?_)),
    hext, hw₁, hw₂⟩
  · obtain ⟨y, rfl⟩ := (fL κ e 1).surjective x
    rcases y with z | (i | t)
    · rw [glueP_fermion_left]
      exact hσ₁ z
    · exact i.elim0
    · rw [fL_inr_inr, glueP_fermion_right]
      exact hσ₂ (.inr t)
  · obtain ⟨y, rfl⟩ := (pModelEquiv e).surjective x
    change gluePPhotons e C₁ C₂ _ = _
    rw [gluePPhotons_apply]
    rcases y with i | s | s
    · simp only [photonModel, hext]
      rw [hτ₂, liftR_inl_zero, Subsingleton.elim i 0]
      rfl
    · by_cases hs : s = extSlot C₁
      · simp only [photonModel, hs, ite_true, hext]
        rw [hτ₂, liftR_inl_one]
        rfl
      · obtain ⟨s', hs', -, -⟩ := photonPair_left e C₁ hs
        rw [photonModel_left e C₁ C₂ hs hs']
        have := hτ₁ (.inr s)
        rw [show τ₁ (.inr s) = .inr s' from hs'] at this
        exact this
    · simp only [photonModel, hext]
      exact hτ₂ (.inr s)

end PeelPCutData

/-- **Cutting a contraction at a photon-leg cut**: for a pair `p, q` of contracted photon fields
and a set `T` holding `q` and not `p`, closed under the other pairs, holding the photon external
and none of the fermion externals, there are a split `e`, increasing on each piece and with right
image `T`, and pieces that glue back to `C`. -/
theorem peelP_exists_glueP (C : Contraction 1 1 κ) {p q : Wick.PhotonSlot κ} (T : Fin N → Prop)
    (hpq : C.1.2 (.inr p) = .inr q) (hp : ¬ T p.1) (hq : T q.1)
    (hferm : ∀ v t, C.1.1 (.inr v) = .inr t → (T v.1 ↔ T t.1))
    (hph : ∀ s t, C.1.2 (.inr s) = .inr t → s ≠ p → s ≠ q → (T s.1 ↔ T t.1))
    (hout : ∀ x, C.1.1 (.inl 0) = .inr x → ¬ T x.1)
    (hin : ∀ y, C.1.1 (.inr y) = .inl 0 → ¬ T y.1)
    (hext : ∀ a, C.1.2 (.inl 0) = .inr a → T a.1) :
    ∃ (N₁ N₂ : ℕ) (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N) (C₁ : Contraction 1 1 (leftKinds κ e))
      (C₂ : Contraction 0 2 (rightKinds κ e)) (w₁ w₂ : Wick.PhotonSlot (rightKinds κ e)),
      N₁ + N₂ = N ∧ IsShuffle e ∧ glueP e C₁ C₂ = C ∧ C₂.1.2 (.inl 0) = .inr w₁ ∧
      C₂.1.2 (.inl 1) = .inr w₂ ∧ p = psSplit κ e (.inl (extSlot C₁)) ∧
      q = psSplit κ e (.inr w₂) ∧ ∀ v, T v ↔ ∃ r, e (.inr r) = v := by
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
  obtain ⟨p', hp'⟩ : ∃ p', p = psSplit κ e (.inl p') := by
    rcases hx : (psSplit κ e).symm p with p' | r
    · exact ⟨p', by rw [← hx, Equiv.apply_symm_apply]⟩
    · have hpr : p = psSplit κ e (.inr r) := by rw [← hx, Equiv.apply_symm_apply]
      rw [hpr] at hp
      exact absurd (hR r.1) hp
  obtain ⟨q', hq'⟩ : ∃ q', q = psSplit κ e (.inr q') := by
    rcases hx : (psSplit κ e).symm q with s' | q'
    · have hqs : q = psSplit κ e (.inl s') := by rw [← hx, Equiv.apply_symm_apply]
      rw [hqs] at hq
      exact absurd hq (hL s'.1)
    · exact ⟨q', by rw [← hx, Equiv.apply_symm_apply]⟩
  subst hp' hq'
  have H : PeelPCutData C e p' q' T := ⟨hpq, hferm, hph, hout, hin, hext, hL, hR⟩
  obtain ⟨C₁, C₂, w₁, hglue, hext', hw₁, hw₂⟩ := H.exists_glueP
  refine ⟨_, _, e, C₁, C₂, w₁, q', ?_, ⟨(s.orderEmbOfFin rfl).strictMono,
    (sᶜ.orderEmbOfFin rfl).strictMono⟩, hglue, hw₁, hw₂, by rw [hext'], rfl,
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
