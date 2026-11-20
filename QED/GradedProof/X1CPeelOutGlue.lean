/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CPeelOutDefs
public import QED.GradedProof.X1CCountOut
public import QED.GradedProof.X1CLinesOut

/-!
# (X₁) piece C: the out-leg glue is reducible, and its peeled set is the self-energy

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (the graph theory of the out-leg peel); the mirror of
`X1CPeelGlue`. For `G = glueOut e C₁ C₂` with a shuffle `e`, the bridge `peelOutBridge` (from the
out-vertex `a` of `C₁` to the in-vertex `c` of the self-energy `C₂`, head `c`):

* `peelOut_glueOut_outCut`: the bridge is an out-leg cut; `peelOut_glueOut_side`: its head side
  is the vertex set of `C₂`, `(countLeftImage e)ᶜ`.
* `peelOut_glueOut_side_subset`: if `C₂` is 1PI, the head side of every out-cut contains the
  vertices of `C₂` (a cut of `C₁` has the out-vertex, a vertex of `C₂`, on its head side);
  hence **`peelOut_glueOut`**: `peelOut G = (countLeftImage e)ᶜ`.
* `peelOut_glueOut_attached`, `peelOut_glueOut_tadFree`: attached and tadpole-free pieces glue
  to an attached tadpole-free contraction.
* `peelOut_glueOut_notRedIn`: no in-cut survives the glue: an in-cut of `G` in `C₁` would be one
  of `C₁`, the lines of `C₂` are not bridges, and the tail side of the bridge holds the photon
  external of `C₁`.
* `peelOut_hmem`, `peelOut_hpeel`: the hypotheses `hmem` of `selectedPart_peelOut` and `hpeel`
  of `countGlueOut_injOn` for the selections `peelOutSelH`, `peelRedOut`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line FermionLine PhotonLine Joined IsBridge VerticesConnected
  ExternalsAttached IsOnePI)
open Relation Finset
open QED.Graded

variable {N N₁ N₂ nA : ℕ} {κ : Fin N → Wick.VertexKind} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}
  (C₁ : Contraction 1 nA (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e))

/-! ### The externals of the glue -/

theorem peelOut_glueOut_out {x : Wick.FermionVertex (rightKinds κ e)}
    (hx : C₂.1.1 (.inl 0) = .inr x) :
    (glueOut e C₁ C₂).1.1 (.inl 0) = .inr (fvSplit κ e (.inr x)) :=
  glueOut_right C₁ C₂ (x := .inl 0) hx

theorem peelOut_glueOut_in {y : Wick.FermionVertex (leftKinds κ e)}
    (hy : C₁.1.1 (.inr y) = .inl 0) :
    (glueOut e C₁ C₂).1.1 (.inr (fvSplit κ e (.inl y))) = .inl 0 := by
  rw [glueOut_left, hy]
  rfl

theorem peelOut_glueOut_photon (j : Fin nA) :
    (glueOut e C₁ C₂).1.2 (.inl j) = pL κ e nA (.inl (C₁.1.2 (.inl j))) :=
  gluePhotons_left C₁ C₂ (.inl j)

theorem peelOut_glueOut_photonExt {j : Fin nA} {a' : Wick.PhotonSlot κ}
    (h : (glueOut e C₁ C₂).1.2 (.inl j) = .inr a') :
    ∃ a₁, C₁.1.2 (.inl j) = .inr a₁ ∧ a'.1 = e (.inl a₁.1) := by
  rw [peelOut_glueOut_photon] at h
  rcases h₁ : C₁.1.2 (.inl j) with j' | a₁
  · rw [h₁, pL_inl_inl] at h
    exact absurd h Sum.inl_ne_inr
  · rw [h₁, pL_inl_inr] at h
    exact ⟨a₁, rfl, by rw [← Sum.inr_injective h]; rfl⟩

theorem peelOut_glueOut_photonExt' {j : Fin nA} {a₁ : Wick.PhotonSlot (leftKinds κ e)}
    (h : C₁.1.2 (.inl j) = .inr a₁) :
    (glueOut e C₁ C₂).1.2 (.inl j) = .inr (psSplit κ e (.inl a₁)) := by
  rw [peelOut_glueOut_photon, h, pL_inl_inr]

/-- **The out-leg glue of attached pieces is attached.** -/
theorem peelOut_glueOut_attached (hA₁ : ExternalsAttached C₁) (hA₂ : ExternalsAttached C₂) :
    ExternalsAttached (glueOut e C₁ C₂) := by
  obtain ⟨x, hx⟩ := count_exists_out hA₂
  refine ⟨fun i j h => ?_, fun i j h => ?_⟩
  · rw [Subsingleton.elim i 0, peelOut_glueOut_out C₁ C₂ hx] at h
    exact Sum.inr_ne_inl h
  · rw [peelOut_glueOut_photon] at h
    rcases h₁ : C₁.1.2 (.inl i) with j' | a₁
    · exact hA₁.2 i j' h₁
    · rw [h₁, pL_inl_inr] at h
      exact Sum.inr_ne_inl h

/-! ### The bridge of the glue -/

variable {a : Wick.FermionVertex (leftKinds κ e)} {c : Wick.FermionVertex (rightKinds κ e)}
  (ha : C₁.1.1 (.inl 0) = .inr a) (hc : C₂.1.1 (.inr c) = .inl 0) (he : IsShuffle e)

/-- The bridge of `glueOut` as a fermion line. -/
def peelOutBridge : FermionLine (glueOut e C₁ C₂) := fermionLineOut C₁ C₂ ha hc (.inr (.inr ()))

theorem peelOutBridge_eq :
    (lineSplitOut C₁ C₂ ha hc he).peelBridge = .inl (peelOutBridge C₁ C₂ ha hc) := rfl

theorem peelOutBridge_head : (peelOutBridge C₁ C₂ ha hc).1.1 = e (.inr c.1) := rfl

theorem peelOutBridge_tail : (peelOutBridge C₁ C₂ ha hc).tail.1 = e (.inl a.1) := by
  rw [peelOutBridge, fermionLineOut_bridge_tail]
  rfl

include he in
theorem peelOut_glueOut_head_right {v : Fin N}
    (h : ReflTransGen (Joined (glueOut e C₁ C₂) {.inl (peelOutBridge C₁ C₂ ha hc)})
      (e (.inr c.1)) v) : ∃ r, v = e (.inr r) :=
  (lineSplitOut C₁ C₂ ha hc he).peel_proj_right_mem (a := a.1) (c := c.1) (.inl ⟨rfl, rfl⟩)
    (S := {.inl (peelOutBridge C₁ C₂ ha hc)}) (Set.mem_singleton _) h

include he in
/-- **The bridge of the out-leg glue is an out-leg cut.** -/
theorem peelOut_glueOut_outCut : PeelOutCut (glueOut e C₁ C₂) (peelOutBridge C₁ C₂ ha hc) := by
  refine ⟨(lineSplitOut C₁ C₂ ha hc he).peel_isBridge_bridge (.inl ⟨rfl, rfl⟩),
    fun j a' hj hr => ?_⟩
  rw [peelOutBridge_head] at hr
  obtain ⟨r, hr⟩ := peelOut_glueOut_head_right C₁ C₂ ha hc he hr
  obtain ⟨a₁, -, ha₁⟩ := peelOut_glueOut_photonExt C₁ C₂ hj
  rw [ha₁] at hr
  exact Sum.inl_ne_inr (e.injective hr)

include he in
/-- **The head side of the bridge is the vertex set of the self-energy.** -/
theorem peelOut_glueOut_side (hV₂ : VerticesConnected C₂) :
    peelSide (glueOut e C₁ C₂) (.inl (peelOutBridge C₁ C₂ ha hc))
      (peelOutBridge C₁ C₂ ha hc).1.1 = (countLeftImage e)ᶜ := by
  ext v
  rw [mem_peelSide, peelOutBridge_head, mem_compl, mem_countLeftImage]
  constructor
  · rintro h ⟨t, ht⟩
    obtain ⟨r, rfl⟩ := peelOut_glueOut_head_right C₁ C₂ ha hc he h
    exact Sum.inl_ne_inr (e.injective ht)
  · intro h
    obtain ⟨x, rfl⟩ := e.surjective v
    rcases x with t | r
    · exact absurd ⟨t, rfl⟩ h
    · refine (lineSplitOut C₁ C₂ ha hc he).peel_lift_right' (fun g hg => ?_) (hV₂ c.1 r)
      have := (lineSplitOut C₁ C₂ ha hc he).equiv.injective (a₁ := .inr (.inl g))
        (a₂ := .inr (.inr ())) hg
      exact Sum.inl_ne_inr (Sum.inr_injective this)

include he in
/-- **Every out-cut of the glue has the self-energy on its head side** when `C₂` is 1PI. -/
theorem peelOut_glueOut_side_subset (hC₂ : IsOnePI C₂) (f : FermionLine (glueOut e C₁ C₂))
    (hf : PeelOutCut (glueOut e C₁ C₂) f) :
    peelSide (glueOut e C₁ C₂) (.inl (peelOutBridge C₁ C₂ ha hc))
        (peelOutBridge C₁ C₂ ha hc).1.1 ⊆ peelSide (glueOut e C₁ C₂) (.inl f) f.1.1 := by
  set L := lineSplitOut C₁ C₂ ha hc he with hL
  intro v hv
  obtain ⟨x, hx⟩ := L.equiv.surjective (.inl f)
  rcases x with g | g | ⟨⟩
  · rw [peelOut_glueOut_side C₁ C₂ ha hc he hC₂.2.1] at hv
    obtain ⟨r, rfl⟩ : ∃ r, v = e (.inr r) := by
      obtain ⟨x, rfl⟩ := e.surjective v
      rcases x with t | r
      · exact absurd (mem_countLeftImage.2 ⟨t, rfl⟩) (mem_compl.1 hv)
      · exact ⟨r, rfl⟩
    obtain ⟨y, hy⟩ := count_exists_out hC₂.1
    rw [mem_peelSide]
    refine (peel_head_reach_out f hf.1 (peelOut_glueOut_out C₁ C₂ hy)).trans
      (L.peel_lift_right' (fun g' hg' => ?_) (hC₂.2.1 y.1 r))
    exact Sum.inr_ne_inl (L.equiv.injective ((Set.mem_singleton_iff.1 hg').trans hx.symm))
  · have hb : IsBridge (L.equiv (.inr (.inl g))) := by rw [hx]; exact hf.1
    exact absurd ((L.peel_isBridge_right_iff (.inl ⟨rfl, rfl⟩) g).1 hb) (hC₂.2.2 g)
  · obtain rfl : f = peelOutBridge C₁ C₂ ha hc := Sum.inl_injective hx.symm
    exact hv

include ha hc he in
/-- **The peeled set of the out-leg glue is the vertex set of the self-energy.** -/
theorem peelOut_glueOut (hC₂ : IsOnePI C₂) :
    peelOut (glueOut e C₁ C₂) = (countLeftImage e)ᶜ := by
  rw [peelOut_eq_of_forall (peelOut_glueOut_outCut C₁ C₂ ha hc he)
    (peelOut_glueOut_side_subset C₁ C₂ ha hc he hC₂), peelOut_glueOut_side C₁ C₂ ha hc he hC₂.2.1]

include ha hc he in
/-- **The out-leg glue of a tadpole-free contraction and a 1PI self-energy is tadpole-free.** -/
theorem peelOut_glueOut_tadFree (hC₂ : IsOnePI C₂) (hT₁ : PeelTadFree C₁) :
    PeelTadFree (glueOut e C₁ C₂) := by
  set L := lineSplitOut C₁ C₂ ha hc he with hL
  intro g hg w hw
  obtain ⟨x, hx⟩ := L.equiv.surjective (.inr g)
  rcases x with (f₁ | p₁) | g₂ | ⟨⟩
  · exact (Sum.inl_ne_inr (a := fermionLineOutEquiv C₁ C₂ ha hc (.inl f₁)) hx).elim
  · have hb₁ : IsBridge (.inr p₁ : Line C₁) :=
      (L.peel_isBridge_left_iff (.inl ⟨rfl, rfl⟩) _).1 (by rw [hx]; exact hg)
    have hends := L.ends_left (.inr p₁)
    rw [hx] at hends
    simp only [Line.ends, Prod.mk.injEq] at hends
    obtain ⟨w₁, hw₁, rfl⟩ : ∃ w₁, (w₁ = p₁.1.1 ∨ w₁ = p₁.head.1) ∧ w = e (.inl w₁) := by
      rcases hw with rfl | rfl
      · exact ⟨_, .inl rfl, hends.1⟩
      · exact ⟨_, .inr rfl, hends.2⟩
    have hS : L.peelSet₁ {.inr g} = {.inr p₁} := by rw [← hx, L.peelSet₁_singleton]
    have hlift : ∀ v₁, tadComp C₁ p₁ w₁ v₁ →
        tadComp (glueOut e C₁ C₂) g (e (.inl w₁)) (e (.inl v₁)) := fun v₁ h => by
      unfold tadComp at h ⊢
      exact L.peel_lift_left (S := {.inr g}) (s := w₁) (t := v₁) (by rw [hS]; exact h)
    rcases hT₁ p₁ hb₁ w₁ hw₁ with ⟨s, hs, hr⟩ | ⟨s, hs, hr⟩ | ⟨j, a₁, hj, hr⟩
    · obtain rfl : s = a := Sum.inr_injective (hs.symm.trans ha)
      obtain ⟨x₂, hx₂⟩ := count_exists_out hC₂.1
      refine .inl ⟨_, peelOut_glueOut_out C₁ C₂ hx₂, ?_⟩
      have hbr : Joined (glueOut e C₁ C₂) {.inr g} (e (.inl s.1)) (e (.inr c.1)) :=
        ⟨L.peelBridge, fun h => Sum.inl_ne_inr (Set.mem_singleton_iff.1 h), .inl L.ends_bridge⟩
      refine ((hlift _ hr).tail hbr).trans (L.peel_lift_right' (fun g' hg' => ?_)
        (hC₂.2.1 c.1 x₂.1))
      have := L.equiv.injective ((Set.mem_singleton_iff.1 hg').trans hx.symm)
      exact Sum.inr_ne_inl this
    · exact .inr (.inl ⟨_, peelOut_glueOut_in C₁ C₂ hs, hlift _ hr⟩)
    · exact .inr (.inr ⟨j, _, peelOut_glueOut_photonExt' C₁ C₂ hj, hlift _ hr⟩)
  · have hb : IsBridge (L.equiv (.inr (.inl g₂))) := by rw [hx]; exact hg
    exact absurd ((L.peel_isBridge_right_iff (.inl ⟨rfl, rfl⟩) g₂).1 hb) (hC₂.2.2 g₂)
  · exact (Sum.inl_ne_inr (a := peelOutBridge C₁ C₂ ha hc) hx).elim

include ha hc he in
/-- **No in-cut survives the out-leg glue** of a contraction without in-cut, with a photon
external, and a 1PI self-energy. -/
theorem peelOut_glueOut_notRedIn (hC₂ : IsOnePI C₂) (hA₁ : ExternalsAttached C₁)
    (hV₁ : VerticesConnected C₁) (j₀ : Fin nA) (hR₁ : ¬ ∃ f, PeelInCut C₁ f) :
    ¬ ∃ f, PeelInCut (glueOut e C₁ C₂) f := by
  set L := lineSplitOut C₁ C₂ ha hc he with hL
  rintro ⟨f, hf⟩
  obtain ⟨x, hx⟩ := L.equiv.surjective (.inl f)
  rcases x with (f₁ | p₁) | g₂ | ⟨⟩
  · have hb₁ : IsBridge (L.equiv (.inl (.inl f₁))) := by rw [hx]; exact hf.1
    refine hR₁ ⟨f₁, (L.peel_isBridge_left_iff (.inl ⟨rfl, rfl⟩) _).1 hb₁,
      fun j a₁ hj hr => ?_⟩
    have hends := L.ends_left (.inl f₁)
    rw [hx] at hends
    simp only [Line.ends, Prod.mk.injEq] at hends
    have hS : L.peelSet₁ {.inl f} = {.inl f₁} := by rw [← hx, L.peelSet₁_singleton]
    have hr' := L.peel_lift_left (S := {.inl f}) (s := f₁.tail.1) (t := a₁.1)
      (by rw [hS]; exact hr)
    rw [← hends.1] at hr'
    exact hf.2 j _ (peelOut_glueOut_photonExt' C₁ C₂ hj) hr'
  · exact (Sum.inr_ne_inl (b := (photonLineSplit (C := glueOut e C₁ C₂) (C₁ := C₁) (C₂ := C₂)
      rfl he) (.inl p₁)) hx).elim
  · have hb : IsBridge (L.equiv (.inr (.inl g₂))) := by rw [hx]; exact hf.1
    exact absurd ((L.peel_isBridge_right_iff (.inl ⟨rfl, rfl⟩) g₂).1 hb) (hC₂.2.2 g₂)
  · obtain rfl : f = peelOutBridge C₁ C₂ ha hc := Sum.inl_injective hx.symm
    rcases hj : C₁.1.2 (.inl j₀) with j' | a₁
    · exact hA₁.2 j₀ j' hj
    · refine hf.2 j₀ _ (peelOut_glueOut_photonExt' C₁ C₂ hj) ?_
      rw [peelOutBridge_tail]
      refine L.peel_lift_left' (fun g' hg' => ?_) (hV₁ a.1 a₁.1)
      have := L.equiv.injective ((Set.mem_singleton_iff.1 hg').trans (peelOutBridge_eq C₁ C₂ ha hc
        he).symm)
      exact Sum.inl_ne_inr this

/-! ### The hypotheses `hmem` and `hpeel` of the out-leg peel -/

/-- **`hmem` of `selectedPart_peelOut`** for `peelOutSelH`, `peelRedOut`. -/
theorem peelOut_hmem {M : ℕ} {κ' : Fin M → Wick.VertexKind} (g : Grading κ') :
    ∀ x ∈ countIdxSet peelOutSelH (countOnePI (nf := 1) (nA := 0)) g,
      peelOutSelH (glueOut x.2.1 x.2.2.1 x.2.2.2) g ∧
        peelRedOut (glueOut x.2.1 x.2.2.1 x.2.2.2) g := by
  rintro ⟨p, e', C₁', C₂'⟩ hx
  obtain ⟨-, he', ⟨⟨hA₁, hV₁, hT₁⟩, hR₁⟩, hC₂⟩ := mem_countIdxSet.1 hx
  obtain ⟨a', ha'⟩ := count_exists_out hA₁
  obtain ⟨c', hc'⟩ := count_exists_in hC₂.1
  exact ⟨⟨⟨peelOut_glueOut_attached C₁' C₂' hA₁ hC₂.1,
      (lineSplitOut C₁' C₂' ha' hc' he').countOut_verticesConnected rfl rfl hV₁ hC₂.2.1,
      peelOut_glueOut_tadFree C₁' C₂' ha' hc' he' hC₂ hT₁⟩,
    peelOut_glueOut_notRedIn C₁' C₂' ha' hc' he' hC₂ hA₁ hV₁ 0 hR₁⟩,
    ⟨_, peelOut_glueOut_outCut C₁' C₂' ha' hc' he'⟩⟩

/-- **`hpeel` of `countGlueOut_injOn`** for `peelOutSelH` and `peelOut`. -/
theorem peelOut_hpeel {M : ℕ} {κ' : Fin M → Wick.VertexKind} (g : Grading κ') :
    ∀ x ∈ countIdxSet peelOutSelH (countOnePI (nf := 1) (nA := 0)) g,
      peelOut (glueOut x.2.1 x.2.2.1 x.2.2.2) = (countLeftImage x.2.1)ᶜ := by
  rintro ⟨p, e', C₁', C₂'⟩ hx
  obtain ⟨-, he', ⟨⟨hA₁, -, -⟩, -⟩, hC₂⟩ := mem_countIdxSet.1 hx
  obtain ⟨a', ha'⟩ := count_exists_out hA₁
  obtain ⟨c', hc'⟩ := count_exists_in hC₂.1
  exact peelOut_glueOut C₁' C₂' ha' hc' he' hC₂

end QED.GradedProof.X1C

end
