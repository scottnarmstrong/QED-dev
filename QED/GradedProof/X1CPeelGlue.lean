/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CPeelDefs
public import QED.GradedProof.X1CCountPeelIn

/-!
# (X₁) piece C: the in-leg glue is reducible, and its peeled set is the self-energy

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (the graph theory of the in-leg peel). For `G = glueIn e C₁ C₂`
with a shuffle `e`, the bridge `peelInBridge` (from the out-vertex `c` of the self-energy `C₂` to
the in-vertex `a` of `C₁`):

* `peel_glueIn_inCut`: the bridge is an in-leg cut; `peel_glueIn_side`: its tail side is the
  vertex set of `C₂`, `(countLeftImage e)ᶜ`.
* `peel_glueIn_side_subset`: if `C₂` is 1PI, the tail side of every in-cut contains the vertices
  of `C₂` (a cut of `C₁` has the in-vertex, hence all of `C₂`, on its tail side; `C₂` has no
  bridge); hence **`peelIn_glueIn`**: `peelIn G = (countLeftImage e)ᶜ`.
* `peel_glueIn_attached`, `peel_glueIn_tadFree`: the glue of an attached tadpole-free `C₁` and a
  1PI `C₂` is attached and tadpole-free (a photon bridge of `G` is one of `C₁`; an external of
  `C₁` on its side gives one of `G`, the in-vertex of `C₁` through the bridge and `C₂`).
* `peel_hmemIn`, `peel_hpeelIn`: the hypotheses `hmem` of `selectedPart_peelIn` and `hpeel` of
  `countGlueIn_injOn` for the selections `peelSelG`, `peelRedIn`.
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

theorem peel_glueIn_out {x : Wick.FermionVertex (leftKinds κ e)}
    (hx : C₁.1.1 (.inl 0) = .inr x) :
    (glueIn e C₁ C₂).1.1 (.inl 0) = .inr (fvSplit κ e (.inl x)) :=
  glueIn_left C₁ C₂ (x := .inl 0) hx

theorem peel_glueIn_in {y : Wick.FermionVertex (rightKinds κ e)}
    (hy : C₂.1.1 (.inr y) = .inl 0) :
    (glueIn e C₁ C₂).1.1 (.inr (fvSplit κ e (.inr y))) = .inl 0 := by
  rw [glueIn_right, hy]
  rfl

theorem peel_glueIn_photon (j : Fin nA) :
    (glueIn e C₁ C₂).1.2 (.inl j) = pL κ e nA (.inl (C₁.1.2 (.inl j))) :=
  gluePhotons_left C₁ C₂ (.inl j)

theorem peel_glueIn_photonExt {j : Fin nA} {a' : Wick.PhotonSlot κ}
    (h : (glueIn e C₁ C₂).1.2 (.inl j) = .inr a') :
    ∃ a₁, C₁.1.2 (.inl j) = .inr a₁ ∧ a'.1 = e (.inl a₁.1) := by
  rw [peel_glueIn_photon] at h
  rcases h₁ : C₁.1.2 (.inl j) with j' | a₁
  · rw [h₁, pL_inl_inl] at h
    exact absurd h Sum.inl_ne_inr
  · rw [h₁, pL_inl_inr] at h
    exact ⟨a₁, rfl, by rw [← Sum.inr_injective h]; rfl⟩

/-- **The in-leg glue of an attached contraction is attached.** -/
theorem peel_glueIn_attached (hA₁ : ExternalsAttached C₁) :
    ExternalsAttached (glueIn e C₁ C₂) := by
  obtain ⟨x, hx⟩ := count_exists_out hA₁
  refine ⟨fun i j h => ?_, fun i j h => ?_⟩
  · rw [Subsingleton.elim i 0, peel_glueIn_out C₁ C₂ hx] at h
    exact Sum.inr_ne_inl h
  · rw [peel_glueIn_photon] at h
    rcases h₁ : C₁.1.2 (.inl i) with j' | a₁
    · exact hA₁.2 i j' h₁
    · rw [h₁, pL_inl_inr] at h
      exact Sum.inr_ne_inl h

/-! ### The bridge of the glue -/

variable {a : Wick.FermionVertex (leftKinds κ e)} {c : Wick.FermionVertex (rightKinds κ e)}
  (ha : C₁.1.1 (.inr a) = .inl 0) (hc : C₂.1.1 (.inl 0) = .inr c) (he : IsShuffle e)

/-- The bridge of `glueIn` as a fermion line. -/
def peelInBridge : FermionLine (glueIn e C₁ C₂) := fermionLineIn C₁ C₂ ha hc (.inr (.inr ()))

theorem peelInBridge_eq :
    (lineSplitIn C₁ C₂ ha hc he).peelBridge = .inl (peelInBridge C₁ C₂ ha hc) := rfl

theorem peelInBridge_tail : (peelInBridge C₁ C₂ ha hc).tail.1 = e (.inr c.1) := by
  rw [peelInBridge, fermionLineIn_bridge_tail]
  rfl

include he in
theorem peel_glueIn_tail_right {v : Fin N}
    (h : ReflTransGen (Joined (glueIn e C₁ C₂) {.inl (peelInBridge C₁ C₂ ha hc)})
      (e (.inr c.1)) v) : ∃ r, v = e (.inr r) :=
  (lineSplitIn C₁ C₂ ha hc he).peel_proj_right_mem (a := a.1) (c := c.1) (.inr ⟨rfl, rfl⟩)
    (S := {.inl (peelInBridge C₁ C₂ ha hc)}) (Set.mem_singleton _) h

include he in
/-- **The bridge of the in-leg glue is an in-leg cut.** -/
theorem peel_glueIn_inCut : PeelInCut (glueIn e C₁ C₂) (peelInBridge C₁ C₂ ha hc) := by
  refine ⟨(lineSplitIn C₁ C₂ ha hc he).peel_isBridge_bridge (.inr ⟨rfl, rfl⟩),
    fun j a' hj hr => ?_⟩
  rw [peelInBridge_tail] at hr
  obtain ⟨r, hr⟩ := peel_glueIn_tail_right C₁ C₂ ha hc he hr
  obtain ⟨a₁, -, ha₁⟩ := peel_glueIn_photonExt C₁ C₂ hj
  rw [ha₁] at hr
  exact Sum.inl_ne_inr (e.injective hr)

include he in
/-- **The tail side of the bridge is the vertex set of the self-energy.** -/
theorem peel_glueIn_side (hV₂ : VerticesConnected C₂) :
    peelSide (glueIn e C₁ C₂) (.inl (peelInBridge C₁ C₂ ha hc))
      (peelInBridge C₁ C₂ ha hc).tail.1 = (countLeftImage e)ᶜ := by
  ext v
  rw [mem_peelSide, peelInBridge_tail, mem_compl, mem_countLeftImage]
  constructor
  · rintro h ⟨t, ht⟩
    obtain ⟨r, rfl⟩ := peel_glueIn_tail_right C₁ C₂ ha hc he h
    exact Sum.inl_ne_inr (e.injective ht)
  · intro h
    obtain ⟨x, rfl⟩ := e.surjective v
    rcases x with t | r
    · exact absurd ⟨t, rfl⟩ h
    · refine (lineSplitIn C₁ C₂ ha hc he).peel_lift_right' (fun g hg => ?_) (hV₂ c.1 r)
      have := (lineSplitIn C₁ C₂ ha hc he).equiv.injective (a₁ := .inr (.inl g))
        (a₂ := .inr (.inr ())) hg
      exact Sum.inl_ne_inr (Sum.inr_injective this)

include he in
/-- **Every in-cut of the glue has the self-energy on its tail side** when `C₂` is 1PI. -/
theorem peel_glueIn_side_subset (hC₂ : IsOnePI C₂) (f : FermionLine (glueIn e C₁ C₂))
    (hf : PeelInCut (glueIn e C₁ C₂) f) :
    peelSide (glueIn e C₁ C₂) (.inl (peelInBridge C₁ C₂ ha hc))
        (peelInBridge C₁ C₂ ha hc).tail.1 ⊆ peelSide (glueIn e C₁ C₂) (.inl f) f.tail.1 := by
  set L := lineSplitIn C₁ C₂ ha hc he with hL
  intro v hv
  obtain ⟨x, hx⟩ := L.equiv.surjective (.inl f)
  rcases x with g | g | ⟨⟩
  · rw [peel_glueIn_side C₁ C₂ ha hc he hC₂.2.1] at hv
    obtain ⟨r, rfl⟩ : ∃ r, v = e (.inr r) := by
      obtain ⟨x, rfl⟩ := e.surjective v
      rcases x with t | r
      · exact absurd (mem_countLeftImage.2 ⟨t, rfl⟩) (mem_compl.1 hv)
      · exact ⟨r, rfl⟩
    obtain ⟨y, hy⟩ := count_exists_in hC₂.1
    rw [mem_peelSide]
    refine (peel_tail_reach_in f hf.1 (peel_glueIn_in C₁ C₂ hy)).trans
      (L.peel_lift_right' (fun g' hg' => ?_) (hC₂.2.1 y.1 r))
    exact Sum.inr_ne_inl (L.equiv.injective ((Set.mem_singleton_iff.1 hg').trans hx.symm))
  · have hb : IsBridge (L.equiv (.inr (.inl g))) := by rw [hx]; exact hf.1
    exact absurd ((L.peel_isBridge_right_iff (.inr ⟨rfl, rfl⟩) g).1 hb) (hC₂.2.2 g)
  · obtain rfl : f = peelInBridge C₁ C₂ ha hc := Sum.inl_injective hx.symm
    exact hv

include ha hc he in
/-- **The peeled set of the in-leg glue is the vertex set of the self-energy.** -/
theorem peelIn_glueIn (hC₂ : IsOnePI C₂) :
    peelIn (glueIn e C₁ C₂) = (countLeftImage e)ᶜ := by
  rw [peelIn_eq_of_forall (peel_glueIn_inCut C₁ C₂ ha hc he)
    (peel_glueIn_side_subset C₁ C₂ ha hc he hC₂), peel_glueIn_side C₁ C₂ ha hc he hC₂.2.1]

include ha hc he in
/-- **The in-leg glue of a tadpole-free contraction and a 1PI self-energy is tadpole-free.** -/
theorem peel_glueIn_tadFree (hC₂ : IsOnePI C₂) (hT₁ : PeelTadFree C₁) :
    PeelTadFree (glueIn e C₁ C₂) := by
  set L := lineSplitIn C₁ C₂ ha hc he with hL
  intro g hg w hw
  obtain ⟨x, hx⟩ := L.equiv.surjective (.inr g)
  rcases x with (f₁ | p₁) | g₂ | ⟨⟩
  · exact (Sum.inl_ne_inr (a := fermionLineInEquiv C₁ C₂ ha hc (.inl f₁)) hx).elim
  · have hb₁ : IsBridge (.inr p₁ : Line C₁) :=
      (L.peel_isBridge_left_iff (.inr ⟨rfl, rfl⟩) _).1 (by rw [hx]; exact hg)
    have hends := L.ends_left (.inr p₁)
    rw [hx] at hends
    simp only [Line.ends, Prod.mk.injEq] at hends
    obtain ⟨w₁, hw₁, rfl⟩ : ∃ w₁, (w₁ = p₁.1.1 ∨ w₁ = p₁.head.1) ∧ w = e (.inl w₁) := by
      rcases hw with rfl | rfl
      · exact ⟨_, .inl rfl, hends.1⟩
      · exact ⟨_, .inr rfl, hends.2⟩
    have hS : L.peelSet₁ {.inr g} = {.inr p₁} := by rw [← hx, L.peelSet₁_singleton]
    have hlift : ∀ v₁, tadComp C₁ p₁ w₁ v₁ →
        tadComp (glueIn e C₁ C₂) g (e (.inl w₁)) (e (.inl v₁)) := fun v₁ h => by
      unfold tadComp at h ⊢
      exact L.peel_lift_left (S := {.inr g}) (s := w₁) (t := v₁) (by rw [hS]; exact h)
    rcases hT₁ p₁ hb₁ w₁ hw₁ with ⟨s, hs, hr⟩ | ⟨s, hs, hr⟩ | ⟨j, a₁, hj, hr⟩
    · exact .inl ⟨_, peel_glueIn_out C₁ C₂ hs, hlift _ hr⟩
    · obtain rfl : s = a := Sum.inr_injective (C₁.1.1.injective (hs.trans ha.symm))
      obtain ⟨y, hy⟩ := count_exists_in hC₂.1
      refine .inr (.inl ⟨_, peel_glueIn_in C₁ C₂ hy, ?_⟩)
      have hbr : Joined (glueIn e C₁ C₂) {.inr g} (e (.inl s.1)) (e (.inr c.1)) :=
        ⟨L.peelBridge, fun h => Sum.inl_ne_inr (Set.mem_singleton_iff.1 h), .inr L.ends_bridge⟩
      refine ((hlift _ hr).tail hbr).trans (L.peel_lift_right' (fun g' hg' => ?_)
        (hC₂.2.1 c.1 y.1))
      have := L.equiv.injective ((Set.mem_singleton_iff.1 hg').trans hx.symm)
      exact Sum.inr_ne_inl this
    · have hj' : (glueIn e C₁ C₂).1.2 (.inl j) = .inr (psSplit κ e (.inl a₁)) := by
        rw [peel_glueIn_photon, hj, pL_inl_inr]
      exact .inr (.inr ⟨j, _, hj', hlift _ hr⟩)
  · have hb : IsBridge (L.equiv (.inr (.inl g₂))) := by rw [hx]; exact hg
    exact absurd ((L.peel_isBridge_right_iff (.inr ⟨rfl, rfl⟩) g₂).1 hb) (hC₂.2.2 g₂)
  · exact (Sum.inl_ne_inr (a := peelInBridge C₁ C₂ ha hc) hx).elim

/-! ### The hypotheses `hmem` and `hpeel` of the in-leg peel -/

/-- **`hmem` of `selectedPart_peelIn`** for `peelSelG`, `peelRedIn`. -/
theorem peel_hmemIn {M : ℕ} {κ' : Fin M → Wick.VertexKind} (g : Grading κ') :
    ∀ x ∈ countIdxSet peelSelG (countOnePI (nf := 1) (nA := 0)) g,
      peelSelG (glueIn x.2.1 x.2.2.1 x.2.2.2) g ∧ peelRedIn (glueIn x.2.1 x.2.2.1 x.2.2.2) g := by
  rintro ⟨p, e', C₁', C₂'⟩ hx
  obtain ⟨-, he', ⟨hA₁, hV₁, hT₁⟩, hC₂⟩ := mem_countIdxSet.1 hx
  obtain ⟨a', ha'⟩ := count_exists_in hA₁
  obtain ⟨c', hc'⟩ := count_exists_out hC₂.1
  exact ⟨⟨peel_glueIn_attached C₁' C₂' hA₁, LineSplit.count_verticesConnected
      (lineSplitIn C₁' C₂' ha' hc' he') rfl rfl hV₁ hC₂.2.1,
    peel_glueIn_tadFree C₁' C₂' ha' hc' he' hC₂ hT₁⟩, ⟨_, peel_glueIn_inCut C₁' C₂' ha' hc' he'⟩⟩

/-- **`hpeel` of `countGlueIn_injOn`** for `peelSelG` and `peelIn`. -/
theorem peel_hpeelIn {M : ℕ} {κ' : Fin M → Wick.VertexKind} (g : Grading κ') :
    ∀ x ∈ countIdxSet peelSelG (countOnePI (nf := 1) (nA := 0)) g,
      peelIn (glueIn x.2.1 x.2.2.1 x.2.2.2) = (countLeftImage x.2.1)ᶜ := by
  rintro ⟨p, e', C₁', C₂'⟩ hx
  obtain ⟨-, he', ⟨hA₁, -, -⟩, hC₂⟩ := mem_countIdxSet.1 hx
  obtain ⟨a', ha'⟩ := count_exists_in hA₁
  obtain ⟨c', hc'⟩ := count_exists_out hC₂.1
  exact peelIn_glueIn C₁' C₂' ha' hc' he' hC₂

end QED.GradedProof.X1C

end
