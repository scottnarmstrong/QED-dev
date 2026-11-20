/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CPeelGlue
public import QED.GradedProof.X1CPeelRestrict

/-!
# (X₁) piece C: the pieces of a reducible contraction

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (the graph theory of the in-leg peel). For a glue
`G = glueIn e C₁ C₂` (bridge from the out-vertex `c` of `C₂` to the in-vertex `a` of `C₁`):

* `peel_attached_left`, `peel_attached_right`: the pieces are attached when `G` is;
* `peel_tadFree_left`: `C₁` is tadpole-free when `G` is (a side of a photon bridge of `C₁`
  in `G` that leaves `C₁` passes the bridge, so it holds the in-vertex `a` of `C₁`);
* `peel_onePI_right`: `C₂` is 1PI when `G` is attached, connected and tadpole-free and no in-cut
  of `G` has fewer than `N₂` vertices on its tail side: a photon bridge of `C₂` would have every
  external on one side (they are all joined to the out-vertex without it), a fermion bridge of
  `C₂` would be an in-cut with a smaller tail side.

**`peel_hsurjIn`**: the hypothesis `hsurj` of `selectedPart_peelIn` for `peelSelG`, `peelRedIn`:
cut a reducible contraction at an in-cut with fewest vertices on its tail side
(`peel_exists_glueIn`).
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line FermionLine PhotonLine Joined IsBridge VerticesConnected
  ExternalsAttached IsOnePI)
open QED.Graded
open Relation Finset

theorem peel_mem_compl_countLeftImage {N N₁ N₂ : ℕ} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}
    {v : Fin N} : v ∈ (countLeftImage e)ᶜ ↔ ∃ r, e (.inr r) = v := by
  rw [mem_compl, mem_countLeftImage]
  obtain ⟨x, rfl⟩ := e.surjective v
  rcases x with t | t
  · exact ⟨fun h => absurd ⟨t, rfl⟩ h, fun ⟨r, hr⟩ => absurd (e.injective hr) Sum.inr_ne_inl⟩
  · exact ⟨fun _ => ⟨t, rfl⟩, fun _ ⟨s, hs⟩ => Sum.inl_ne_inr (e.injective hs)⟩

variable {N N₁ N₂ nA : ℕ} {κ : Fin N → Wick.VertexKind} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}
  (C₁ : Contraction 1 nA (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e))
  {a : Wick.FermionVertex (leftKinds κ e)} {c : Wick.FermionVertex (rightKinds κ e)}
  (ha : C₁.1.1 (.inr a) = .inl 0) (hc : C₂.1.1 (.inl 0) = .inr c) (he : IsShuffle e)

include ha in
theorem peel_attached_left (hA : ExternalsAttached (glueIn e C₁ C₂)) : ExternalsAttached C₁ := by
  refine ⟨fun i j h => ?_, fun i j h => ?_⟩
  · rw [Subsingleton.elim i 0, Subsingleton.elim j 0] at h
    exact Sum.inl_ne_inr (C₁.1.1.injective (h.trans ha.symm))
  · have h' := peel_glueIn_photon C₁ C₂ i
    rw [h, pL_inl_inl] at h'
    exact hA.2 i j h'

include hc in
theorem peel_attached_right : ExternalsAttached C₂ := by
  refine ⟨fun i j h => ?_, fun i => i.elim0⟩
  rw [Subsingleton.elim i 0, hc] at h
  exact Sum.inr_ne_inl h

include ha hc he in
/-- **The left piece of a tadpole-free glue is tadpole-free.** -/
theorem peel_tadFree_left (hA₁ : ExternalsAttached C₁) (hT : PeelTadFree (glueIn e C₁ C₂)) :
    PeelTadFree C₁ := by
  set L := lineSplitIn C₁ C₂ ha hc he with hL
  intro p₁ hb₁ w₁ hw₁
  obtain ⟨g, hg⟩ : ∃ g, L.equiv (.inl (.inr p₁)) = .inr g := ⟨_, rfl⟩
  have hbG : IsBridge (.inr g : Line (glueIn e C₁ C₂)) := by
    rw [← hg]; exact (L.peel_isBridge_left_iff (.inr ⟨rfl, rfl⟩) _).2 hb₁
  have hends := L.ends_left (.inr p₁)
  rw [hg] at hends
  simp only [Line.ends, Prod.mk.injEq] at hends
  have hwG : e (.inl w₁) = g.1.1 ∨ e (.inl w₁) = g.head.1 := by
    rcases hw₁ with rfl | rfl
    · exact .inl hends.1.symm
    · exact .inr hends.2.symm
  have hS : L.peelSet₁ {.inr g} = {.inr p₁} := by rw [← hg, L.peelSet₁_singleton]
  have hproj : ∀ v, tadComp (glueIn e C₁ C₂) g (e (.inl w₁)) v →
      Sum.elim (fun s' => tadComp C₁ p₁ w₁ s') (fun _ => tadComp C₁ p₁ w₁ a.1) (e.symm v) := by
    intro v hv
    have := L.peel_proj_left (.inr ⟨rfl, rfl⟩) hv
    rw [hS] at this
    rcases hx : e.symm v with s' | r <;> rw [hx] at this
    · exact this
    · exact this.2
  have hleft : ∀ s', tadComp (glueIn e C₁ C₂) g (e (.inl w₁)) (e (.inl s')) →
      tadComp C₁ p₁ w₁ s' := fun s' h => by simpa using hproj _ h
  rcases hT g hbG _ hwG with ⟨x, hx, hr⟩ | ⟨y, hy, hr⟩ | ⟨j, a', hj, hr⟩
  · obtain ⟨x₁, hx₁⟩ := count_exists_out hA₁
    rw [peel_glueIn_out C₁ C₂ hx₁] at hx
    cases Sum.inr_injective hx
    exact .inl ⟨x₁, hx₁, hleft _ hr⟩
  · obtain ⟨z, rfl⟩ := (fvSplit κ e).surjective y
    rcases z with s | r
    · rcases hs : C₁.1.1 (.inr s) with i | t
      · obtain rfl : s = a := Sum.inr_injective (C₁.1.1.injective
          (hs.trans ((congrArg Sum.inl (Subsingleton.elim i 0)).trans ha.symm)))
        exact .inr (.inl ⟨s, ha, hleft _ hr⟩)
      · rw [glueIn_left' C₁ C₂ hs] at hy
        exact absurd hy Sum.inr_ne_inl
    · have := hproj _ hr
      simp only [fvSplit_inr, Equiv.symm_apply_apply, Sum.elim_inr] at this
      exact .inr (.inl ⟨a, ha, this⟩)
  · obtain ⟨a₁, ha₁, ha'⟩ := peel_glueIn_photonExt C₁ C₂ hj
    rw [ha'] at hr
    exact .inr (.inr ⟨j, a₁, ha₁, hleft _ hr⟩)

/-- Every external vertex of the glue is joined to the out-vertex without any line of `C₂`. -/
theorem peel_ext_reach_out (hV₁ : VerticesConnected C₁)
    {x₁ : Wick.FermionVertex (leftKinds κ e)} (hx₁ : C₁.1.1 (.inl 0) = .inr x₁)
    {S : Set (Line (glueIn e C₁ C₂))} (hS₁ : ∀ g, (lineSplitIn C₁ C₂ ha hc he).equiv (.inl g) ∉ S)
    (hSf : ∀ f : FermionLine (glueIn e C₁ C₂), (.inl f : Line _) ∉ S) {T : Fin N → Prop}
    (hext : PeelExtAt (glueIn e C₁ C₂) T) :
    ∃ v, T v ∧ ReflTransGen (Joined (glueIn e C₁ C₂) S) v (e (.inl x₁.1)) := by
  have hx := peel_glueIn_out C₁ C₂ hx₁
  rcases hext with ⟨x, hx', hr⟩ | ⟨y, hy, hr⟩ | ⟨j, a', hj, hr⟩
  · rw [hx] at hx'
    cases Sum.inr_injective hx'
    exact ⟨_, hr, .refl⟩
  · exact ⟨_, hr, peel_reach_symm (peel_reach_out_in hx hy hSf)⟩
  · obtain ⟨a₁, -, ha'⟩ := peel_glueIn_photonExt C₁ C₂ hj
    refine ⟨_, hr, ?_⟩
    rw [ha']
    exact (lineSplitIn C₁ C₂ ha hc he).peel_lift_left' hS₁ (hV₁ a₁.1 x₁.1)

include ha hc he in
/-- **The right piece of a minimally cut glue is 1PI.** -/
theorem peel_onePI_right (hN : N₁ + N₂ = N) (hA : ExternalsAttached (glueIn e C₁ C₂))
    (hV : VerticesConnected (glueIn e C₁ C₂)) (hT : PeelTadFree (glueIn e C₁ C₂))
    (hmin : ∀ f', PeelInCut (glueIn e C₁ C₂) f' →
      N₂ ≤ (peelSide (glueIn e C₁ C₂) (.inl f') f'.tail.1).card) : IsOnePI C₂ := by
  set L := lineSplitIn C₁ C₂ ha hc he with hL
  have hb : (e (.inr c.1) = e (.inl a.1) ∧ e (.inl a.1) = e (.inr c.1)) ∨
      (e (.inr c.1) = e (.inr c.1) ∧ e (.inl a.1) = e (.inl a.1)) := .inr ⟨rfl, rfl⟩
  have hA₁ := peel_attached_left C₁ C₂ ha hA
  have hV₁ := L.peel_connected_left hb hV
  obtain ⟨x₁, hx₁⟩ := count_exists_out hA₁
  refine ⟨peel_attached_right C₂ hc, L.peel_connected_right hb hV, fun g₂ hb₂ => ?_⟩
  have hbG := (L.peel_isBridge_right_iff hb g₂).2 hb₂
  rcases g₂ with f₂ | p₂
  · obtain ⟨F, hF⟩ : ∃ F, L.equiv (.inr (.inl (.inl f₂))) = .inl F := ⟨_, rfl⟩
    rw [hF] at hbG
    have hends := L.ends_right (.inl f₂)
    rw [hF] at hends
    simp only [Line.ends, Prod.mk.injEq] at hends
    have hright : ∀ v, ReflTransGen (Joined (glueIn e C₁ C₂) {.inl F}) F.tail.1 v →
        ∃ r, e (.inr r) = v := by
      intro v hv
      obtain ⟨z, rfl⟩ := e.surjective v
      rcases z with s | r
      · refine absurd (peel_head_reach_out F hbG (peel_glueIn_out C₁ C₂ hx₁)) fun h => ?_
        refine peel_sides_disjoint hbG (hv.trans (L.peel_lift_left' (fun g hg => ?_)
          (hV₁ s x₁.1))) h
        exact Sum.inl_ne_inr (L.equiv.injective ((Set.mem_singleton_iff.1 hg).trans hF.symm))
      · exact ⟨r, rfl⟩
    have hcut : PeelInCut (glueIn e C₁ C₂) F := by
      refine ⟨hbG, fun j a' hj hr => ?_⟩
      obtain ⟨r, hr'⟩ := hright _ hr
      obtain ⟨a₁, -, ha'⟩ := peel_glueIn_photonExt C₁ C₂ hj
      rw [ha'] at hr'
      exact Sum.inr_ne_inl (e.injective hr')
    have hsub : peelSide (glueIn e C₁ C₂) (.inl F) F.tail.1 ⊂ (countLeftImage e)ᶜ := by
      refine ⟨fun v hv => peel_mem_compl_countLeftImage.2 (hright v (mem_peelSide.1 hv)),
        fun h => hbG ?_⟩
      have hh : F.1.1 ∈ (countLeftImage e)ᶜ := peel_mem_compl_countLeftImage.2
        ⟨f₂.1.1, hends.2.symm⟩
      exact mem_peelSide.1 (h hh)
    have hlt := card_lt_card hsub
    rw [card_compl_countLeftImage hN] at hlt
    exact absurd (hmin F hcut) (not_le.2 hlt)
  · obtain ⟨g, hg⟩ : ∃ g, L.equiv (.inr (.inl (.inr p₂))) = .inr g := ⟨_, rfl⟩
    rw [hg] at hbG
    have hS₁ : ∀ g', L.equiv (.inl g') ∉ ({.inr g} : Set (Line (glueIn e C₁ C₂))) :=
      fun g' hg' => Sum.inl_ne_inr (L.equiv.injective ((Set.mem_singleton_iff.1 hg').trans
        hg.symm))
    have hSf : ∀ f : FermionLine (glueIn e C₁ C₂),
        (.inl f : Line _) ∉ ({.inr g} : Set (Line (glueIn e C₁ C₂))) :=
      fun f hf => Sum.inl_ne_inr (Set.mem_singleton_iff.1 hf)
    have key : ∀ w, (w = g.1.1 ∨ w = g.head.1) →
        ReflTransGen (Joined (glueIn e C₁ C₂) {.inr g}) w (e (.inl x₁.1)) := by
      intro w hw
      obtain ⟨v, hv, hr⟩ := peel_ext_reach_out C₁ C₂ ha hc he hV₁ hx₁ hS₁ hSf
        (hT g hbG w hw)
      exact (show ReflTransGen _ w v from hv).trans hr
    exact hbG ((key _ (.inl rfl)).trans (peel_reach_symm (key _ (.inr rfl))))

/-- **`hsurj` of `selectedPart_peelIn`** for `peelSelG`, `peelRedIn`: a reducible contraction is
the in-leg glue of a selected contraction and a 1PI self-energy. -/
theorem peel_hsurjIn {M : ℕ} {κ' : Fin M → Wick.VertexKind} (g : Grading κ')
    (C : Contraction 1 1 κ') (hS : peelSelG C g) (hR : peelRedIn C g) :
    ∃ x ∈ countIdxSet peelSelG (countOnePI (nf := 1) (nA := 0)) g,
      glueIn x.2.1 x.2.2.1 x.2.2.2 = C := by
  obtain ⟨hA, hV, hT⟩ := hS
  obtain ⟨f, hf, hmin, -⟩ := peelIn_spec C hR
  obtain ⟨M₁, M₂, e', C₁', C₂', a', c', hN, he', hglue, ha', hc', hTe⟩ :=
    peel_exists_glueIn C f (ReflTransGen (Joined C {(.inl f : Line C)}) f.tail.1)
      (fun l hl => ⟨fun h => h.tail (peel_joined_ends l hl),
        fun h => h.tail (peel_joined_symm (peel_joined_ends l hl))⟩) .refl hf.1
      (fun _ hy => peel_tail_reach_in f hf.1 hy)
      (fun _ hx hT' => peel_sides_disjoint hf.1 hT' (peel_head_reach_out f hf.1 hx)) hf.2
      (fun i => hA.1 0 i)
  subst hglue
  have hside : peelSide (glueIn e' C₁' C₂') (.inl f) f.tail.1 = (countLeftImage e')ᶜ := by
    ext v
    rw [mem_peelSide, peel_mem_compl_countLeftImage, hTe]
  have hA₁ := peel_attached_left C₁' C₂' ha' hA
  have hV₁ := (lineSplitIn C₁' C₂' ha' hc' he').peel_connected_left (.inr ⟨rfl, rfl⟩) hV
  refine ⟨⟨(M₁, M₂), e', C₁', C₂'⟩, mem_countIdxSet.2 ⟨hN, he', ⟨hA₁, hV₁,
    peel_tadFree_left C₁' C₂' ha' hc' he' hA₁ hT⟩, peel_onePI_right C₁' C₂' ha' hc' he' hN hA
      hV hT fun f' hf' => ?_⟩, rfl⟩
  have := hmin f' hf'
  rwa [hside, card_compl_countLeftImage hN] at this

end QED.GradedProof.X1C

end
