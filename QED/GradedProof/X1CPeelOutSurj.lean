/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CPeelOutGlue
public import QED.GradedProof.X1CPeelOutRestrict
public import QED.GradedProof.X1CPeelSurj

/-!
# (X₁) piece C: the pieces of an out-leg reducible contraction

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (the graph theory of the out-leg peel); the mirror of
`X1CPeelSurj`. For a glue `G = glueOut e C₁ C₂` (bridge from the out-vertex `a` of `C₁` to the
in-vertex `c` of `C₂`):

* `peelOut_attached_left`, `peelOut_attached_right`: the pieces are attached when `G` is;
* `peelOut_tadFree_left`: `C₁` is tadpole-free when `G` is (a side of a photon bridge of `C₁`
  in `G` that leaves `C₁` passes the bridge, so it holds the out-vertex `a` of `C₁`);
* `peelOut_notRedIn_left`: `C₁` has no in-cut when `G` has none (an in-cut of `C₁` is one of
  `G`: a path of `G` from a vertex of `C₁` to a photon external projects to `C₁`);
* `peelOut_onePI_right`: `C₂` is 1PI when `G` is attached, connected and tadpole-free and no
  out-cut of `G` has fewer than `N₂` vertices on its head side: a photon bridge of `C₂` would
  have every external on one side (they are all joined to the in-vertex without it), a fermion
  bridge of `C₂` would be an out-cut with a smaller head side.

**`peelOut_hsurj`**: the hypothesis `hsurj` of `selectedPart_peelOut` for `peelOutSelH`,
`peelRedOut`: cut a reducible contraction at an out-cut with fewest vertices on its head side
(`peelOut_exists_glueOut`).
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line FermionLine PhotonLine Joined IsBridge VerticesConnected
  ExternalsAttached IsOnePI)
open QED.Graded
open Relation Finset

variable {N N₁ N₂ nA : ℕ} {κ : Fin N → Wick.VertexKind} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}
  (C₁ : Contraction 1 nA (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e))
  {a : Wick.FermionVertex (leftKinds κ e)} {c : Wick.FermionVertex (rightKinds κ e)}
  (ha : C₁.1.1 (.inl 0) = .inr a) (hc : C₂.1.1 (.inr c) = .inl 0) (he : IsShuffle e)

include ha in
theorem peelOut_attached_left (hA : ExternalsAttached (glueOut e C₁ C₂)) :
    ExternalsAttached C₁ := by
  refine ⟨fun i j h => ?_, fun i j h => ?_⟩
  · rw [Subsingleton.elim i 0, ha] at h
    exact Sum.inr_ne_inl h
  · have h' := peelOut_glueOut_photon C₁ C₂ i
    rw [h, pL_inl_inl] at h'
    exact hA.2 i j h'

include hc in
theorem peelOut_attached_right : ExternalsAttached C₂ := by
  refine ⟨fun i j h => ?_, fun i => i.elim0⟩
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0] at h
  exact Sum.inl_ne_inr (C₂.1.1.injective (h.trans hc.symm))

/-- The in-vertex of the glue is the in-vertex of the left piece. -/
theorem peelOut_glueOut_in_eq {y₁ : Wick.FermionVertex (leftKinds κ e)}
    (hy₁ : C₁.1.1 (.inr y₁) = .inl 0) {y : Wick.FermionVertex κ}
    (hy : (glueOut e C₁ C₂).1.1 (.inr y) = .inl 0) : y = fvSplit κ e (.inl y₁) :=
  Sum.inr_injective ((glueOut e C₁ C₂).1.1.injective
    (hy.trans (peelOut_glueOut_in C₁ C₂ hy₁).symm))

include ha hc he in
/-- **The left piece of a tadpole-free out-leg glue is tadpole-free.** -/
theorem peelOut_tadFree_left (hA₁ : ExternalsAttached C₁) (hT : PeelTadFree (glueOut e C₁ C₂)) :
    PeelTadFree C₁ := by
  set L := lineSplitOut C₁ C₂ ha hc he with hL
  intro p₁ hb₁ w₁ hw₁
  obtain ⟨g, hg⟩ : ∃ g, L.equiv (.inl (.inr p₁)) = .inr g := ⟨_, rfl⟩
  have hbG : IsBridge (.inr g : Line (glueOut e C₁ C₂)) := by
    rw [← hg]; exact (L.peel_isBridge_left_iff (.inl ⟨rfl, rfl⟩) _).2 hb₁
  have hends := L.ends_left (.inr p₁)
  rw [hg] at hends
  simp only [Line.ends, Prod.mk.injEq] at hends
  have hwG : e (.inl w₁) = g.1.1 ∨ e (.inl w₁) = g.head.1 := by
    rcases hw₁ with rfl | rfl
    · exact .inl hends.1.symm
    · exact .inr hends.2.symm
  have hS : L.peelSet₁ {.inr g} = {.inr p₁} := by rw [← hg, L.peelSet₁_singleton]
  have hproj : ∀ v, tadComp (glueOut e C₁ C₂) g (e (.inl w₁)) v →
      Sum.elim (fun s' => tadComp C₁ p₁ w₁ s') (fun _ => tadComp C₁ p₁ w₁ a.1) (e.symm v) := by
    intro v hv
    have := L.peel_proj_left (.inl ⟨rfl, rfl⟩) hv
    rw [hS] at this
    rcases hx : e.symm v with s' | r <;> rw [hx] at this
    · exact this
    · exact this.2
  have hleft : ∀ s', tadComp (glueOut e C₁ C₂) g (e (.inl w₁)) (e (.inl s')) →
      tadComp C₁ p₁ w₁ s' := fun s' h => by simpa using hproj _ h
  rcases hT g hbG _ hwG with ⟨x, hx, hr⟩ | ⟨y, hy, hr⟩ | ⟨j, a', hj, hr⟩
  · obtain ⟨x₂, hx₂⟩ := count_exists_out (peelOut_attached_right C₂ hc)
    rw [peelOut_glueOut_out C₁ C₂ hx₂] at hx
    cases Sum.inr_injective hx
    have := hproj _ hr
    simp only [fvSplit_inr, Equiv.symm_apply_apply, Sum.elim_inr] at this
    exact .inl ⟨a, ha, this⟩
  · obtain ⟨y₁, hy₁⟩ := count_exists_in hA₁
    obtain rfl := peelOut_glueOut_in_eq C₁ C₂ hy₁ hy
    exact .inr (.inl ⟨y₁, hy₁, hleft _ hr⟩)
  · obtain ⟨a₁, ha₁, ha'⟩ := peelOut_glueOut_photonExt C₁ C₂ hj
    rw [ha'] at hr
    exact .inr (.inr ⟨j, a₁, ha₁, hleft _ hr⟩)

include ha hc he in
/-- **The left piece of an out-leg glue without in-cut has no in-cut.** -/
theorem peelOut_notRedIn_left (hR : ¬ ∃ f, PeelInCut (glueOut e C₁ C₂) f) :
    ¬ ∃ f, PeelInCut C₁ f := by
  set L := lineSplitOut C₁ C₂ ha hc he with hL
  rintro ⟨f₁, hf₁⟩
  obtain ⟨F, hF⟩ : ∃ F, L.equiv (.inl (.inl f₁)) = .inl F := ⟨_, rfl⟩
  have hbG : IsBridge (.inl F : Line (glueOut e C₁ C₂)) := by
    rw [← hF]; exact (L.peel_isBridge_left_iff (.inl ⟨rfl, rfl⟩) _).2 hf₁.1
  have hends := L.ends_left (.inl f₁)
  rw [hF] at hends
  simp only [Line.ends, Prod.mk.injEq] at hends
  have hS : L.peelSet₁ {.inl F} = {.inl f₁} := by rw [← hF, L.peelSet₁_singleton]
  refine hR ⟨F, hbG, fun j a' hj hr => ?_⟩
  obtain ⟨a₁, ha₁, ha'⟩ := peelOut_glueOut_photonExt C₁ C₂ hj
  rw [ha', hends.1] at hr
  have := L.peel_proj_left_left (.inl ⟨rfl, rfl⟩) hr
  rw [hS] at this
  exact hf₁.2 j a₁ ha₁ this

/-- Every external vertex of the out-leg glue is joined to the in-vertex without any line of
`C₂`. -/
theorem peelOut_ext_reach_in (hV₁ : VerticesConnected C₁)
    {y₁ : Wick.FermionVertex (leftKinds κ e)} (hy₁ : C₁.1.1 (.inr y₁) = .inl 0)
    {S : Set (Line (glueOut e C₁ C₂))}
    (hS₁ : ∀ g, (lineSplitOut C₁ C₂ ha hc he).equiv (.inl g) ∉ S)
    (hSf : ∀ f : FermionLine (glueOut e C₁ C₂), (.inl f : Line _) ∉ S) {T : Fin N → Prop}
    (hext : PeelExtAt (glueOut e C₁ C₂) T) :
    ∃ v, T v ∧ ReflTransGen (Joined (glueOut e C₁ C₂) S) v (e (.inl y₁.1)) := by
  have hy := peelOut_glueOut_in C₁ C₂ hy₁
  rcases hext with ⟨x, hx, hr⟩ | ⟨y, hy', hr⟩ | ⟨j, a', hj, hr⟩
  · exact ⟨_, hr, peel_reach_out_in hx hy hSf⟩
  · obtain rfl := peelOut_glueOut_in_eq C₁ C₂ hy₁ hy'
    exact ⟨_, hr, .refl⟩
  · obtain ⟨a₁, -, ha'⟩ := peelOut_glueOut_photonExt C₁ C₂ hj
    refine ⟨_, hr, ?_⟩
    rw [ha']
    exact (lineSplitOut C₁ C₂ ha hc he).peel_lift_left' hS₁ (hV₁ a₁.1 y₁.1)

include ha hc he in
/-- **The right piece of a minimally cut out-leg glue is 1PI.** -/
theorem peelOut_onePI_right (hN : N₁ + N₂ = N) (hA : ExternalsAttached (glueOut e C₁ C₂))
    (hV : VerticesConnected (glueOut e C₁ C₂)) (hT : PeelTadFree (glueOut e C₁ C₂))
    (hmin : ∀ f', PeelOutCut (glueOut e C₁ C₂) f' →
      N₂ ≤ (peelSide (glueOut e C₁ C₂) (.inl f') f'.1.1).card) : IsOnePI C₂ := by
  set L := lineSplitOut C₁ C₂ ha hc he with hL
  have hb : (e (.inl a.1) = e (.inl a.1) ∧ e (.inr c.1) = e (.inr c.1)) ∨
      (e (.inl a.1) = e (.inr c.1) ∧ e (.inr c.1) = e (.inl a.1)) := .inl ⟨rfl, rfl⟩
  have hA₁ := peelOut_attached_left C₁ C₂ ha hA
  have hV₁ := L.peel_connected_left hb hV
  obtain ⟨y₁, hy₁⟩ := count_exists_in hA₁
  have hyG := peelOut_glueOut_in C₁ C₂ hy₁
  refine ⟨peelOut_attached_right C₂ hc, L.peel_connected_right hb hV, fun g₂ hb₂ => ?_⟩
  have hbG := (L.peel_isBridge_right_iff hb g₂).2 hb₂
  rcases g₂ with f₂ | p₂
  · obtain ⟨F, hF⟩ : ∃ F, L.equiv (.inr (.inl (.inl f₂))) = .inl F := ⟨_, rfl⟩
    rw [hF] at hbG
    have hends := L.ends_right (.inl f₂)
    rw [hF] at hends
    simp only [Line.ends, Prod.mk.injEq] at hends
    have hright : ∀ v, ReflTransGen (Joined (glueOut e C₁ C₂) {.inl F}) F.1.1 v →
        ∃ r, e (.inr r) = v := by
      intro v hv
      obtain ⟨z, rfl⟩ := e.surjective v
      rcases z with s | r
      · refine absurd (peel_tail_reach_in F hbG hyG) fun h => ?_
        refine peel_sides_disjoint hbG h (hv.trans (L.peel_lift_left' (fun g hg => ?_)
          (hV₁ s y₁.1)))
        exact Sum.inl_ne_inr (L.equiv.injective ((Set.mem_singleton_iff.1 hg).trans hF.symm))
      · exact ⟨r, rfl⟩
    have hcut : PeelOutCut (glueOut e C₁ C₂) F := by
      refine ⟨hbG, fun j a' hj hr => ?_⟩
      obtain ⟨r, hr'⟩ := hright _ hr
      obtain ⟨a₁, -, ha'⟩ := peelOut_glueOut_photonExt C₁ C₂ hj
      rw [ha'] at hr'
      exact Sum.inr_ne_inl (e.injective hr')
    have hsub : peelSide (glueOut e C₁ C₂) (.inl F) F.1.1 ⊂ (countLeftImage e)ᶜ := by
      refine ⟨fun v hv => peel_mem_compl_countLeftImage.2 (hright v (mem_peelSide.1 hv)),
        fun h => hbG ?_⟩
      have ht : F.tail.1 ∈ (countLeftImage e)ᶜ := peel_mem_compl_countLeftImage.2
        ⟨f₂.tail.1, hends.1.symm⟩
      exact peel_reach_symm (mem_peelSide.1 (h ht))
    have hlt := card_lt_card hsub
    rw [card_compl_countLeftImage hN] at hlt
    exact absurd (hmin F hcut) (not_le.2 hlt)
  · obtain ⟨g, hg⟩ : ∃ g, L.equiv (.inr (.inl (.inr p₂))) = .inr g := ⟨_, rfl⟩
    rw [hg] at hbG
    have hS₁ : ∀ g', L.equiv (.inl g') ∉ ({.inr g} : Set (Line (glueOut e C₁ C₂))) :=
      fun g' hg' => Sum.inl_ne_inr (L.equiv.injective ((Set.mem_singleton_iff.1 hg').trans
        hg.symm))
    have hSf : ∀ f : FermionLine (glueOut e C₁ C₂),
        (.inl f : Line _) ∉ ({.inr g} : Set (Line (glueOut e C₁ C₂))) :=
      fun f hf => Sum.inl_ne_inr (Set.mem_singleton_iff.1 hf)
    have key : ∀ w, (w = g.1.1 ∨ w = g.head.1) →
        ReflTransGen (Joined (glueOut e C₁ C₂) {.inr g}) w (e (.inl y₁.1)) := by
      intro w hw
      obtain ⟨v, hv, hr⟩ := peelOut_ext_reach_in C₁ C₂ ha hc he hV₁ hy₁ hS₁ hSf
        (hT g hbG w hw)
      exact (show ReflTransGen _ w v from hv).trans hr
    exact hbG ((key _ (.inl rfl)).trans (peel_reach_symm (key _ (.inr rfl))))

/-- **`hsurj` of `selectedPart_peelOut`** for `peelOutSelH`, `peelRedOut`: an out-leg reducible
contraction is the out-leg glue of a selected contraction and a 1PI self-energy. -/
theorem peelOut_hsurj {M : ℕ} {κ' : Fin M → Wick.VertexKind} (g : Grading κ')
    (C : Contraction 1 1 κ') (hS : peelOutSelH C g) (hR : peelRedOut C g) :
    ∃ x ∈ countIdxSet peelOutSelH (countOnePI (nf := 1) (nA := 0)) g,
      glueOut x.2.1 x.2.2.1 x.2.2.2 = C := by
  obtain ⟨⟨hA, hV, hT⟩, hRI⟩ := hS
  obtain ⟨f, hf, hmin, -⟩ := peelOut_spec C hR
  obtain ⟨M₁, M₂, e', C₁', C₂', a', c', hN, he', hglue, ha', hc', hTe⟩ :=
    peelOut_exists_glueOut C f (ReflTransGen (Joined C {(.inl f : Line C)}) f.1.1)
      (fun l hl => ⟨fun h => h.tail (peel_joined_ends l hl),
        fun h => h.tail (peel_joined_symm (peel_joined_ends l hl))⟩) .refl
      (fun h => hf.1 (peel_reach_symm h)) (fun _ hx => peel_head_reach_out f hf.1 hx)
      (fun _ hy hT' => peel_sides_disjoint hf.1 (peel_tail_reach_in f hf.1 hy) hT') hf.2
      (fun i => hA.1 0 i)
  subst hglue
  have hside : peelSide (glueOut e' C₁' C₂') (.inl f) f.1.1 = (countLeftImage e')ᶜ := by
    ext v
    rw [mem_peelSide, peel_mem_compl_countLeftImage, hTe]
  have hA₁ := peelOut_attached_left C₁' C₂' ha' hA
  have hV₁ := (lineSplitOut C₁' C₂' ha' hc' he').peel_connected_left (.inl ⟨rfl, rfl⟩) hV
  refine ⟨⟨(M₁, M₂), e', C₁', C₂'⟩, mem_countIdxSet.2 ⟨hN, he', ⟨⟨hA₁, hV₁,
    peelOut_tadFree_left C₁' C₂' ha' hc' he' hA₁ hT⟩,
      peelOut_notRedIn_left C₁' C₂' ha' hc' he' hRI⟩,
    peelOut_onePI_right C₁' C₂' ha' hc' he' hN hA hV hT fun f' hf' => ?_⟩, rfl⟩
  have := hmin f' hf'
  rwa [hside, card_compl_countLeftImage hN] at this

end QED.GradedProof.X1C

end
