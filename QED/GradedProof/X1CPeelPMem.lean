/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CPeelPGlue
public import QED.GradedProof.X1CCountP
public import QED.GradedProof.X1CPeelSurj

/-!
# (X₁) piece C: the photon-leg glue is photon-leg reducible, and nothing else

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (the graph theory of the photon-leg peel). For
`G = glueP e C₁ C₂` with a connected vacuum polarization `C₂`:

* `peelP_inCut_iff`, `peelP_outCut_iff`: a fermion line of `C₁` is an in-leg (out-leg) cut of
  `G` iff it is one of `C₁`; `peelP_not_redIn`, `peelP_not_redOut`: `G` has no in-leg (out-leg)
  cut if `C₁` has none and no fermion line of `C₂` is a bridge of `G`.
* `peelP_tadFree_glue`, `peelP_tadFree_left`: `G` is tadpole-free iff `C₁` is (for 1PI `C₂`).
* `peelP_cut_bridge`: the bridge with its `C₂` end is a photon-leg cut of `G`.
* `peelP_glue_side`: if `C₁` is attached, connected and tadpole-free and `C₂` is 1PI, the cut
  side of every photon-leg cut of `G` contains `C₂`; hence `peelPSide G = (countLeftImage e)ᶜ`.

**`peelP_hmemP`**, **`peelP_hinjP`**: the hypotheses `hmemP`, `hinjP` of
`countDyson_dysonFive_t9` for `SelG := peelSelG`, `RedIn := peelRedIn`, `RedOut := peelRedOut`,
`RedP := peelRedP`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line FermionLine PhotonLine Joined IsBridge VerticesConnected
  ExternalsAttached IsOnePI)
open QED.Graded
open Relation Finset

variable {N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}

section Glue

variable (C₁ : Contraction 1 1 (leftKinds κ e)) (C₂ : Contraction 0 2 (rightKinds κ e))
  {w₁ : Wick.PhotonSlot (rightKinds κ e)} (hw₁ : C₂.1.2 (.inl 0) = .inr w₁)
  {w₂ : Wick.PhotonSlot (rightKinds κ e)} (hw : C₂.1.2 (.inl 1) = .inr w₂)
  (he : IsShuffle e) {b : PhotonLine (glueP e C₁ C₂)}
  (hbl : b.1 = psSplit κ e (.inl (extSlot C₁)) ∨ b.1 = psSplit κ e (.inr w₂))
include hw he hbl

/-! ### Fermion cuts -/

include hw₁ in
/-- **A fermion line of the vertex piece is an in-leg cut of the glue iff it is one of the vertex
piece.** -/
theorem peelP_inCut_iff (hV₂ : VerticesConnected C₂) (f₁ : FermionLine C₁)
    {F : FermionLine (glueP e C₁ C₂)}
    (hF : (lineSplitP C₁ C₂ hw he hbl).equiv (.inl (.inl f₁)) = .inl F) :
    PeelInCut (glueP e C₁ C₂) F ↔ PeelInCut C₁ f₁ := by
  have hends := (lineSplitP C₁ C₂ hw he hbl).ends_left (.inl f₁)
  rw [hF] at hends
  simp only [Line.ends, Prod.mk.injEq] at hends
  unfold PeelInCut
  rw [hends.1, ← hF, (lineSplitP C₁ C₂ hw he hbl).peel_isBridge_left_iff
    (peelP_ends C₁ C₂ hw hbl), peelP_noPhotonAt_side C₁ C₂ hw₁ hw he hbl hV₂]

include hw₁ in
/-- **A fermion line of the vertex piece is an out-leg cut of the glue iff it is one of the
vertex piece.** -/
theorem peelP_outCut_iff (hV₂ : VerticesConnected C₂) (f₁ : FermionLine C₁)
    {F : FermionLine (glueP e C₁ C₂)}
    (hF : (lineSplitP C₁ C₂ hw he hbl).equiv (.inl (.inl f₁)) = .inl F) :
    PeelOutCut (glueP e C₁ C₂) F ↔ PeelOutCut C₁ f₁ := by
  have hends := (lineSplitP C₁ C₂ hw he hbl).ends_left (.inl f₁)
  rw [hF] at hends
  simp only [Line.ends, Prod.mk.injEq] at hends
  unfold PeelOutCut
  rw [hends.2, ← hF, (lineSplitP C₁ C₂ hw he hbl).peel_isBridge_left_iff
    (peelP_ends C₁ C₂ hw hbl), peelP_noPhotonAt_side C₁ C₂ hw₁ hw he hbl hV₂]

/-- The fermion bridges of the glue are those of the vertex piece, when no fermion line of `C₂`
is a bridge of `G`. -/
theorem peelP_fermion_cases (h₂ : ∀ f₂ : FermionLine C₂,
      ¬ IsBridge ((lineSplitP C₁ C₂ hw he hbl).equiv (.inr (.inl (.inl f₂)))))
    (F : FermionLine (glueP e C₁ C₂)) (hF : IsBridge (.inl F : Line (glueP e C₁ C₂))) :
    ∃ f₁, (lineSplitP C₁ C₂ hw he hbl).equiv (.inl (.inl f₁)) = .inl F := by
  obtain ⟨x, hx⟩ := (lineSplitP C₁ C₂ hw he hbl).equiv.surjective (.inl F)
  rcases x with (f₁ | p₁) | (f₂ | p₂) | ⟨⟩
  · exact ⟨f₁, hx⟩
  · obtain ⟨g, hg⟩ := peelP_left_photon C₁ C₂ hw he hbl p₁
    exact absurd (hg.symm.trans hx) Sum.inr_ne_inl
  · exact absurd (hx ▸ hF) (h₂ f₂)
  · obtain ⟨g, hg⟩ := peelP_right_photon C₁ C₂ hw he hbl p₂
    exact absurd (hg.symm.trans hx) Sum.inr_ne_inl
  · exact absurd hx Sum.inr_ne_inl

include hw₁ in
theorem peelP_not_redIn (hV₂ : VerticesConnected C₂) (h₂ : ∀ f₂ : FermionLine C₂,
      ¬ IsBridge ((lineSplitP C₁ C₂ hw he hbl).equiv (.inr (.inl (.inl f₂))))) :
    (∃ f, PeelInCut (glueP e C₁ C₂) f) ↔ ∃ f, PeelInCut C₁ f := by
  constructor
  · rintro ⟨F, hF⟩
    obtain ⟨f₁, hf₁⟩ := peelP_fermion_cases C₁ C₂ hw he hbl h₂ F hF.1
    exact ⟨f₁, (peelP_inCut_iff C₁ C₂ hw₁ hw he hbl hV₂ f₁ hf₁).1 hF⟩
  · rintro ⟨f₁, hf₁⟩
    obtain ⟨F, hF⟩ := peelP_left_fermion C₁ C₂ hw he hbl f₁
    exact ⟨F, (peelP_inCut_iff C₁ C₂ hw₁ hw he hbl hV₂ f₁ hF).2 hf₁⟩

include hw₁ in
theorem peelP_not_redOut (hV₂ : VerticesConnected C₂) (h₂ : ∀ f₂ : FermionLine C₂,
      ¬ IsBridge ((lineSplitP C₁ C₂ hw he hbl).equiv (.inr (.inl (.inl f₂))))) :
    (∃ f, PeelOutCut (glueP e C₁ C₂) f) ↔ ∃ f, PeelOutCut C₁ f := by
  constructor
  · rintro ⟨F, hF⟩
    obtain ⟨f₁, hf₁⟩ := peelP_fermion_cases C₁ C₂ hw he hbl h₂ F hF.1
    exact ⟨f₁, (peelP_outCut_iff C₁ C₂ hw₁ hw he hbl hV₂ f₁ hf₁).1 hF⟩
  · rintro ⟨f₁, hf₁⟩
    obtain ⟨F, hF⟩ := peelP_left_fermion C₁ C₂ hw he hbl f₁
    exact ⟨F, (peelP_outCut_iff C₁ C₂ hw₁ hw he hbl hV₂ f₁ hF).2 hf₁⟩

/-! ### Tadpole-freeness -/

/-- The ends of a photon line of the vertex piece in the glue. -/
theorem peelP_left_photon_ends (p₁ : PhotonLine C₁) {g : PhotonLine (glueP e C₁ C₂)}
    (hg : (lineSplitP C₁ C₂ hw he hbl).equiv (.inl (.inr p₁)) = .inr g) {w : Fin N} :
    (w = g.1.1 ∨ w = g.head.1) ↔ ∃ w₁, (w₁ = p₁.1.1 ∨ w₁ = p₁.head.1) ∧ w = e (.inl w₁) := by
  have hends := (lineSplitP C₁ C₂ hw he hbl).ends_left (.inr p₁)
  rw [hg] at hends
  simp only [Line.ends, Prod.mk.injEq] at hends
  rw [hends.1, hends.2]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨_, .inl rfl, rfl⟩
    · exact ⟨_, .inr rfl, rfl⟩
  · rintro ⟨w₁, (rfl | rfl), rfl⟩
    · exact .inl rfl
    · exact .inr rfl

include hw₁ in
/-- **The glue of a tadpole-free vertex and a 1PI vacuum polarization is tadpole-free.** -/
theorem peelP_tadFree_glue (hA₁ : ExternalsAttached C₁) (hV₁ : VerticesConnected C₁)
    (hT₁ : PeelTadFree C₁) (hC₂ : IsOnePI C₂) : PeelTadFree (glueP e C₁ C₂) := by
  set L := lineSplitP C₁ C₂ hw he hbl with hL
  intro g hg w hw'
  obtain ⟨x, hx⟩ := L.equiv.surjective (.inr g)
  rcases x with (f₁ | p₁) | l₂ | ⟨⟩
  · obtain ⟨F, hF⟩ := peelP_left_fermion C₁ C₂ hw he hbl f₁
    exact absurd (hF.symm.trans hx) Sum.inl_ne_inr
  · obtain ⟨w₁', hw₁', rfl⟩ := (peelP_left_photon_ends C₁ C₂ hw he hbl p₁ hx).1 hw'
    have hb₁ : IsBridge (.inr p₁ : Line C₁) :=
      (L.peel_isBridge_left_iff (peelP_ends C₁ C₂ hw hbl) _).1 (by rw [hx]; exact hg)
    unfold tadComp
    rw [← hx, peelP_extAt_side C₁ C₂ hw₁ hw he hbl hC₂.2.1]
    exact hT₁ p₁ hb₁ w₁' hw₁'
  · exact absurd ((L.peel_isBridge_right_iff (peelP_ends C₁ C₂ hw hbl) l₂).1 (by rw [hx]; exact hg))
      (hC₂.2.2 l₂)
  · obtain rfl : b = g := Sum.inr_injective hx
    have hS₁ : ∀ l, L.equiv (.inl l) ∉ ({.inr b} : Set (Line (glueP e C₁ C₂))) :=
      fun l hl => Sum.inl_ne_inr (L.equiv.injective
        (show L.equiv (.inl l) = L.equiv (.inr (.inr ())) from Set.mem_singleton_iff.1 hl))
    have hS₂ : ∀ l, L.equiv (.inr (.inl l)) ∉ ({.inr b} : Set (Line (glueP e C₁ C₂))) :=
      fun l hl => Sum.inl_ne_inr (Sum.inr_injective (L.equiv.injective
        (show L.equiv (.inr (.inl l)) = L.equiv (.inr (.inr ())) from
          Set.mem_singleton_iff.1 hl)))
    have hcase : w = e (.inl (extSlot C₁).1) ∨ w = e (.inr w₂.1) := by
      rcases peelP_ends C₁ C₂ hw hbl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rcases hw' with rfl | rfl <;> simp only [h1, h2, true_or, or_true]
    rcases hcase with rfl | rfl
    · obtain ⟨x₁, hx₁⟩ := count_exists_out hA₁
      exact .inl ⟨_, peelP_glue_out C₁ C₂ hx₁, L.peel_lift_left' hS₁ (hV₁ _ _)⟩
    · refine (peelP_extAt_iff _ _).2 (.inr ((peelP_photonAt_glue C₁ C₂ hw₁ _).2 ?_))
      exact L.peel_lift_right' hS₂ (hC₂.2.1 _ _)

include hw₁ in
/-- **The vertex piece of a tadpole-free glue is tadpole-free.** -/
theorem peelP_tadFree_left (hV₂ : VerticesConnected C₂) (hT : PeelTadFree (glueP e C₁ C₂)) :
    PeelTadFree C₁ := by
  set L := lineSplitP C₁ C₂ hw he hbl with hL
  intro p₁ hb₁ w₁' hw₁'
  obtain ⟨g, hg⟩ := peelP_left_photon C₁ C₂ hw he hbl p₁
  have hbG : IsBridge (.inr g : Line (glueP e C₁ C₂)) := by
    rw [← hg]; exact (L.peel_isBridge_left_iff (peelP_ends C₁ C₂ hw hbl) _).2 hb₁
  have h := hT g hbG _ ((peelP_left_photon_ends C₁ C₂ hw he hbl p₁ hg).2 ⟨w₁', hw₁', rfl⟩)
  unfold tadComp at h
  rw [← hg, peelP_extAt_side C₁ C₂ hw₁ hw he hbl hV₂] at h
  exact h

/-! ### The photon-leg cut of the glue -/

/-- **The bridge, with its end in the vacuum polarization, is a photon-leg cut.** -/
theorem peelP_cut_bridge : PeelPCut (glueP e C₁ C₂) b (e (.inr w₂.1)) := by
  set L := lineSplitP C₁ C₂ hw he hbl with hL
  have hends := peelP_ends C₁ C₂ hw hbl
  refine ⟨L.peel_isBridge_bridge hends, ?_, fun hF => ?_⟩
  · rcases hends with ⟨-, h⟩ | ⟨h, -⟩
    · exact .inr h.symm
    · exact .inl h.symm
  · rw [peelP_fermAt_glue] at hF
    have key : ∀ s, ¬ tadComp (glueP e C₁ C₂) b (e (.inr w₂.1)) (e (.inl s)) := by
      intro s hs
      obtain ⟨s', hs'⟩ := L.peel_proj_right_mem hends (S := {L.peelBridge})
        (Set.mem_singleton _) hs
      exact Sum.inl_ne_inr (e.injective hs')
    rcases hF with ⟨s, -, hs⟩ | ⟨s, -, hs⟩
    · exact key _ hs
    · exact key _ hs

/-- **The cut side of every photon-leg cut of the glue contains the vacuum polarization.** -/
theorem peelP_glue_side (hA₁ : ExternalsAttached C₁) (hV₁ : VerticesConnected C₁)
    (hT₁ : PeelTadFree C₁) (hC₂ : IsOnePI C₂) (g : PhotonLine (glueP e C₁ C₂)) (w : Fin N)
    (hg : PeelPCut (glueP e C₁ C₂) g w) (r : Fin N₂) :
    tadComp (glueP e C₁ C₂) g w (e (.inr r)) := by
  set L := lineSplitP C₁ C₂ hw he hbl with hL
  obtain ⟨hgb, hw', hF⟩ := hg
  obtain ⟨x, hx⟩ := L.equiv.surjective (.inr g)
  rcases x with (f₁ | p₁) | l₂ | ⟨⟩
  · obtain ⟨F, hF'⟩ := peelP_left_fermion C₁ C₂ hw he hbl f₁
    exact absurd (hF'.symm.trans hx) Sum.inl_ne_inr
  · obtain ⟨w₁', hw₁', rfl⟩ := (peelP_left_photon_ends C₁ C₂ hw he hbl p₁ hx).1 hw'
    have hb₁ : IsBridge (.inr p₁ : Line C₁) :=
      (L.peel_isBridge_left_iff (peelP_ends C₁ C₂ hw hbl) _).1 (by rw [hx]; exact hgb)
    unfold tadComp at hF ⊢
    rw [← hx, peelP_fermAt_side C₁ C₂ hw he hbl] at hF
    rw [← hx, peelP_side_right C₁ C₂ hw he hbl hC₂.2.1]
    rcases (peelP_extAt_iff _ _).1 (hT₁ p₁ hb₁ w₁' hw₁') with h | h
    · exact absurd h hF
    · exact (peelP_photonAt_one C₁ _).1 h
  · exact absurd ((L.peel_isBridge_right_iff (peelP_ends C₁ C₂ hw hbl) l₂).1
      (by rw [hx]; exact hgb)) (hC₂.2.2 l₂)
  · obtain rfl : b = g := Sum.inr_injective hx
    have hS₁ : ∀ l, L.equiv (.inl l) ∉ ({.inr b} : Set (Line (glueP e C₁ C₂))) :=
      fun l hl => Sum.inl_ne_inr (L.equiv.injective
        (show L.equiv (.inl l) = L.equiv (.inr (.inr ())) from Set.mem_singleton_iff.1 hl))
    have hS₂ : ∀ l, L.equiv (.inr (.inl l)) ∉ ({.inr b} : Set (Line (glueP e C₁ C₂))) :=
      fun l hl => Sum.inl_ne_inr (Sum.inr_injective (L.equiv.injective
        (show L.equiv (.inr (.inl l)) = L.equiv (.inr (.inr ())) from
          Set.mem_singleton_iff.1 hl)))
    have hcase : w = e (.inl (extSlot C₁).1) ∨ w = e (.inr w₂.1) := by
      rcases peelP_ends C₁ C₂ hw hbl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rcases hw' with rfl | rfl <;> simp only [h1, h2, true_or, or_true]
    rcases hcase with rfl | rfl
    · obtain ⟨x₁, hx₁⟩ := count_exists_out hA₁
      exact absurd (.inl ⟨_, peelP_glue_out C₁ C₂ hx₁, L.peel_lift_left' hS₁ (hV₁ _ _)⟩) hF
    · exact L.peel_lift_right' hS₂ (hC₂.2.1 _ _)

/-- **The peeled set of the photon-leg glue is the vertex set of the vacuum polarization.** -/
theorem peelPSide_glue (hA₁ : ExternalsAttached C₁) (hV₁ : VerticesConnected C₁)
    (hT₁ : PeelTadFree C₁) (hC₂ : IsOnePI C₂) :
    peelPSide (glueP e C₁ C₂) = (countLeftImage e)ᶜ := by
  ext v
  rw [mem_peelPSide, peel_mem_compl_countLeftImage]
  constructor
  · intro h
    have h' := h b _ (peelP_cut_bridge C₁ C₂ hw he hbl)
    obtain ⟨s', hs'⟩ := (lineSplitP C₁ C₂ hw he hbl).peel_proj_right_mem
      (peelP_ends C₁ C₂ hw hbl) (S := {(lineSplitP C₁ C₂ hw he hbl).peelBridge})
      (Set.mem_singleton _) h'
    exact ⟨s', hs'.symm⟩
  · rintro ⟨r, rfl⟩ g w hg
    exact peelP_glue_side C₁ C₂ hw he hbl hA₁ hV₁ hT₁ hC₂ g w hg r

end Glue

/-! ### The hypotheses `hmemP`, `hinjP` -/

/-- The class of the photon-leg peel: selected, with no in-leg and no out-leg cut. -/
abbrev peelPSelJ : CountSel 1 1 := fun C g => (peelSelG C g ∧ ¬ peelRedIn C g) ∧ ¬ peelRedOut C g

/-- **The photon-leg glue of a `J` contraction and a 1PI vacuum polarization is a photon-leg
reducible `J` contraction.** -/
theorem peelP_glue_mem (C₁ : Contraction 1 1 (leftKinds κ e))
    (C₂ : Contraction 0 2 (rightKinds κ e)) (he : IsShuffle e) (g : Grading κ)
    (h₁ : peelPSelJ C₁ (gradL κ e g)) (hC₂ : IsOnePI C₂) :
    peelPSelJ (glueP e C₁ C₂) g ∧ peelRedP (glueP e C₁ C₂) g := by
  obtain ⟨⟨⟨hA₁, hV₁, hT₁⟩, hI₁⟩, hO₁⟩ := h₁
  obtain ⟨w₁, hw₁⟩ := count_exists_photon hC₂.1 0
  obtain ⟨w₂, hw⟩ := count_exists_photon hC₂.1 1
  obtain ⟨b, hbl⟩ := exists_bridgeP C₁ C₂ hw
  have h₂ : ∀ f₂ : FermionLine C₂,
      ¬ IsBridge ((lineSplitP C₁ C₂ hw he hbl).equiv (.inr (.inl (.inl f₂)))) := fun f₂ hf =>
    hC₂.2.2 _ (((lineSplitP C₁ C₂ hw he hbl).peel_isBridge_right_iff
      (peelP_ends C₁ C₂ hw hbl) _).1 hf)
  refine ⟨⟨⟨⟨peelP_glue_attached C₁ C₂ hA₁ hw₁, countP_verticesConnected C₁ C₂ hw he hV₁ hC₂.2.1,
    peelP_tadFree_glue C₁ C₂ hw₁ hw he hbl hA₁ hV₁ hT₁ hC₂⟩,
    fun h => hI₁ ((peelP_not_redIn C₁ C₂ hw₁ hw he hbl hC₂.2.1 h₂).1 h)⟩,
    fun h => hO₁ ((peelP_not_redOut C₁ C₂ hw₁ hw he hbl hC₂.2.1 h₂).1 h)⟩,
    ⟨b, _, peelP_cut_bridge C₁ C₂ hw he hbl⟩⟩

/-- **`hmemP` of `countDyson_dysonFive_t9`** for `peelSelG`, `peelRedIn`, `peelRedOut`,
`peelRedP`. -/
theorem peelP_hmemP {M : ℕ} (κ' : Fin M → Wick.VertexKind) (g : Grading κ')
    (_ : gradedOrder κ' g ≤ 5) :
    ∀ x ∈ countIdxSet (fun C g => (peelSelG C g ∧ ¬ peelRedIn C g) ∧ ¬ peelRedOut C g)
        (countOnePI (nf := 0) (nA := 2)) g,
      ((peelSelG (glueP x.2.1 x.2.2.1 x.2.2.2) g ∧ ¬ peelRedIn (glueP x.2.1 x.2.2.1 x.2.2.2) g) ∧
        ¬ peelRedOut (glueP x.2.1 x.2.2.1 x.2.2.2) g) ∧
        peelRedP (glueP x.2.1 x.2.2.1 x.2.2.2) g := by
  rintro ⟨p, e', C₁', C₂'⟩ hx
  obtain ⟨-, he', h₁, hC₂⟩ := mem_countIdxSet.1 hx
  exact peelP_glue_mem C₁' C₂' he' g h₁ hC₂

/-- **`hpeel` of `countGlueP_injOn`** for `peelPSide`. -/
theorem peelP_hpeel {M : ℕ} {κ' : Fin M → Wick.VertexKind} (g : Grading κ') :
    ∀ x ∈ countIdxSet peelPSelJ (countOnePI (nf := 0) (nA := 2)) g,
      peelPSide (glueP x.2.1 x.2.2.1 x.2.2.2) = (countLeftImage x.2.1)ᶜ := by
  rintro ⟨p, e', C₁', C₂'⟩ hx
  obtain ⟨-, he', ⟨⟨⟨hA₁, hV₁, hT₁⟩, -⟩, -⟩, hC₂⟩ := mem_countIdxSet.1 hx
  obtain ⟨w₂, hw⟩ := count_exists_photon hC₂.1 1
  obtain ⟨b, hbl⟩ := exists_bridgeP C₁' C₂' hw
  exact peelPSide_glue C₁' C₂' hw he' hbl hA₁ hV₁ hT₁ hC₂

/-- **`hinjP` of `countDyson_dysonFive_t9`** for `peelSelG`, `peelRedIn`, `peelRedOut`. -/
theorem peelP_hinjP {M : ℕ} (κ' : Fin M → Wick.VertexKind) (g : Grading κ')
    (_ : gradedOrder κ' g ≤ 5) :
    Set.InjOn (fun x : CountIdx 1 1 0 2 κ' => glueP x.2.1 x.2.2.1 x.2.2.2)
      (countIdxSet (fun C g => (peelSelG C g ∧ ¬ peelRedIn C g) ∧ ¬ peelRedOut C g)
        (countOnePI (nf := 0) (nA := 2)) g) :=
  countGlueP_injOn peelPSelJ g peelPSide (peelP_hpeel g)

end QED.GradedProof.X1C

end
