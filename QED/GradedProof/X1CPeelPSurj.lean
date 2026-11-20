/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CPeelPMem
public import QED.GradedProof.X1CPeelPRestrict

/-!
# (X₁) piece C: a photon-leg reducible contraction is a photon-leg glue

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (the graph theory of the photon-leg peel). Cut a photon-leg
reducible contraction `C` of the class `J` (attached, connected, tadpole-free, no in-leg and no
out-leg cut) at a photon-leg cut with fewest vertices on its cut side (`peelP_exists_minCut`,
`peelP_exists_glueP`): the cut side holds the photon external (tadpole-freeness) and no fermion
external, and only the cut line leaves it. The pieces:

* the vertex piece `C₁` is again in `J` (`peelP_tadFree_left`, `peelP_not_redIn`,
  `peelP_not_redOut`), since no fermion line of the vacuum polarization is a bridge of `C`
  (`peelP_right_fermion_not_bridge`: the out- and in-vertices are joined in `C₁`, but a fermion
  bridge separates them);
* the vacuum polarization `C₂` is 1PI (`peelP_onePI_right`): a photon bridge of `C₂` has a side
  inside `C₂` without fermion externals, a photon-leg cut with fewer vertices.

**`peelP_hsurjP`**: the hypothesis `hsurjP` of `countDyson_dysonFive_t9` for `SelG := peelSelG`,
`RedIn := peelRedIn`, `RedOut := peelRedOut`, `RedP := peelRedP`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line FermionLine PhotonLine Joined IsBridge VerticesConnected
  ExternalsAttached IsOnePI)
open QED.TwoLoop.Enumeration (tail_eq)
open QED.TwoLoop.LoopBound (apply_inr_photonLine)
open QED.Graded
open Relation Finset

variable {N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}
  (C₁ : Contraction 1 1 (leftKinds κ e)) (C₂ : Contraction 0 2 (rightKinds κ e))
  {w₂ : Wick.PhotonSlot (rightKinds κ e)} (hw : C₂.1.2 (.inl 1) = .inr w₂)
  (he : IsShuffle e) {b : PhotonLine (glueP e C₁ C₂)}
  (hbl : b.1 = psSplit κ e (.inl (extSlot C₁)) ∨ b.1 = psSplit κ e (.inr w₂))
include hw he hbl

omit hw he hbl in
theorem peelP_attached_left (hA : ExternalsAttached (glueP e C₁ C₂)) : ExternalsAttached C₁ := by
  refine ⟨fun i j h => ?_, fun i j h => ?_⟩
  · have h' := glueP_fermion_left e C₁ C₂ (.inl i)
    rw [h] at h'
    exact hA.1 i j h'
  · rw [Subsingleton.elim i 0, Subsingleton.elim j 0] at h
    exact (C₁.2 _).2 h

/-- **No fermion line of the vacuum polarization is a bridge of the glue.** -/
theorem peelP_right_fermion_not_bridge (hA₁ : ExternalsAttached C₁)
    (hV₁ : VerticesConnected C₁) (f₂ : FermionLine C₂) :
    ¬ IsBridge ((lineSplitP C₁ C₂ hw he hbl).equiv (.inr (.inl (.inl f₂)))) := by
  set L := lineSplitP C₁ C₂ hw he hbl with hL
  obtain ⟨F, hF⟩ := peelP_right_fermion C₁ C₂ hw he hbl f₂
  rw [hF]
  intro hb
  obtain ⟨x₁, hx₁⟩ := count_exists_out hA₁
  obtain ⟨y₁, hy₁⟩ := count_exists_in hA₁
  have hS : ∀ l, L.equiv (.inl l) ∉ ({.inl F} : Set (Line (glueP e C₁ C₂))) := fun l hl =>
    Sum.inl_ne_inr (L.equiv.injective ((Set.mem_singleton_iff.1 hl).trans hF.symm))
  have hxy := L.peel_lift_left' hS (hV₁ y₁.1 x₁.1)
  have hx := peel_head_reach_out F hb (peelP_glue_out C₁ C₂ hx₁)
  have hy := peel_tail_reach_in F hb (peelP_glue_in C₁ C₂ hy₁)
  exact hb ((hy.trans hxy).trans (peel_reach_symm hx))

/-- **The vacuum polarization of a minimal photon-leg cut is 1PI.** -/
theorem peelP_onePI_right (hN : N₁ + N₂ = N) (hA : ExternalsAttached (glueP e C₁ C₂))
    (hV : VerticesConnected (glueP e C₁ C₂))
    {w₁ : Wick.PhotonSlot (rightKinds κ e)} (hw₁ : C₂.1.2 (.inl 0) = .inr w₁)
    (hmin : ∀ g' w', PeelPCut (glueP e C₁ C₂) g' w' →
      N₂ ≤ (peelSide (glueP e C₁ C₂) (.inr g') w').card) : IsOnePI C₂ := by
  set L := lineSplitP C₁ C₂ hw he hbl with hL
  have hends := peelP_ends C₁ C₂ hw hbl
  have hA₁ := peelP_attached_left C₁ C₂ hA
  have hV₁ := L.peel_connected_left hends hV
  obtain ⟨x₁, hx₁⟩ := count_exists_out hA₁
  refine ⟨⟨fun i => i.elim0, fun i j h => ?_⟩, L.peel_connected_right hends hV, ?_⟩
  · fin_cases i
    · exact Sum.inr_ne_inl (hw₁.symm.trans h)
    · exact Sum.inr_ne_inl (hw.symm.trans h)
  rintro (f₂ | p₂) hb₂
  · exact peelP_right_fermion_not_bridge C₁ C₂ hw he hbl hA₁ hV₁ f₂
      ((L.peel_isBridge_right_iff hends _).2 hb₂)
  obtain ⟨g', hg'⟩ := peelP_right_photon C₁ C₂ hw he hbl p₂
  have hbG : IsBridge (.inr g' : Line (glueP e C₁ C₂)) := by
    rw [← hg']; exact (L.peel_isBridge_right_iff hends _).2 hb₂
  have he' := L.ends_right (.inr p₂)
  rw [hg'] at he'
  simp only [Line.ends, Prod.mk.injEq] at he'
  set X := e (.inl x₁.1)
  have hS₁ : ∀ l, L.equiv (.inl l) ∉ ({.inr g'} : Set (Line (glueP e C₁ C₂))) := fun l hl =>
    Sum.inl_ne_inr (L.equiv.injective ((Set.mem_singleton_iff.1 hl).trans hg'.symm))
  obtain ⟨E, E', hEE', hE⟩ : ∃ E E', ((E = g'.1.1 ∧ E' = g'.head.1) ∨
      (E = g'.head.1 ∧ E' = g'.1.1)) ∧ ¬ ReflTransGen (Joined (glueP e C₁ C₂) {.inr g'}) E X := by
    by_cases h1 : ReflTransGen (Joined (glueP e C₁ C₂) {.inr g'}) g'.1.1 X
    · refine ⟨_, _, .inr ⟨rfl, rfl⟩, fun h2 => hbG ?_⟩
      exact h1.trans (peel_reach_symm h2)
    · exact ⟨_, _, .inl ⟨rfl, rfl⟩, h1⟩
  have hEE : ¬ ReflTransGen (Joined (glueP e C₁ C₂) {.inr g'}) E E' := by
    rcases hEE' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hbG
    · exact fun h => hbG (peel_reach_symm h)
  have hleft : ∀ s, ¬ tadComp (glueP e C₁ C₂) g' E (e (.inl s)) := fun s hs =>
    hE (hs.trans (L.peel_lift_left' hS₁ (hV₁ s x₁.1)))
  have hcut : PeelPCut (glueP e C₁ C₂) g' E := by
    refine ⟨hbG, ?_, fun hF => ?_⟩
    · rcases hEE' with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact .inl rfl
      · exact .inr rfl
    · rw [peelP_fermAt_glue] at hF
      rcases hF with ⟨s, -, hs⟩ | ⟨s, -, hs⟩ <;> exact hleft _ hs
  have hE'r : E' ∈ (countLeftImage e)ᶜ := by
    rw [peel_mem_compl_countLeftImage]
    rcases hEE' with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨_, he'.2.symm⟩
    · exact ⟨_, he'.1.symm⟩
  have hsub : peelSide (glueP e C₁ C₂) (.inr g') E ⊂ (countLeftImage e)ᶜ := by
    refine ⟨fun v hv => ?_, fun h => hEE (mem_peelSide.1 (h hE'r))⟩
    rw [peel_mem_compl_countLeftImage]
    obtain ⟨z, rfl⟩ := e.surjective v
    rcases z with s | r
    · exact absurd (mem_peelSide.1 hv) (hleft s)
    · exact ⟨r, rfl⟩
  have hlt := card_lt_card hsub
  rw [card_compl_countLeftImage hN] at hlt
  exact absurd (hmin g' E hcut) (not_le.2 hlt)

omit hw he hbl in
/-- **`hsurj` of the photon-leg peel**: a photon-leg reducible contraction of the class `J` is
the photon-leg glue of a `J` contraction and a 1PI vacuum polarization. -/
theorem peelP_surj {M : ℕ} {κ' : Fin M → Wick.VertexKind} (g : Grading κ')
    (C : Contraction 1 1 κ') (hS : peelPSelJ C g) (hR : peelRedP C g) :
    ∃ x ∈ countIdxSet peelPSelJ (countOnePI (nf := 0) (nA := 2)) g,
      glueP x.2.1 x.2.2.1 x.2.2.2 = C := by
  obtain ⟨⟨⟨hA, hV, hT⟩, hI⟩, hO⟩ := hS
  obtain ⟨g₀, w, ⟨hgb, hw, hF⟩, hmin⟩ := peelP_exists_minCut C hR
  obtain ⟨p, q, hpq, hqw, hpq'⟩ : ∃ p q, C.1.2 (.inr p) = .inr q ∧ q.1 = w ∧
      ((p = g₀.1 ∧ q = g₀.head) ∨ (p = g₀.head ∧ q = g₀.1)) := by
    rcases hw with rfl | rfl
    · exact ⟨_, _, by rw [← apply_inr_photonLine g₀, (C.2 _).1], rfl, .inr ⟨rfl, rfl⟩⟩
    · exact ⟨_, _, apply_inr_photonLine g₀, rfl, .inl ⟨rfl, rfl⟩⟩
  have hcross := tadComp_bridge hgb hw
  have hq : tadComp C g₀ w q.1 := by rw [hqw]; exact .refl
  have hp : ¬ tadComp C g₀ w p.1 := fun hp => hcross (by
    rcases hpq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact iff_of_true hp hq
    · exact iff_of_true hq hp)
  obtain ⟨M₁, M₂, e, C₁, C₂, w₁, w₂, hN, he, hglue, hw₁, hw₂, hp', hq', hTe⟩ :=
    peelP_exists_glueP C (tadComp C g₀ w) hpq hp hq
      (fun v t h => by
        by_contra hne
        have := tadComp_crossing g₀ w (.inl (peelFLine h)) (by
          simp only [Line.ends, tail_eq (peelFLine h) h]
          exact fun h' => hne h'.symm)
        exact Sum.inl_ne_inr this)
      (fun s t h hsp hsq => by
        by_contra hne
        obtain ⟨l, hl⟩ := tadSide_photon_pair h
        have := tadComp_crossing g₀ w (.inr l) (by
          simp only [Line.ends]
          rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
          · exact hne
          · exact fun h' => hne h'.symm)
        obtain rfl := Sum.inr_injective this
        rcases hl with ⟨h1, -⟩ | ⟨-, h2⟩ <;> rcases hpq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hsp h1.symm
        · exact hsq h1.symm
        · exact hsq h2.symm
        · exact hsp h2.symm)
      (fun x hx hT' => hF (.inl ⟨x, hx, hT'⟩)) (fun y hy hT' => hF (.inr ⟨y, hy, hT'⟩))
      (fun a ha => by
        rcases (peelP_extAt_iff _ _).1 (hT g₀ hgb w hw) with h | ⟨j, a', hj, ha'⟩
        · exact absurd h hF
        · rw [Subsingleton.elim j 0, ha] at hj
          rwa [Sum.inr_injective hj])
  subst hglue
  have hbl : g₀.1 = psSplit κ' e (.inl (extSlot C₁)) ∨ g₀.1 = psSplit κ' e (.inr w₂) := by
    rcases hpq' with ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact .inl hp'
    · exact .inr hq'
  set L := lineSplitP C₁ C₂ hw₂ he hbl with hL
  have hends := peelP_ends C₁ C₂ hw₂ hbl
  have hA₁ := peelP_attached_left C₁ C₂ hA
  have hV₁ := L.peel_connected_left hends hV
  have hV₂ := L.peel_connected_right hends hV
  have h₂ := peelP_right_fermion_not_bridge C₁ C₂ hw₂ he hbl hA₁ hV₁
  have hside : peelSide (glueP e C₁ C₂) (.inr g₀) w = (countLeftImage e)ᶜ := by
    ext v
    rw [mem_peelSide, peel_mem_compl_countLeftImage, ← hTe]
    rfl
  refine ⟨⟨(M₁, M₂), e, C₁, C₂⟩, mem_countIdxSet.2 ⟨hN, he, ⟨⟨⟨hA₁, hV₁,
    peelP_tadFree_left C₁ C₂ hw₁ hw₂ he hbl hV₂ hT⟩,
    fun h => hI ((peelP_not_redIn C₁ C₂ hw₁ hw₂ he hbl hV₂ h₂).2 h)⟩,
    fun h => hO ((peelP_not_redOut C₁ C₂ hw₁ hw₂ he hbl hV₂ h₂).2 h)⟩,
    peelP_onePI_right C₁ C₂ hw₂ he hbl hN hA hV hw₁ fun g' w' hc => ?_⟩, rfl⟩
  have := hmin g' w' hc
  rwa [hside, card_compl_countLeftImage hN] at this

omit hw he hbl in
/-- **`hsurjP` of `countDyson_dysonFive_t9`** for `peelSelG`, `peelRedIn`, `peelRedOut`,
`peelRedP`. -/
theorem peelP_hsurjP {M : ℕ} (κ' : Fin M → Wick.VertexKind) (g : Grading κ')
    (_ : gradedOrder κ' g ≤ 5) :
    ∀ C : Contraction 1 1 κ', ((peelSelG C g ∧ ¬ peelRedIn C g) ∧ ¬ peelRedOut C g) →
      peelRedP C g →
        ∃ x ∈ countIdxSet (fun C g => (peelSelG C g ∧ ¬ peelRedIn C g) ∧ ¬ peelRedOut C g)
            (countOnePI (nf := 0) (nA := 2)) g,
          glueP x.2.1 x.2.2.1 x.2.2.2 = C :=
  fun C hS hR => peelP_surj g C hS hR

end QED.GradedProof.X1C

end
