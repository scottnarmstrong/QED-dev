/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CAmpGlueIn
public import QED.GradedProof.X1CRouteP
public import QED.GradedProof.X1CTadSign

/-!
# (X₁) piece C: the amplitude of `glueP` factorizes

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C3 (value factorization).

At the split assignment of `lineSplitP` (bridge `b` with momentum `P = ∓q`), the amplitude (G₃)
of `glueP e C₁ C₂` with external photon momentum `q` is
`∑_{ν ρ} A₁(μ = ν) · (1/i) D̃_{νρ}(q) · A₂(μ = (μ₀, ρ))`, with `C₁` at the photon momentum `q` and
the vacuum polarization piece `C₂` at `(q, -q)` (`contractionAmplitude_glueP`). The photon
propagator is even and symmetric, so the orientation of the bridge does not matter.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X1C

open QED.WickModel (Params Contraction Line FermionLine PhotonLine psiMomentum₂ photonMomentum₂)
open QED.TwoLoop.LoopBound (apply_inr_photonLine)
open QED.TwoLoop.Enumeration (head_eq)
open QED.Graded

theorem photonPropagator_swap (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    QED.OneLoop.photonPropagator mγ Λ ε k μ ν = QED.OneLoop.photonPropagator mγ Λ ε k ν μ := by
  simp only [QED.OneLoop.photonPropagator, Minkowski.metric_symm μ ν]

theorem extPh_iff {M nf' : ℕ} {κ' : Fin M → Wick.VertexKind} {C : Contraction nf' 1 κ'}
    {w : Wick.PhotonSlot κ'} (hw : C.1.2 (.inl 0) = .inr w) (lor : Wick.PhotonSlot κ' → Fin 4)
    (μ : Fin 1 → Fin 4) :
    (∀ j s, C.1.2 (.inl j) = .inr s → lor s = μ j) ↔ lor w = μ 0 := by
  constructor
  · exact fun h => h 0 w hw
  · intro h j s hs
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    rw [hw] at hs
    rwa [← Sum.inr_injective hs]

variable {N N₁ N₂ : ℕ} {F : Type} {κ : Fin N → Wick.VertexKind}
  {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N} (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
  (C₁ : Contraction 1 1 (leftKinds κ e)) (C₂ : Contraction 0 2 (rightKinds κ e))
  {w₁ w₂ : Wick.PhotonSlot (rightKinds κ e)} (hw₁ : C₂.1.2 (.inl 0) = .inr w₁)
  (hw : C₂.1.2 (.inl 1) = .inr w₂) (he : IsShuffle e) {b : PhotonLine (glueP e C₁ C₂)}
  (hb : b.1 = psSplit κ e (.inl (extSlot C₁)) ∨ b.1 = psSplit κ e (.inr w₂))

/-! ### The lines and momenta of `glueP` -/

theorem lineSplitP_left_fermion (f : FermionLine C₁) :
    (lineSplitP C₁ C₂ hw he hb).equiv (.inl (.inl f)) = .inl (fermionLineP C₁ C₂ (.inl f)) :=
  rfl

theorem lineSplitP_right_fermion (f : FermionLine C₂) :
    (lineSplitP C₁ C₂ hw he hb).equiv (.inr (.inl (.inl f))) =
      .inl (fermionLineP C₁ C₂ (.inr f)) := rfl

theorem lineSplitP_left_photon (g : PhotonLine C₁) :
    (lineSplitP C₁ C₂ hw he hb).equiv (.inl (.inr g)) = .inr (photonLineP C₁ C₂ he b (.inl g)) :=
  rfl

theorem lineSplitP_right_photon (g : PhotonLine C₂) :
    (lineSplitP C₁ C₂ hw he hb).equiv (.inr (.inl (.inr g))) =
      .inr (photonLineP C₁ C₂ he b (.inr (.inl g))) := rfl

theorem lineSplitP_bridge : (lineSplitP C₁ C₂ hw he hb).equiv (.inr (.inr ())) = .inr b := rfl

include hw in
theorem bridgeP_cases {q Pm : Fin 4 → ℝ}
    (hP : (b.1 = psSplit κ e (.inl (extSlot C₁)) ∧ Pm = -q) ∨
      (b.1 = psSplit κ e (.inr w₂) ∧ Pm = q)) :
    (b.1 = psSplit κ e (.inl (extSlot C₁)) ∧ b.head = psSplit κ e (.inr w₂) ∧ Pm = -q) ∨
      (b.1 = psSplit κ e (.inr w₂) ∧ b.head = psSplit κ e (.inl (extSlot C₁)) ∧ Pm = q) := by
  rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact .inl ⟨h1, head_eq b (h1 ▸ glueP_ext_w₂ C₁ C₂ hw), h2⟩
  · exact .inr ⟨h1, head_eq b (h1 ▸ glueP_w₂_ext C₁ C₂ hw), h2⟩

variable (k₁ : Line C₁ → Fin 4 → ℝ) (k₂ : Line C₂ → Fin 4 → ℝ) (Pm : Fin 4 → ℝ)

theorem psiMomentum₂_glueP_left (pIn : Fin 1 → Fin 4 → ℝ)
    (s : Wick.FermionVertex (leftKinds κ e)) :
    psiMomentum₂ (glueP e C₁ C₂) pIn ((lineSplitP C₁ C₂ hw he hb).splitMom k₁ k₂ Pm)
        (fvSplit κ e (.inl s)) = psiMomentum₂ C₁ pIn k₁ s := by
  rcases h : C₁.1.1 (.inr s) with i | s'
  · rw [QED.TwoLoop.Relabel.psiMomentum₂_of_inl h,
      QED.TwoLoop.Relabel.psiMomentum₂_of_inl ((glueP_inl_iff C₁ C₂ s i).2 h)]
  · have hf : (C₁.1.1 (.inr s)).isRight := by rw [h]; rfl
    have hG : ((glueP e C₁ C₂).1.1 (.inr (fvSplit κ e (.inl s)))).isRight := by
      rw [glueP_left' C₁ C₂ h]; rfl
    rw [QED.TwoLoop.Relabel.psiMomentum₂_of_isRight hf,
      QED.TwoLoop.Relabel.psiMomentum₂_of_isRight hG]
    exact LineSplit.splitMom_left (lineSplitP C₁ C₂ hw he hb) k₁ k₂ Pm (.inl ⟨s, hf⟩)

theorem psiMomentum₂_glueP_right (pIn : Fin 1 → Fin 4 → ℝ)
    (s : Wick.FermionVertex (rightKinds κ e)) :
    psiMomentum₂ (glueP e C₁ C₂) pIn ((lineSplitP C₁ C₂ hw he hb).splitMom k₁ k₂ Pm)
        (fvSplit κ e (.inr s)) = psiMomentum₂ C₂ ![] k₂ s := by
  obtain ⟨s', h⟩ := exists_right_pair C₂ s
  have hf : (C₂.1.1 (.inr s)).isRight := by rw [h]; rfl
  have hG : ((glueP e C₁ C₂).1.1 (.inr (fvSplit κ e (.inr s)))).isRight := by
    rw [glueP_right' C₁ C₂ h]; rfl
  rw [QED.TwoLoop.Relabel.psiMomentum₂_of_isRight hf,
    QED.TwoLoop.Relabel.psiMomentum₂_of_isRight hG]
  exact LineSplit.splitMom_right (lineSplitP C₁ C₂ hw he hb) k₁ k₂ Pm (.inl ⟨s, hf⟩)

theorem photonLineP_left_head (g : PhotonLine C₁) :
    (photonLineP C₁ C₂ he b (.inl g)).head = psSplit κ e (.inl g.head) :=
  head_eq _ (glueP_photon_left e C₁ C₂ (ne_extSlot C₁ g) (apply_inr_photonLine g))

theorem photonLineP_right_head (g : PhotonLine C₂) :
    (photonLineP C₁ C₂ he b (.inr (.inl g))).head = psSplit κ e (.inr g.head) :=
  head_eq _ (glueP_photon_right' C₁ C₂ (apply_inr_photonLine g))

include hw hb in
/-- The line sum of (T₆) over the lines of `glueP`, split over the pieces and the bridge. -/
theorem sum_photonLineP (G : PhotonLine (glueP e C₁ C₂) → Fin 4 → ℝ) :
    ∑ g, G g = (∑ g, G (photonLineP C₁ C₂ he b (.inl g))) +
      (∑ g, G (photonLineP C₁ C₂ he b (.inr (.inl g)))) + G b := by
  rw [← Fintype.sum_bijective _ (photonLineP_bijective C₁ C₂ hw he hb) _ _ fun _ => rfl,
    Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Fintype.univ_unit, Finset.sum_singleton, add_assoc]
  rfl

include hw₁ hw in
theorem photonMomentum₂_glueP_left {q : Fin 4 → ℝ}
    (hP : (b.1 = psSplit κ e (.inl (extSlot C₁)) ∧ Pm = -q) ∨
      (b.1 = psSplit κ e (.inr w₂) ∧ Pm = q)) (s : Wick.PhotonSlot (leftKinds κ e)) :
    photonMomentum₂ (glueP e C₁ C₂) ![q] ((lineSplitP C₁ C₂ hw he hb).splitMom k₁ k₂ Pm)
        (psSplit κ e (.inl s)) = photonMomentum₂ C₁ ![q] k₁ s := by
  unfold photonMomentum₂
  rw [sum_photonLineP C₁ C₂ hw he hb]
  have h0 : ∀ g : PhotonLine C₂,
      ((if (photonLineP C₁ C₂ he b (.inr (.inl g))).head = psSplit κ e (.inl s) then
        (lineSplitP C₁ C₂ hw he hb).splitMom k₁ k₂ Pm
          (.inr (photonLineP C₁ C₂ he b (.inr (.inl g)))) else 0) -
      (if (photonLineP C₁ C₂ he b (.inr (.inl g))).1 = psSplit κ e (.inl s) then
        (lineSplitP C₁ C₂ hw he hb).splitMom k₁ k₂ Pm
          (.inr (photonLineP C₁ C₂ he b (.inr (.inl g)))) else 0)) = 0 := fun g => by
    rw [photonLineP_right_head]
    simp [photonLineP]
  rw [Finset.sum_eq_zero fun g _ => h0 g, add_zero]
  have hL : ∀ g : PhotonLine C₁,
      ((if (photonLineP C₁ C₂ he b (.inl g)).head = psSplit κ e (.inl s) then
        (lineSplitP C₁ C₂ hw he hb).splitMom k₁ k₂ Pm
          (.inr (photonLineP C₁ C₂ he b (.inl g))) else 0) -
      (if (photonLineP C₁ C₂ he b (.inl g)).1 = psSplit κ e (.inl s) then
        (lineSplitP C₁ C₂ hw he hb).splitMom k₁ k₂ Pm
          (.inr (photonLineP C₁ C₂ he b (.inl g))) else 0)) =
      ((if g.head = s then k₁ (.inr g) else 0) - (if g.1 = s then k₁ (.inr g) else 0)) :=
    fun g => by
      have hk := (lineSplitP C₁ C₂ hw he hb).splitMom_left k₁ k₂ Pm (.inr g)
      rw [lineSplitP_left_photon] at hk
      rw [hk, photonLineP_left_head]
      simp only [photonLineP, (psSplit κ e).injective.eq_iff, Sum.inl.injEq]
  rw [Finset.sum_congr rfl fun g _ => hL g]
  have hB := (lineSplitP C₁ C₂ hw he hb).splitMom_bridge k₁ k₂ Pm
  rw [lineSplitP_bridge] at hB
  simp only [Fin.sum_univ_one]
  rw [hB, glueP_ext_w₁ C₁ C₂ hw₁, extSlot_spec]
  simp only [Matrix.cons_val_zero, Sum.inr.injEq,
    (psSplit κ e).injective.eq_iff, reduceCtorEq, ite_false, zero_add]
  rcases bridgeP_cases C₁ C₂ hw hP with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [h1, h2, h3]
    simp only [(psSplit κ e).injective.eq_iff, Sum.inl.injEq, reduceCtorEq, ite_false,
      zero_sub, eq_comm (a := extSlot C₁)]
    split_ifs <;> simp only [neg_neg, neg_zero] <;> abel
  · rw [h1, h2, h3]
    simp only [(psSplit κ e).injective.eq_iff, Sum.inl.injEq, reduceCtorEq, ite_false,
      sub_zero, eq_comm (a := extSlot C₁)]
    split_ifs <;> abel

include hw₁ hw in
theorem photonMomentum₂_glueP_right {q : Fin 4 → ℝ}
    (hP : (b.1 = psSplit κ e (.inl (extSlot C₁)) ∧ Pm = -q) ∨
      (b.1 = psSplit κ e (.inr w₂) ∧ Pm = q)) (s : Wick.PhotonSlot (rightKinds κ e)) :
    photonMomentum₂ (glueP e C₁ C₂) ![q] ((lineSplitP C₁ C₂ hw he hb).splitMom k₁ k₂ Pm)
        (psSplit κ e (.inr s)) = photonMomentum₂ C₂ ![q, -q] k₂ s := by
  unfold photonMomentum₂
  rw [sum_photonLineP C₁ C₂ hw he hb]
  have h0 : ∀ g : PhotonLine C₁,
      ((if (photonLineP C₁ C₂ he b (.inl g)).head = psSplit κ e (.inr s) then
        (lineSplitP C₁ C₂ hw he hb).splitMom k₁ k₂ Pm
          (.inr (photonLineP C₁ C₂ he b (.inl g))) else 0) -
      (if (photonLineP C₁ C₂ he b (.inl g)).1 = psSplit κ e (.inr s) then
        (lineSplitP C₁ C₂ hw he hb).splitMom k₁ k₂ Pm
          (.inr (photonLineP C₁ C₂ he b (.inl g))) else 0)) = 0 := fun g => by
    rw [photonLineP_left_head]
    simp [photonLineP]
  rw [Finset.sum_eq_zero fun g _ => h0 g, zero_add]
  have hR : ∀ g : PhotonLine C₂,
      ((if (photonLineP C₁ C₂ he b (.inr (.inl g))).head = psSplit κ e (.inr s) then
        (lineSplitP C₁ C₂ hw he hb).splitMom k₁ k₂ Pm
          (.inr (photonLineP C₁ C₂ he b (.inr (.inl g)))) else 0) -
      (if (photonLineP C₁ C₂ he b (.inr (.inl g))).1 = psSplit κ e (.inr s) then
        (lineSplitP C₁ C₂ hw he hb).splitMom k₁ k₂ Pm
          (.inr (photonLineP C₁ C₂ he b (.inr (.inl g)))) else 0)) =
      ((if g.head = s then k₂ (.inr g) else 0) - (if g.1 = s then k₂ (.inr g) else 0)) :=
    fun g => by
      have hk := (lineSplitP C₁ C₂ hw he hb).splitMom_right k₁ k₂ Pm (.inr g)
      rw [lineSplitP_right_photon] at hk
      rw [hk, photonLineP_right_head]
      simp only [photonLineP, (psSplit κ e).injective.eq_iff, Sum.inr.injEq]
  rw [Finset.sum_congr rfl fun g _ => hR g]
  have hB := (lineSplitP C₁ C₂ hw he hb).splitMom_bridge k₁ k₂ Pm
  rw [lineSplitP_bridge] at hB
  simp only [Fin.sum_univ_one, Fin.sum_univ_two]
  rw [hB, glueP_ext_w₁ C₁ C₂ hw₁, hw₁, hw]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Sum.inr.injEq,
    (psSplit κ e).injective.eq_iff]
  rcases bridgeP_cases C₁ C₂ hw hP with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [h1, h2, h3]
    simp only [(psSplit κ e).injective.eq_iff, Sum.inr.injEq, reduceCtorEq, ite_false,
      sub_zero]
    split_ifs <;> abel
  · rw [h1, h2, h3]
    simp only [(psSplit κ e).injective.eq_iff, Sum.inr.injEq, reduceCtorEq, ite_false,
      zero_sub]
    split_ifs <;> abel

end QED.GradedProof.X1C

end
