/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CAmpGlueP

/-!
# (X₁) piece C: the vertex and line factors and the amplitude of `glueP`

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C3 (value factorization).

* `bodyOf_glueP`: at a joined index assignment, the vertex and line factors of `glueP e C₁ C₂`
  are those of `C₁` (photon momentum `q`) times the bridge photon propagator `(1/i) D̃(q)` between
  the Lorentz indices of `extSlot C₁` and `w₂` times those of `C₂` (photon momenta `(q, -q)`).
* `contractionAmplitude_glueP`: the amplitude factorizes over the bridge indices `ν`, `ρ`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X1C

open QED.WickModel (Params Contraction Line FermionLine PhotonLine psiMomentum₂ photonMomentum₂)
open QED.Graded

variable {N N₁ N₂ : ℕ} {F : Type} {κ : Fin N → Wick.VertexKind}
  {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N} (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
  (C₁ : Contraction 1 1 (leftKinds κ e)) (C₂ : Contraction 0 2 (rightKinds κ e))
  {w₁ w₂ : Wick.PhotonSlot (rightKinds κ e)} (hw₁ : C₂.1.2 (.inl 0) = .inr w₁)
  (hw : C₂.1.2 (.inl 1) = .inr w₂) (he : IsShuffle e) {b : PhotonLine (glueP e C₁ C₂)}
  (hb : b.1 = psSplit κ e (.inl (extSlot C₁)) ∨ b.1 = psSplit κ e (.inr w₂))
  (k₁ : Line C₁ → Fin 4 → ℝ) (k₂ : Line C₂ → Fin 4 → ℝ) {q Pm : Fin 4 → ℝ}
  (hP : (b.1 = psSplit κ e (.inl (extSlot C₁)) ∧ Pm = -q) ∨
    (b.1 = psSplit κ e (.inr w₂) ∧ Pm = q))

include hw₁ hP in
/-- **The vertex and line factors of `glueP` at a joined index assignment.** -/
theorem bodyOf_glueP (φ : Flavoring F κ) (g : Grading κ) (pIn : Fin 1 → Fin 4 → ℝ)
    (v₁ : IdxAsg (leftKinds κ e)) (v₂ : IdxAsg (rightKinds κ e)) :
    bodyOf P Φ D (glueP e C₁ C₂) φ g pIn ![q] ((lineSplitP C₁ C₂ hw he hb).splitMom k₁ k₂ Pm)
        (joinT κ e v₁ v₂).1 (joinT κ e v₁ v₂).2.1 (joinT κ e v₁ v₂).2.2 =
      bodyOf P Φ D C₁ (flL κ e φ) (gradL κ e g) pIn ![q] k₁ v₁.1 v₁.2.1 v₁.2.2 *
        ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε q (v₁.2.2 (extSlot C₁))
          (v₂.2.2 w₂)) *
        bodyOf P Φ D C₂ (flR κ e φ) (gradR κ e g) ![] ![q, -q] k₂ v₂.1 v₂.2.1 v₂.2.2 := by
  obtain ⟨α₁, β₁, l₁⟩ := v₁
  obtain ⟨α₂, β₂, l₂⟩ := v₂
  simp only [joinT]
  rw [bodyOf_eq, bodyOf_eq, bodyOf_eq, prod_split_vertices e,
    prod_lines_split (lineSplitP C₁ C₂ hw he hb)]
  simp only [vtxOf_split_left, vtxOf_split_right, joinF_inl, joinF_inr,
    psiMomentum₂_glueP_left C₁ C₂ hw he hb, psiMomentum₂_glueP_right C₁ C₂ hw he hb,
    photonMomentum₂_glueP_left C₁ C₂ hw₁ hw he hb k₁ k₂ Pm hP,
    photonMomentum₂_glueP_right C₁ C₂ hw₁ hw he hb k₁ k₂ Pm hP]
  have hL : ∀ l : Line C₁, lineFac P Φ φ ((lineSplitP C₁ C₂ hw he hb).splitMom k₁ k₂ Pm)
      (joinF (fvSplit κ e) α₁ α₂) (joinF (fvSplit κ e) β₁ β₂) (joinF (psSplit κ e) l₁ l₂)
      ((lineSplitP C₁ C₂ hw he hb).equiv (.inl l)) = lineFac P Φ (flL κ e φ) k₁ α₁ β₁ l₁ l := by
    rintro (f | g')
    · have hk := (lineSplitP C₁ C₂ hw he hb).splitMom_left k₁ k₂ Pm (.inl f)
      rw [lineSplitP_left_fermion] at hk
      rw [lineSplitP_left_fermion]
      simp only [lineFac, Sum.elim_inl]
      rw [hk, fermionLineP_left_tail]
      simp only [fermionLineP, joinF_inl]
      rfl
    · have hk := (lineSplitP C₁ C₂ hw he hb).splitMom_left k₁ k₂ Pm (.inr g')
      rw [lineSplitP_left_photon] at hk
      rw [lineSplitP_left_photon]
      simp only [lineFac, Sum.elim_inr]
      rw [hk, photonLineP_left_head]
      simp only [photonLineP, joinF_inl]
  have hR : ∀ l : Line C₂, lineFac P Φ φ ((lineSplitP C₁ C₂ hw he hb).splitMom k₁ k₂ Pm)
      (joinF (fvSplit κ e) α₁ α₂) (joinF (fvSplit κ e) β₁ β₂) (joinF (psSplit κ e) l₁ l₂)
      ((lineSplitP C₁ C₂ hw he hb).equiv (.inr (.inl l))) =
        lineFac P Φ (flR κ e φ) k₂ α₂ β₂ l₂ l := by
    rintro (f | g')
    · have hk := (lineSplitP C₁ C₂ hw he hb).splitMom_right k₁ k₂ Pm (.inl f)
      rw [lineSplitP_right_fermion] at hk
      rw [lineSplitP_right_fermion]
      simp only [lineFac, Sum.elim_inl]
      rw [hk, fermionLineP_right_tail]
      simp only [fermionLineP, joinF_inr]
      rfl
    · have hk := (lineSplitP C₁ C₂ hw he hb).splitMom_right k₁ k₂ Pm (.inr g')
      rw [lineSplitP_right_photon] at hk
      rw [lineSplitP_right_photon]
      simp only [lineFac, Sum.elim_inr]
      rw [hk, photonLineP_right_head]
      simp only [photonLineP, joinF_inr]
  have hB := (lineSplitP C₁ C₂ hw he hb).splitMom_bridge k₁ k₂ Pm
  rw [lineSplitP_bridge] at hB
  have hD : lineFac P Φ φ ((lineSplitP C₁ C₂ hw he hb).splitMom k₁ k₂ Pm)
      (joinF (fvSplit κ e) α₁ α₂) (joinF (fvSplit κ e) β₁ β₂) (joinF (psSplit κ e) l₁ l₂)
      ((lineSplitP C₁ C₂ hw he hb).equiv (.inr (.inr ()))) =
      (1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε q (l₁ (extSlot C₁)) (l₂ w₂) := by
    rw [lineSplitP_bridge]
    simp only [lineFac, Sum.elim_inr]
    rw [hB]
    rcases bridgeP_cases C₁ C₂ hw hP with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · rw [h1, h2, h3, joinF_inl, joinF_inr, photonPropagator_neg]
    · rw [h1, h2, h3, joinF_inl, joinF_inr, photonPropagator_swap]
  rw [Finset.prod_congr rfl fun l _ => hL l, Finset.prod_congr rfl fun l _ => hR l, hD]
  ring

open scoped Classical in
include hw₁ hP in
/-- **The amplitude of `glueP` factorizes** over the bridge indices `ν` (the photon index of
`C₁`) and `ρ` (the second photon index of `C₂`). -/
theorem contractionAmplitude_glueP {x y : Wick.FermionVertex (leftKinds κ e)}
    (hx : C₁.1.1 (.inl 0) = .inr x) (hy : C₁.1.1 (.inr y) = .inl 0) (φ : Flavoring F κ)
    (g : Grading κ) (pIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude P Φ D (glueP e C₁ C₂) φ g pIn ![q]
        ((lineSplitP C₁ C₂ hw he hb).splitMom k₁ k₂ Pm) αOut βIn μ =
      ∑ ν, ∑ ρ, contractionAmplitude P Φ D C₁ (flL κ e φ) (gradL κ e g) pIn ![q] k₁ αOut βIn ![ν] *
        ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε q ν ρ) *
        contractionAmplitude P Φ D C₂ (flR κ e φ) (gradR κ e g) ![] ![q, -q] k₂ ![] ![]
          ![μ 0, ρ] := by
  have hI₁ : ∀ ν (v : IdxAsg (leftKinds κ e)), IndOf C₁ αOut βIn ![ν] v.1 v.2.1 v.2.2 ↔
      v.2.2 (extSlot C₁) = ν ∧ (v.1 x = αOut 0 ∧ v.2.1 y = βIn 0) := by
    intro ν v
    unfold IndOf
    rw [extOut_iff hx, extIn_iff hy, extPh_iff (extSlot_spec C₁)]
    simp only [Matrix.cons_val_fin_one]
    tauto
  have hI₂ : ∀ ρ (v : IdxAsg (rightKinds κ e)), IndOf C₂ ![] ![] ![μ 0, ρ] v.1 v.2.1 v.2.2 ↔
      v.2.2 w₂ = ρ ∧ v.2.2 w₁ = μ 0 := by
    intro ρ v
    unfold IndOf
    simp only [IsEmpty.forall_iff, implies_true, true_and]
    constructor
    · intro h
      exact ⟨h 1 w₂ hw, h 0 w₁ hw₁⟩
    · rintro ⟨h1, h0⟩ j s hs
      fin_cases j
      · have hs' : C₂.1.2 (.inl 0) = .inr s := hs
        rw [hw₁] at hs'
        rw [← Sum.inr_injective hs']
        exact h0
      · have hs' : C₂.1.2 (.inl 1) = .inr s := hs
        rw [hw] at hs'
        rw [← Sum.inr_injective hs']
        exact h1
  have hIG : ∀ v₁ v₂, IndOf (glueP e C₁ C₂) αOut βIn μ (joinT κ e v₁ v₂).1
      (joinT κ e v₁ v₂).2.1 (joinT κ e v₁ v₂).2.2 ↔
        (v₁.1 x = αOut 0 ∧ v₁.2.1 y = βIn 0) ∧ v₂.2.2 w₁ = μ 0 := by
    intro v₁ v₂
    unfold IndOf
    have hx' : (glueP e C₁ C₂).1.1 (.inl 0) = .inr (fvSplit κ e (.inl x)) := by
      rw [glueP_ext_fermion, hx]
      rfl
    have hy' : (glueP e C₁ C₂).1.1 (.inr (fvSplit κ e (.inl y))) = .inl 0 :=
      (glueP_inl_iff C₁ C₂ y 0).2 hy
    rw [extOut_iff hx', extIn_iff hy', extPh_iff (glueP_ext_w₁ C₁ C₂ hw₁)]
    simp only [joinT, joinF_inl, joinF_inr]
    tauto
  rw [contractionAmplitude_eq_sum, sum_joinT]
  symm
  refine glue_sum_algebra
    (fun v => (if v.1 x = αOut 0 ∧ v.2.1 y = βIn 0 then 1 else 0) *
      bodyOf P Φ D C₁ (flL κ e φ) (gradL κ e g) pIn ![q] k₁ v.1 v.2.1 v.2.2)
    (fun v => (if v.2.2 w₁ = μ 0 then 1 else 0) *
      bodyOf P Φ D C₂ (flR κ e φ) (gradR κ e g) ![] ![q, -q] k₂ v.1 v.2.1 v.2.2)
    (fun v => v.2.2 (extSlot C₁)) (fun v => v.2.2 w₂)
    (fun ν ρ => (1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε q ν ρ)
    _ _ (fun ν => ?_) (fun ρ => ?_) |>.trans (Finset.sum_congr rfl fun v₁ _ =>
      Finset.sum_congr rfl fun v₂ _ => ?_)
  · rw [contractionAmplitude_eq_sum]
    exact Finset.sum_congr rfl fun v _ => by rw [if_congr (hI₁ ν v) rfl rfl, ite_and_one_mul]
  · rw [contractionAmplitude_eq_sum]
    exact Finset.sum_congr rfl fun v _ => by rw [if_congr (hI₂ ρ v) rfl rfl, ite_and_one_mul]
  · rw [bodyOf_glueP P Φ D C₁ C₂ hw₁ hw he hb k₁ k₂ hP, if_congr (hIG v₁ v₂) rfl rfl,
      ite_split_mul]

end QED.GradedProof.X1C

end
