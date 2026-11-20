/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CAmpGlueIn
public import QED.GradedProof.X1CLinesOut

/-!
# (X₁) piece C: the amplitude of `glueOut` factorizes

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C3 (value factorization); the mirror of `X1CAmpGlueIn`.

At the split assignment of `lineSplitOut` (bridge momentum `r'`), the amplitude (G₃) of
`glueOut e C₁ C₂` is `∑_{γ δ} A₂(…, βIn = γ) · (1/i) S̃_{γδ}(r') · A₁(αOut = δ, …)`: the
self-energy piece `C₂` (incoming momentum `r'`) carries the outgoing external, `C₁` the incoming
one and the photon (`contractionAmplitude_glueOut`).
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X1C

open QED.WickModel (Params Contraction Line FermionLine PhotonLine psiMomentum₂ photonMomentum₂)
open QED.Graded

variable {N N₁ N₂ nA : ℕ} {F : Type} {κ : Fin N → Wick.VertexKind}
  {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}
  (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
  (C₁ : Contraction 1 nA (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e))
  {a : Wick.FermionVertex (leftKinds κ e)} {c : Wick.FermionVertex (rightKinds κ e)}
  (ha : C₁.1.1 (.inl 0) = .inr a) (hc : C₂.1.1 (.inr c) = .inl 0) (he : IsShuffle e)

/-! ### The lines and momenta of `glueOut` -/

theorem lineSplitOut_left_fermion (f : FermionLine C₁) :
    (lineSplitOut C₁ C₂ ha hc he).equiv (.inl (.inl f)) =
      .inl ⟨fvSplit κ e (.inl f.1), (fermionLineOut C₁ C₂ ha hc (.inl f)).2⟩ := rfl

theorem lineSplitOut_right_fermion (f : FermionLine C₂) :
    (lineSplitOut C₁ C₂ ha hc he).equiv (.inr (.inl (.inl f))) =
      .inl ⟨fvSplit κ e (.inr f.1), (fermionLineOut C₁ C₂ ha hc (.inr (.inl f))).2⟩ := rfl

theorem lineSplitOut_bridge :
    (lineSplitOut C₁ C₂ ha hc he).equiv (.inr (.inr ())) =
      .inl ⟨fvSplit κ e (.inr c), (fermionLineOut C₁ C₂ ha hc (.inr (.inr ()))).2⟩ := rfl

theorem lineSplitOut_left_photon (g : PhotonLine C₁) :
    (lineSplitOut C₁ C₂ ha hc he).equiv (.inl (.inr g)) =
      .inr (photonLineMap (C := glueOut e C₁ C₂) rfl he (.inl g)) := rfl

theorem lineSplitOut_right_photon (g : PhotonLine C₂) :
    (lineSplitOut C₁ C₂ ha hc he).equiv (.inr (.inl (.inr g))) =
      .inr (photonLineMap (C := glueOut e C₁ C₂) rfl he (.inr g)) := rfl

variable (k₁ : Line C₁ → Fin 4 → ℝ) (k₂ : Line C₂ → Fin 4 → ℝ) (r' : Fin 4 → ℝ)

theorem psiMomentum₂_glueOut_left (pIn : Fin 1 → Fin 4 → ℝ)
    (s : Wick.FermionVertex (leftKinds κ e)) :
    psiMomentum₂ (glueOut e C₁ C₂) pIn ((lineSplitOut C₁ C₂ ha hc he).splitMom k₁ k₂ r')
        (fvSplit κ e (.inl s)) = psiMomentum₂ C₁ pIn k₁ s := by
  rcases h : C₁.1.1 (.inr s) with i | s'
  · rw [QED.TwoLoop.Relabel.psiMomentum₂_of_inl h,
      QED.TwoLoop.Relabel.psiMomentum₂_of_inl (show (glueOut e C₁ C₂).1.1
        (.inr (fvSplit κ e (.inl s))) = .inl i by rw [glueOut_left, h]; rfl)]
  · have hf : (C₁.1.1 (.inr s)).isRight := by rw [h]; rfl
    have hG : ((glueOut e C₁ C₂).1.1 (.inr (fvSplit κ e (.inl s)))).isRight := by
      rw [glueOut_left' C₁ C₂ h]; rfl
    rw [QED.TwoLoop.Relabel.psiMomentum₂_of_isRight hf,
      QED.TwoLoop.Relabel.psiMomentum₂_of_isRight hG]
    have h := LineSplit.splitMom_left (lineSplitOut C₁ C₂ ha hc he) k₁ k₂ r' (.inl ⟨s, hf⟩)
    rw [lineSplitOut_left_fermion] at h
    exact h

theorem psiMomentum₂_glueOut_right (pIn : Fin 1 → Fin 4 → ℝ)
    (s : Wick.FermionVertex (rightKinds κ e)) :
    psiMomentum₂ (glueOut e C₁ C₂) pIn ((lineSplitOut C₁ C₂ ha hc he).splitMom k₁ k₂ r')
        (fvSplit κ e (.inr s)) = psiMomentum₂ C₂ ![r'] k₂ s := by
  by_cases hs : s = c
  · subst hs
    have hG : ((glueOut e C₁ C₂).1.1 (.inr (fvSplit κ e (.inr s)))).isRight := by
      rw [glueOut_bridge C₁ C₂ ha hc]; rfl
    rw [QED.TwoLoop.Relabel.psiMomentum₂_of_inl hc, QED.TwoLoop.Relabel.psiMomentum₂_of_isRight hG]
    have h := LineSplit.splitMom_bridge (lineSplitOut C₁ C₂ ha hc he) k₁ k₂ r'
    rw [lineSplitOut_bridge] at h
    exact h
  · obtain ⟨s', hs'⟩ : ∃ s', C₂.1.1 (.inr s) = .inr s' := by
      rcases h : C₂.1.1 (.inr s) with i | s'
      · refine absurd ?_ hs
        have := h.trans ((congrArg Sum.inl (Subsingleton.elim i 0)).trans hc.symm)
        exact Sum.inr_injective (C₂.1.1.injective this)
      · exact ⟨s', rfl⟩
    have hf : (C₂.1.1 (.inr s)).isRight := by rw [hs']; rfl
    have hG : ((glueOut e C₁ C₂).1.1 (.inr (fvSplit κ e (.inr s)))).isRight := by
      rw [glueOut_right' C₁ C₂ hs']; rfl
    rw [QED.TwoLoop.Relabel.psiMomentum₂_of_isRight hf,
      QED.TwoLoop.Relabel.psiMomentum₂_of_isRight hG]
    have h := LineSplit.splitMom_right (lineSplitOut C₁ C₂ ha hc he) k₁ k₂ r' (.inl ⟨s, hf⟩)
    rw [lineSplitOut_right_fermion] at h
    exact h

theorem photonMomentum₂_glueOut_left (kIn : Fin nA → Fin 4 → ℝ)
    (s : Wick.PhotonSlot (leftKinds κ e)) :
    photonMomentum₂ (glueOut e C₁ C₂) kIn ((lineSplitOut C₁ C₂ ha hc he).splitMom k₁ k₂ r')
        (psSplit κ e (.inl s)) = photonMomentum₂ C₁ kIn k₁ s :=
  photonMomentum₂_split_left rfl he kIn (fun g => by
    have h := LineSplit.splitMom_left (lineSplitOut C₁ C₂ ha hc he) k₁ k₂ r' (.inr g)
    rwa [lineSplitOut_left_photon] at h) s

theorem photonMomentum₂_glueOut_right (kIn : Fin nA → Fin 4 → ℝ)
    (s : Wick.PhotonSlot (rightKinds κ e)) :
    photonMomentum₂ (glueOut e C₁ C₂) kIn ((lineSplitOut C₁ C₂ ha hc he).splitMom k₁ k₂ r')
        (psSplit κ e (.inr s)) = photonMomentum₂ C₂ ![] k₂ s :=
  photonMomentum₂_split_right rfl he kIn (fun g => by
    have h := LineSplit.splitMom_right (lineSplitOut C₁ C₂ ha hc he) k₁ k₂ r' (.inr g)
    rwa [lineSplitOut_right_photon] at h) s

/-! ### The vertex and line factors of `glueOut` -/

/-- **The vertex and line factors of `glueOut` at a joined index assignment.** -/
theorem bodyOf_glueOut (φ : Flavoring F κ) (g : Grading κ) (pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (v₁ : IdxAsg (leftKinds κ e)) (v₂ : IdxAsg (rightKinds κ e)) :
    bodyOf P Φ D (glueOut e C₁ C₂) φ g pIn kIn ((lineSplitOut C₁ C₂ ha hc he).splitMom k₁ k₂ r')
        (joinT κ e v₁ v₂).1 (joinT κ e v₁ v₂).2.1 (joinT κ e v₁ v₂).2.2 =
      bodyOf P Φ D C₂ (flR κ e φ) (gradR κ e g) ![r'] ![] k₂ v₂.1 v₂.2.1 v₂.2.2 *
        ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass (flR κ e φ c)) P.ε r' (v₂.2.1 c)
          (v₁.1 a)) *
        bodyOf P Φ D C₁ (flL κ e φ) (gradL κ e g) pIn kIn k₁ v₁.1 v₁.2.1 v₁.2.2 := by
  obtain ⟨α₁, β₁, l₁⟩ := v₁
  obtain ⟨α₂, β₂, l₂⟩ := v₂
  simp only [joinT]
  rw [bodyOf_eq, bodyOf_eq, bodyOf_eq, prod_split_vertices e,
    prod_lines_split (lineSplitOut C₁ C₂ ha hc he)]
  simp only [vtxOf_split_left, vtxOf_split_right, joinF_inl, joinF_inr,
    psiMomentum₂_glueOut_left C₁ C₂ ha hc he, psiMomentum₂_glueOut_right C₁ C₂ ha hc he,
    photonMomentum₂_glueOut_left C₁ C₂ ha hc he, photonMomentum₂_glueOut_right C₁ C₂ ha hc he]
  have hL : ∀ l : Line C₁, lineFac P Φ φ ((lineSplitOut C₁ C₂ ha hc he).splitMom k₁ k₂ r')
      (joinF (fvSplit κ e) α₁ α₂) (joinF (fvSplit κ e) β₁ β₂) (joinF (psSplit κ e) l₁ l₂)
      ((lineSplitOut C₁ C₂ ha hc he).equiv (.inl l)) = lineFac P Φ (flL κ e φ) k₁ α₁ β₁ l₁ l := by
    rintro (f | g')
    · have hk := (lineSplitOut C₁ C₂ ha hc he).splitMom_left k₁ k₂ r' (.inl f)
      have ht := fermionLineOut_left_tail C₁ C₂ ha hc f
      rw [lineSplitOut_left_fermion] at hk
      rw [lineSplitOut_left_fermion]
      simp only [lineFac, Sum.elim_inl]
      rw [hk]
      simp only [fermionLineOut] at ht
      rw [ht, joinF_inl, joinF_inl]
      rfl
    · have hk := (lineSplitOut C₁ C₂ ha hc he).splitMom_left k₁ k₂ r' (.inr g')
      obtain ⟨h1, h2⟩ :=
        photonLineMap_left (C := glueOut e C₁ C₂) (C₁ := C₁) (C₂ := C₂) rfl he g'
      rw [lineSplitOut_left_photon] at hk
      rw [lineSplitOut_left_photon]
      simp only [lineFac, Sum.elim_inr]
      rw [hk, h1, h2, joinF_inl, joinF_inl]
  have hR : ∀ l : Line C₂, lineFac P Φ φ ((lineSplitOut C₁ C₂ ha hc he).splitMom k₁ k₂ r')
      (joinF (fvSplit κ e) α₁ α₂) (joinF (fvSplit κ e) β₁ β₂) (joinF (psSplit κ e) l₁ l₂)
      ((lineSplitOut C₁ C₂ ha hc he).equiv (.inr (.inl l))) =
        lineFac P Φ (flR κ e φ) k₂ α₂ β₂ l₂ l := by
    rintro (f | g')
    · have hk := (lineSplitOut C₁ C₂ ha hc he).splitMom_right k₁ k₂ r' (.inl f)
      have ht := fermionLineOut_right_tail C₁ C₂ ha hc f
      rw [lineSplitOut_right_fermion] at hk
      rw [lineSplitOut_right_fermion]
      simp only [lineFac, Sum.elim_inl]
      rw [hk]
      simp only [fermionLineOut] at ht
      rw [ht, joinF_inr, joinF_inr]
      rfl
    · have hk := (lineSplitOut C₁ C₂ ha hc he).splitMom_right k₁ k₂ r' (.inr g')
      obtain ⟨h1, h2⟩ :=
        photonLineMap_right (C := glueOut e C₁ C₂) (C₁ := C₁) (C₂ := C₂) rfl he g'
      rw [lineSplitOut_right_photon] at hk
      rw [lineSplitOut_right_photon]
      simp only [lineFac, Sum.elim_inr]
      rw [hk, h1, h2, joinF_inr, joinF_inr]
  have hB := (lineSplitOut C₁ C₂ ha hc he).splitMom_bridge k₁ k₂ r'
  have htB := fermionLineOut_bridge_tail C₁ C₂ ha hc
  rw [lineSplitOut_bridge] at hB
  simp only [fermionLineOut] at htB
  rw [Finset.prod_congr rfl fun l _ => hL l, Finset.prod_congr rfl fun l _ => hR l,
    lineSplitOut_bridge]
  simp only [lineFac, Sum.elim_inl]
  rw [hB, htB, joinF_inl, joinF_inr]
  simp only [flR]
  ring

open scoped Classical in
/-- **The amplitude of `glueOut` factorizes** over the bridge indices `γ` (the incoming index of
`C₂`) and `δ` (the outgoing index of `C₁`). -/
theorem contractionAmplitude_glueOut {x : Wick.FermionVertex (rightKinds κ e)}
    {y : Wick.FermionVertex (leftKinds κ e)} (hx : C₂.1.1 (.inl 0) = .inr x)
    (hy : C₁.1.1 (.inr y) = .inl 0) (φ : Flavoring F κ) (g : Grading κ)
    (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) :
    contractionAmplitude P Φ D (glueOut e C₁ C₂) φ g pIn kIn
        ((lineSplitOut C₁ C₂ ha hc he).splitMom k₁ k₂ r') αOut βIn μ =
      ∑ γ, ∑ δ, contractionAmplitude P Φ D C₂ (flR κ e φ) (gradR κ e g) ![r'] ![] k₂ αOut ![γ] ![] *
        ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass (flR κ e φ c)) P.ε r' γ δ) *
        contractionAmplitude P Φ D C₁ (flL κ e φ) (gradL κ e g) pIn kIn k₁ ![δ] βIn μ := by
  have hI₂ : ∀ γ (v : IdxAsg (rightKinds κ e)), IndOf C₂ αOut ![γ] ![] v.1 v.2.1 v.2.2 ↔
      v.2.1 c = γ ∧ v.1 x = αOut 0 := by
    intro γ v
    unfold IndOf
    rw [extOut_iff hx, extIn_iff hc]
    simp only [Matrix.cons_val_fin_one, IsEmpty.forall_iff, and_true]
    tauto
  have hI₁ : ∀ δ (v : IdxAsg (leftKinds κ e)), IndOf C₁ ![δ] βIn μ v.1 v.2.1 v.2.2 ↔
      v.1 a = δ ∧ (v.2.1 y = βIn 0 ∧ ∀ j s, C₁.1.2 (.inl j) = .inr s → v.2.2 s = μ j) := by
    intro δ v
    unfold IndOf
    rw [extOut_iff ha, extIn_iff hy]
    simp only [Matrix.cons_val_fin_one]
  have hIG : ∀ v₁ v₂, IndOf (glueOut e C₁ C₂) αOut βIn μ (joinT κ e v₁ v₂).1
      (joinT κ e v₁ v₂).2.1 (joinT κ e v₁ v₂).2.2 ↔
        v₂.1 x = αOut 0 ∧
          (v₁.2.1 y = βIn 0 ∧ ∀ j s, C₁.1.2 (.inl j) = .inr s → v₁.2.2 s = μ j) := by
    intro v₁ v₂
    unfold IndOf
    have hx' : (glueOut e C₁ C₂).1.1 (.inl 0) = .inr (fvSplit κ e (.inr x)) := by
      have h := glueOut_right C₁ C₂ hx
      rwa [fR_inr_inl] at h
    have hy' : (glueOut e C₁ C₂).1.1 (.inr (fvSplit κ e (.inl y))) = .inl 0 := by
      rw [glueOut_left, hy, fL_inl_inl]
    rw [extOut_iff hx', extIn_iff hy']
    simp only [joinT, joinF_inl, joinF_inr]
    rw [lorOK_glue_iff (C := glueOut e C₁ C₂) rfl]
  rw [contractionAmplitude_eq_sum, sum_joinT, Finset.sum_comm]
  symm
  refine glue_sum_algebra
    (fun v => (if v.1 x = αOut 0 then 1 else 0) *
      bodyOf P Φ D C₂ (flR κ e φ) (gradR κ e g) ![r'] ![] k₂ v.1 v.2.1 v.2.2)
    (fun v => (if v.2.1 y = βIn 0 ∧ ∀ j s, C₁.1.2 (.inl j) = .inr s → v.2.2 s = μ j then 1
        else 0) * bodyOf P Φ D C₁ (flL κ e φ) (gradL κ e g) pIn kIn k₁ v.1 v.2.1 v.2.2)
    (fun v => v.2.1 c) (fun v => v.1 a)
    (fun γ δ => (1 / I) * QED.OneLoop.electronPropagator (Φ.mass (flR κ e φ c)) P.ε r' γ δ)
    _ _ (fun γ => ?_) (fun δ => ?_) |>.trans (Finset.sum_congr rfl fun v₂ _ =>
      Finset.sum_congr rfl fun v₁ _ => ?_)
  · rw [contractionAmplitude_eq_sum]
    exact Finset.sum_congr rfl fun v _ => by rw [if_congr (hI₂ γ v) rfl rfl, ite_and_one_mul]
  · rw [contractionAmplitude_eq_sum]
    exact Finset.sum_congr rfl fun v _ => by rw [if_congr (hI₁ δ v) rfl rfl, ite_and_one_mul]
  · rw [bodyOf_glueOut P Φ D C₁ C₂ ha hc he, if_congr (hIG v₁ v₂) rfl rfl, ite_split_mul]

end QED.GradedProof.X1C

end
