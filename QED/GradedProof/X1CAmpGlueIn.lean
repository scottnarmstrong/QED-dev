/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CAmpGen
public import QED.GradedProof.X1CPhotonMom

/-!
# (X₁) piece C: the amplitude of `glueIn` factorizes

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C3 (value factorization).

At the split assignment of `lineSplitIn` (line momenta `k₁`, `k₂` of the pieces, bridge momentum
`r`), the amplitude (G₃) of `glueIn e C₁ C₂` with the flavouring `φ` and grading `g` is
`∑_{γ δ} A₁(…, βIn = γ) · (1/i) S̃_{γδ}(r) · A₂(αOut = δ, …)`, with the amplitudes of the pieces
at the flavourings `flL φ`, `flR φ`, the gradings `gradL g`, `gradR g`, the incoming momentum `r`
for `C₁`, and the bridge mass of the flavour of the bridge (`contractionAmplitude_glueIn`).

* `extOut_iff`, `extIn_iff`, `lorOK_glue_iff`: the external index conditions of a piece and of
  the glued contraction.
* `bodyOf_glueIn`: the product of the vertex and line factors of the glue at a joined index
  assignment is the product of those of the pieces and the bridge propagator.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X1C

open QED.WickModel (Params Contraction Line FermionLine PhotonLine psiMomentum₂ photonMomentum₂)
open QED.Graded

variable {N N₁ N₂ nA : ℕ} {F : Type} {κ : Fin N → Wick.VertexKind}
  {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}

/-! ### External index conditions -/

theorem extOut_iff {M nA' : ℕ} {κ' : Fin M → Wick.VertexKind} {C : Contraction 1 nA' κ'}
    {x : Wick.FermionVertex κ'} (hx : C.1.1 (.inl 0) = .inr x) (α : Wick.FermionVertex κ' → Fin 4)
    (αOut : Fin 1 → Fin 4) :
    (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ↔ α x = αOut 0 := by
  constructor
  · exact fun h => h 0 x hx
  · intro h i t ht
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [hx] at ht
    rwa [← Sum.inr_injective ht]

theorem extIn_iff {M nA' : ℕ} {κ' : Fin M → Wick.VertexKind} {C : Contraction 1 nA' κ'}
    {a : Wick.FermionVertex κ'} (ha : C.1.1 (.inr a) = .inl 0) (β : Wick.FermionVertex κ' → Fin 4)
    (βIn : Fin 1 → Fin 4) :
    (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ↔ β a = βIn 0 := by
  constructor
  · exact fun h => h a 0 ha
  · intro h t i ht
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rwa [Sum.inr_injective (C.1.1.injective (ht.trans ha.symm))]

theorem lorOK_glue_iff {nf₁ nf₂ nf : ℕ} {C₁ : Contraction nf₁ nA (leftKinds κ e)}
    {C₂ : Contraction nf₂ 0 (rightKinds κ e)} {C : Contraction nf nA κ}
    (hC : C.1.2 = dsum (pL κ e nA) C₁.1.2 C₂.1.2) (μ : Fin nA → Fin 4)
    (lor₁ : Wick.PhotonSlot (leftKinds κ e) → Fin 4)
    (lor₂ : Wick.PhotonSlot (rightKinds κ e) → Fin 4) :
    (∀ j s, C.1.2 (.inl j) = .inr s → joinF (psSplit κ e) lor₁ lor₂ s = μ j) ↔
      ∀ j s, C₁.1.2 (.inl j) = .inr s → lor₁ s = μ j := by
  constructor
  · intro h j s hs
    have := h j _ ((photon_inl_left_iff hC j s).2 hs)
    rwa [joinF_inl] at this
  · intro h j s hs
    obtain ⟨x, rfl⟩ := (psSplit κ e).surjective s
    rcases x with s | s
    · rw [joinF_inl]
      exact h j s ((photon_inl_left_iff hC j s).1 hs)
    · exact absurd hs (photon_inl_ne_right hC j s)

theorem ite_split_mul (p q : Prop) [Decidable p] [Decidable q] (a b c : ℂ) :
    (if p ∧ q then (1 : ℂ) else 0) * (a * b * c) =
      ((if p then 1 else 0) * a) * (b * ((if q then 1 else 0) * c)) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
  ring

theorem ite_and_one_mul (p q : Prop) [Decidable p] [Decidable q] (b : ℂ) :
    (if p ∧ q then (1 : ℂ) else 0) * b = if p then (if q then 1 else 0) * b else 0 := by
  by_cases hp : p <;> simp [hp]

/-- The sums over the two bridge indices of a glued amplitude. -/
theorem glue_sum_algebra {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂] (F₁ : V₁ → ℂ) (F₂ : V₂ → ℂ)
    (p : V₁ → Fin 4) (q : V₂ → Fin 4) (B : Fin 4 → Fin 4 → ℂ) (X Y : Fin 4 → ℂ)
    (hX : ∀ γ, X γ = ∑ v, if p v = γ then F₁ v else 0)
    (hY : ∀ δ, Y δ = ∑ v, if q v = δ then F₂ v else 0) :
    ∑ γ, ∑ δ, X γ * B γ δ * Y δ = ∑ v₁, ∑ v₂, F₁ v₁ * (B (p v₁) (q v₂) * F₂ v₂) := by
  simp_rw [mul_assoc, ← Finset.mul_sum, hX, collapse_left, hY, collapse_right]

/-! ### The vertex and line factors of `glueIn` -/

section GlueIn

variable (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
  (C₁ : Contraction 1 nA (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e))
  {a : Wick.FermionVertex (leftKinds κ e)} {c : Wick.FermionVertex (rightKinds κ e)}
  (ha : C₁.1.1 (.inr a) = .inl 0) (hc : C₂.1.1 (.inl 0) = .inr c) (he : IsShuffle e)

/-- **The vertex and line factors of `glueIn` at a joined index assignment** are those of the
pieces times the bridge propagator. -/
theorem bodyOf_glueIn (φ : Flavoring F κ) (g : Grading κ) (pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (k₁ : Line C₁ → Fin 4 → ℝ) (k₂ : Line C₂ → Fin 4 → ℝ)
    (r : Fin 4 → ℝ) (v₁ : IdxAsg (leftKinds κ e)) (v₂ : IdxAsg (rightKinds κ e)) :
    bodyOf P Φ D (glueIn e C₁ C₂) φ g pIn kIn ((lineSplitIn C₁ C₂ ha hc he).splitMom k₁ k₂ r)
        (joinT κ e v₁ v₂).1 (joinT κ e v₁ v₂).2.1 (joinT κ e v₁ v₂).2.2 =
      bodyOf P Φ D C₁ (flL κ e φ) (gradL κ e g) ![r] kIn k₁ v₁.1 v₁.2.1 v₁.2.2 *
        ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass (flL κ e φ a)) P.ε r (v₁.2.1 a)
          (v₂.1 c)) *
        bodyOf P Φ D C₂ (flR κ e φ) (gradR κ e g) pIn ![] k₂ v₂.1 v₂.2.1 v₂.2.2 := by
  obtain ⟨α₁, β₁, l₁⟩ := v₁
  obtain ⟨α₂, β₂, l₂⟩ := v₂
  simp only [joinT]
  rw [bodyOf_eq, bodyOf_eq, bodyOf_eq, prod_split_vertices e,
    prod_lines_split (lineSplitIn C₁ C₂ ha hc he)]
  simp only [vtxOf_split_left, vtxOf_split_right, joinF_inl, joinF_inr,
    psiMomentum₂_glueIn_left C₁ C₂ ha hc he, psiMomentum₂_glueIn_right C₁ C₂ ha hc he,
    photonMomentum₂_glueIn_left C₁ C₂ ha hc he, photonMomentum₂_glueIn_right C₁ C₂ ha hc he]
  have hL : ∀ l : Line C₁, lineFac P Φ φ ((lineSplitIn C₁ C₂ ha hc he).splitMom k₁ k₂ r)
      (joinF (fvSplit κ e) α₁ α₂) (joinF (fvSplit κ e) β₁ β₂) (joinF (psSplit κ e) l₁ l₂)
      ((lineSplitIn C₁ C₂ ha hc he).equiv (.inl l)) = lineFac P Φ (flL κ e φ) k₁ α₁ β₁ l₁ l := by
    rintro (f | g')
    · have hk := (lineSplitIn C₁ C₂ ha hc he).splitMom_left k₁ k₂ r (.inl f)
      have ht := fermionLineIn_left_tail C₁ C₂ ha hc f
      rw [lineSplitIn_left_fermion] at hk
      rw [lineSplitIn_left_fermion]
      simp only [lineFac, Sum.elim_inl]
      rw [hk]
      simp only [fermionLineIn] at ht
      rw [ht, joinF_inl, joinF_inl]
      rfl
    · have hk := (lineSplitIn C₁ C₂ ha hc he).splitMom_left k₁ k₂ r (.inr g')
      obtain ⟨h1, h2⟩ := photonLineMap_left (C := glueIn e C₁ C₂) (C₁ := C₁) (C₂ := C₂) rfl he g'
      rw [lineSplitIn_left_photon] at hk
      rw [lineSplitIn_left_photon]
      simp only [lineFac, Sum.elim_inr]
      rw [hk, h1, h2, joinF_inl, joinF_inl]
  have hR : ∀ l : Line C₂, lineFac P Φ φ ((lineSplitIn C₁ C₂ ha hc he).splitMom k₁ k₂ r)
      (joinF (fvSplit κ e) α₁ α₂) (joinF (fvSplit κ e) β₁ β₂) (joinF (psSplit κ e) l₁ l₂)
      ((lineSplitIn C₁ C₂ ha hc he).equiv (.inr (.inl l))) =
        lineFac P Φ (flR κ e φ) k₂ α₂ β₂ l₂ l := by
    rintro (f | g')
    · have hk := (lineSplitIn C₁ C₂ ha hc he).splitMom_right k₁ k₂ r (.inl f)
      have ht := fermionLineIn_right_tail C₁ C₂ ha hc f
      rw [lineSplitIn_right_fermion] at hk
      rw [lineSplitIn_right_fermion]
      simp only [lineFac, Sum.elim_inl]
      rw [hk]
      simp only [fermionLineIn] at ht
      rw [ht, joinF_inr, joinF_inr]
      rfl
    · have hk := (lineSplitIn C₁ C₂ ha hc he).splitMom_right k₁ k₂ r (.inr g')
      obtain ⟨h1, h2⟩ :=
        photonLineMap_right (C := glueIn e C₁ C₂) (C₁ := C₁) (C₂ := C₂) rfl he g'
      rw [lineSplitIn_right_photon] at hk
      rw [lineSplitIn_right_photon]
      simp only [lineFac, Sum.elim_inr]
      rw [hk, h1, h2, joinF_inr, joinF_inr]
  have hB := (lineSplitIn C₁ C₂ ha hc he).splitMom_bridge k₁ k₂ r
  have htB := fermionLineIn_bridge_tail C₁ C₂ ha hc
  rw [lineSplitIn_bridge] at hB
  simp only [fermionLineIn] at htB
  rw [Finset.prod_congr rfl fun l _ => hL l, Finset.prod_congr rfl fun l _ => hR l,
    lineSplitIn_bridge]
  simp only [lineFac, Sum.elim_inl]
  rw [hB, htB, joinF_inl, joinF_inr]
  simp only [flL]
  ring

open scoped Classical in
/-- **The amplitude of `glueIn` factorizes** over the bridge indices `γ` (row of the bridge
propagator, the incoming index of `C₁`) and `δ` (the outgoing index of `C₂`). -/
theorem contractionAmplitude_glueIn {x : Wick.FermionVertex (leftKinds κ e)}
    {y : Wick.FermionVertex (rightKinds κ e)} (hx : C₁.1.1 (.inl 0) = .inr x)
    (hy : C₂.1.1 (.inr y) = .inl 0) (φ : Flavoring F κ) (g : Grading κ)
    (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k₁ : Line C₁ → Fin 4 → ℝ)
    (k₂ : Line C₂ → Fin 4 → ℝ) (r : Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) :
    contractionAmplitude P Φ D (glueIn e C₁ C₂) φ g pIn kIn
        ((lineSplitIn C₁ C₂ ha hc he).splitMom k₁ k₂ r) αOut βIn μ =
      ∑ γ, ∑ δ, contractionAmplitude P Φ D C₁ (flL κ e φ) (gradL κ e g) ![r] kIn k₁ αOut ![γ] μ *
        ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass (flL κ e φ a)) P.ε r γ δ) *
        contractionAmplitude P Φ D C₂ (flR κ e φ) (gradR κ e g) pIn ![] k₂ ![δ] βIn ![] := by
  have hI₁ : ∀ γ (v : IdxAsg (leftKinds κ e)), IndOf C₁ αOut ![γ] μ v.1 v.2.1 v.2.2 ↔
      v.2.1 a = γ ∧ (v.1 x = αOut 0 ∧ ∀ j s, C₁.1.2 (.inl j) = .inr s → v.2.2 s = μ j) := by
    intro γ v
    unfold IndOf
    rw [extOut_iff hx, extIn_iff ha]
    simp only [Matrix.cons_val_fin_one]
    tauto
  have hI₂ : ∀ δ (v : IdxAsg (rightKinds κ e)), IndOf C₂ ![δ] βIn ![] v.1 v.2.1 v.2.2 ↔
      v.1 c = δ ∧ v.2.1 y = βIn 0 := by
    intro δ v
    unfold IndOf
    rw [extOut_iff hc, extIn_iff hy]
    simp only [Matrix.cons_val_fin_one, IsEmpty.forall_iff, and_true]
  have hIG : ∀ v₁ v₂, IndOf (glueIn e C₁ C₂) αOut βIn μ (joinT κ e v₁ v₂).1
      (joinT κ e v₁ v₂).2.1 (joinT κ e v₁ v₂).2.2 ↔
        (v₁.1 x = αOut 0 ∧ ∀ j s, C₁.1.2 (.inl j) = .inr s → v₁.2.2 s = μ j) ∧
          v₂.2.1 y = βIn 0 := by
    intro v₁ v₂
    unfold IndOf
    have hx' : (glueIn e C₁ C₂).1.1 (.inl 0) = .inr (fvSplit κ e (.inl x)) := by
      have h := glueIn_left C₁ C₂ hx
      rwa [fL_inl_inl] at h
    have hy' : (glueIn e C₁ C₂).1.1 (.inr (fvSplit κ e (.inr y))) = .inl 0 := by
      rw [glueIn_right, hy, fR_inr_inl]
    rw [extOut_iff hx', extIn_iff hy']
    simp only [joinT, joinF_inl, joinF_inr]
    rw [lorOK_glue_iff (C := glueIn e C₁ C₂) rfl]
    tauto
  rw [contractionAmplitude_eq_sum, sum_joinT]
  symm
  refine glue_sum_algebra
    (fun v => (if v.1 x = αOut 0 ∧ ∀ j s, C₁.1.2 (.inl j) = .inr s → v.2.2 s = μ j then 1 else 0) *
      bodyOf P Φ D C₁ (flL κ e φ) (gradL κ e g) ![r] kIn k₁ v.1 v.2.1 v.2.2)
    (fun v => (if v.2.1 y = βIn 0 then 1 else 0) *
      bodyOf P Φ D C₂ (flR κ e φ) (gradR κ e g) pIn ![] k₂ v.1 v.2.1 v.2.2)
    (fun v => v.2.1 a) (fun v => v.1 c)
    (fun γ δ => (1 / I) * QED.OneLoop.electronPropagator (Φ.mass (flL κ e φ a)) P.ε r γ δ)
    _ _ (fun γ => ?_) (fun δ => ?_) |>.trans (Finset.sum_congr rfl fun v₁ _ =>
      Finset.sum_congr rfl fun v₂ _ => ?_)
  · rw [contractionAmplitude_eq_sum]
    exact Finset.sum_congr rfl fun v _ => by rw [if_congr (hI₁ γ v) rfl rfl, ite_and_one_mul]
  · rw [contractionAmplitude_eq_sum]
    exact Finset.sum_congr rfl fun v _ => by rw [if_congr (hI₂ δ v) rfl rfl, ite_and_one_mul]
  · rw [bodyOf_glueIn P Φ D C₁ C₂ ha hc he, if_congr (hIG v₁ v₂) rfl rfl, ite_split_mul]

end GlueIn

end QED.GradedProof.X1C

end
