/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CRouteIn
public import QED.Frozen.TwoLoop.PsiMomentum
public import QED.TwoLoop.RelabelCountertermValue

/-!
# (X₁) piece C: the factors of a split amplitude, and the momenta of `glueIn`

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C3 (value factorization), first part.

* `prod_split_vertices`, `prod_lines_split`, `prod_fermion_photon`: the vertex product of a split
  contraction is the product over the two pieces, and the line product (fermion lines and photon
  lines together) is the product over the lines of the pieces and the bridge, for any `LineSplit`.
* The vertex factors of a piece are the vertex factors of the glued contraction read through the
  split (`rfl`: the kinds of the pieces are `κ ∘ e ∘ inl`, `κ ∘ e ∘ inr`; checked in this file by
  `vertexFactor_split_left`, `vertexFactor_split_right`).
* `psiMomentum₂_glueIn_left`, `_right`: at the split assignment of `glueIn` with bridge momentum
  `r`, the momentum entering a fermion field of a piece is that of the piece, with incoming
  momentum `r` for the left piece.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line FermionLine PhotonLine psiMomentum₂)

variable {N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}

/-! ### Products over a split -/

theorem prod_split_vertices (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N) (G : Fin N → ℂ) :
    ∏ t, G t = (∏ t, G (e (.inl t))) * ∏ t, G (e (.inr t)) := by
  rw [← e.prod_comp, Fintype.prod_sum_type]

theorem prod_lines_split {nf nA nf₁ nA₁ nf₂ nA₂ : ℕ} {C : Contraction nf nA κ}
    {C₁ : Contraction nf₁ nA₁ (leftKinds κ e)} {C₂ : Contraction nf₂ nA₂ (rightKinds κ e)}
    {u w : Fin N} (S : LineSplit C C₁ C₂ u w) (Ψ : Line C → ℂ) :
    ∏ l, Ψ l = (∏ l, Ψ (S.equiv (.inl l))) * (∏ l, Ψ (S.equiv (.inr (.inl l)))) *
      Ψ (S.equiv (.inr (.inr ()))) := by
  rw [← S.equiv.prod_comp, Fintype.prod_sum_type (α₁ := Line C₁) (α₂ := Line C₂ ⊕ Unit),
    Fintype.prod_sum_type (α₁ := Line C₂) (α₂ := Unit)]
  simp only [Fintype.univ_unit, Finset.prod_singleton]
  ring

theorem prod_fermion_photon {nf nA : ℕ} {C : Contraction nf nA κ} (A : FermionLine C → ℂ)
    (B : PhotonLine C → ℂ) :
    (∏ f, A f) * ∏ g, B g = ∏ l : Line C, Sum.elim A B l := by
  rw [Fintype.prod_sum_type (α₁ := FermionLine C) (α₂ := PhotonLine C)]
  rfl

/-! ### Vertex factors of the pieces -/

theorem vertexFactor_split_left (e' δ₁ δ₂ δm δ₃ m : ℝ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (kψ : Wick.FermionVertex κ → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (t : Fin N₁) :
    Wick.vertexFactor e' δ₁ δ₂ δm δ₃ m α β lor kψ kA (e (.inl t)) =
      Wick.vertexFactor (κ := leftKinds κ e) e' δ₁ δ₂ δm δ₃ m
        (fun s => α (fvSplit κ e (.inl s))) (fun s => β (fvSplit κ e (.inl s)))
        (fun a => lor (psSplit κ e (.inl a))) (fun s => kψ (fvSplit κ e (.inl s)))
        (fun a => kA (psSplit κ e (.inl a))) t := rfl

theorem vertexFactor_split_right (e' δ₁ δ₂ δm δ₃ m : ℝ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (kψ : Wick.FermionVertex κ → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (t : Fin N₂) :
    Wick.vertexFactor e' δ₁ δ₂ δm δ₃ m α β lor kψ kA (e (.inr t)) =
      Wick.vertexFactor (κ := rightKinds κ e) e' δ₁ δ₂ δm δ₃ m
        (fun s => α (fvSplit κ e (.inr s))) (fun s => β (fvSplit κ e (.inr s)))
        (fun a => lor (psSplit κ e (.inr a))) (fun s => kψ (fvSplit κ e (.inr s)))
        (fun a => kA (psSplit κ e (.inr a))) t := rfl

/-! ### The momenta of `glueIn` -/

section GlueIn

variable {nA : ℕ} (C₁ : Contraction 1 nA (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e))
  {a : Wick.FermionVertex (leftKinds κ e)} {c : Wick.FermionVertex (rightKinds κ e)}
  (ha : C₁.1.1 (.inr a) = .inl 0) (hc : C₂.1.1 (.inl 0) = .inr c) (he : IsShuffle e)

theorem lineSplitIn_left_fermion (f : FermionLine C₁) :
    (lineSplitIn C₁ C₂ ha hc he).equiv (.inl (.inl f)) =
      .inl ⟨fvSplit κ e (.inl f.1), (fermionLineIn C₁ C₂ ha hc (.inl f)).2⟩ := rfl

theorem lineSplitIn_right_fermion (f : FermionLine C₂) :
    (lineSplitIn C₁ C₂ ha hc he).equiv (.inr (.inl (.inl f))) =
      .inl ⟨fvSplit κ e (.inr f.1), (fermionLineIn C₁ C₂ ha hc (.inr (.inl f))).2⟩ := rfl

theorem lineSplitIn_bridge :
    (lineSplitIn C₁ C₂ ha hc he).equiv (.inr (.inr ())) =
      .inl ⟨fvSplit κ e (.inl a), (fermionLineIn C₁ C₂ ha hc (.inr (.inr ()))).2⟩ := rfl

theorem lineSplitIn_left_photon (g : PhotonLine C₁) :
    (lineSplitIn C₁ C₂ ha hc he).equiv (.inl (.inr g)) =
      .inr (photonLineMap (C := glueIn e C₁ C₂) rfl he (.inl g)) := rfl

theorem lineSplitIn_right_photon (g : PhotonLine C₂) :
    (lineSplitIn C₁ C₂ ha hc he).equiv (.inr (.inl (.inr g))) =
      .inr (photonLineMap (C := glueIn e C₁ C₂) rfl he (.inr g)) := rfl

variable (k₁ : Line C₁ → Fin 4 → ℝ) (k₂ : Line C₂ → Fin 4 → ℝ) (r : Fin 4 → ℝ)

theorem psiMomentum₂_glueIn_left (pIn : Fin 1 → Fin 4 → ℝ)
    (s : Wick.FermionVertex (leftKinds κ e)) :
    psiMomentum₂ (glueIn e C₁ C₂) pIn ((lineSplitIn C₁ C₂ ha hc he).splitMom k₁ k₂ r)
        (fvSplit κ e (.inl s)) = psiMomentum₂ C₁ ![r] k₁ s := by
  by_cases hs : s = a
  · subst hs
    have hG : ((glueIn e C₁ C₂).1.1 (.inr (fvSplit κ e (.inl s)))).isRight := by
      rw [glueIn_bridge C₁ C₂ ha hc]; rfl
    rw [QED.TwoLoop.Relabel.psiMomentum₂_of_inl ha, QED.TwoLoop.Relabel.psiMomentum₂_of_isRight hG]
    have h := LineSplit.splitMom_bridge (lineSplitIn C₁ C₂ ha hc he) k₁ k₂ r
    rw [lineSplitIn_bridge] at h
    exact h
  · obtain ⟨s', hs'⟩ : ∃ s', C₁.1.1 (.inr s) = .inr s' := by
      rcases h : C₁.1.1 (.inr s) with i | s'
      · refine absurd ?_ hs
        have := h.trans ((congrArg Sum.inl (Subsingleton.elim i 0)).trans ha.symm)
        exact Sum.inr_injective (C₁.1.1.injective this)
      · exact ⟨s', rfl⟩
    have hf : (C₁.1.1 (.inr s)).isRight := by rw [hs']; rfl
    have hG : ((glueIn e C₁ C₂).1.1 (.inr (fvSplit κ e (.inl s)))).isRight := by
      rw [glueIn_left' C₁ C₂ hs']; rfl
    rw [QED.TwoLoop.Relabel.psiMomentum₂_of_isRight hf,
      QED.TwoLoop.Relabel.psiMomentum₂_of_isRight hG]
    have h := LineSplit.splitMom_left (lineSplitIn C₁ C₂ ha hc he) k₁ k₂ r (.inl ⟨s, hf⟩)
    rw [lineSplitIn_left_fermion] at h
    exact h

theorem psiMomentum₂_glueIn_right (pIn : Fin 1 → Fin 4 → ℝ)
    (s : Wick.FermionVertex (rightKinds κ e)) :
    psiMomentum₂ (glueIn e C₁ C₂) pIn ((lineSplitIn C₁ C₂ ha hc he).splitMom k₁ k₂ r)
        (fvSplit κ e (.inr s)) = psiMomentum₂ C₂ pIn k₂ s := by
  rcases h : C₂.1.1 (.inr s) with i | s'
  · rw [QED.TwoLoop.Relabel.psiMomentum₂_of_inl h,
      QED.TwoLoop.Relabel.psiMomentum₂_of_inl (show (glueIn e C₁ C₂).1.1
        (.inr (fvSplit κ e (.inr s))) = .inl i by rw [glueIn_right, h]; rfl)]
  · have hf : (C₂.1.1 (.inr s)).isRight := by rw [h]; rfl
    have hG : ((glueIn e C₁ C₂).1.1 (.inr (fvSplit κ e (.inr s)))).isRight := by
      rw [glueIn_right' C₁ C₂ h]; rfl
    rw [QED.TwoLoop.Relabel.psiMomentum₂_of_isRight hf,
      QED.TwoLoop.Relabel.psiMomentum₂_of_isRight hG]
    have h := LineSplit.splitMom_right (lineSplitIn C₁ C₂ ha hc he) k₁ k₂ r (.inl ⟨s, hf⟩)
    rw [lineSplitIn_right_fermion] at h
    exact h

end GlueIn

end QED.GradedProof.X1C

end
