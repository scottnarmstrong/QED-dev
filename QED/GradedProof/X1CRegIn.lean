/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CAmpGlueIn
public import QED.GradedProof.X1CLoopWIn
public import QED.Frozen.Graded.RegulatedAmplitude

/-!
# (X₁) piece C: the regulated amplitude of `glueIn` factorizes

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C3 (value factorization).

`regulatedAmplitude_glueIn`: at the split assignment of `lineSplitIn`, the regulated amplitude
(G₄) of `glueIn e C₁ C₂` is `∑_{γ δ} R₁(βIn = γ) · (1/i) S̃_{γδ}(r) · R₂(αOut = δ)`, with the
regulated amplitudes of the pieces at the gradings `gradL g`, `gradR g` and the bridge propagator
of the open-line mass. The flavourings of `κ` are pairs of flavourings of the pieces
(`sum_joinF`), the glue preserves a flavouring iff the pieces preserve its restrictions, the
regulator weight is multiplicative, and the bridge carries the open-line flavour.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X1C

open QED.WickModel (Params Contraction Line)
open QED.Graded

/-- Functions on `X` are pairs of functions on the summands. -/
theorem sum_joinF {X₁ X₂ X Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq X₁] [DecidableEq X₂] (E : X₁ ⊕ X₂ ≃ X) {M : Type*}
    [AddCommMonoid M] (G : (X → Y) → M) :
    ∑ x, G x = ∑ x₁, ∑ x₂, G (joinF E x₁ x₂) := by
  rw [← ((Equiv.sumArrowEquivProdArrow X₁ X₂ Y).symm.trans
    (Equiv.arrowCongr E (Equiv.refl Y))).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum4_comm {A B : Type*} [Fintype A] [Fintype B] (X : A → Fin 4 → ℂ)
    (Y : B → Fin 4 → ℂ) (Bm : Fin 4 → Fin 4 → ℂ) :
    ∑ γ, ∑ δ, (∑ a, X a γ) * Bm γ δ * (∑ b, Y b δ) =
      ∑ a, ∑ b, ∑ γ, ∑ δ, X a γ * Bm γ δ * Y b δ := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ γ, ∑ a, ∑ δ, ∑ b, X a γ * Bm γ δ * Y b δ :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ γ, ∑ δ, ∑ b, X a γ * Bm γ δ * Y b δ := Finset.sum_comm
    _ = ∑ a, ∑ γ, ∑ b, ∑ δ, X a γ * Bm γ δ * Y b δ :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

variable {N N₁ N₂ nA : ℕ} {F : Type} [Fintype F] [DecidableEq F] {κ : Fin N → Wick.VertexKind}
  {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}

omit [Fintype F] [DecidableEq F] in
theorem flL_joinF (φ₁ : Flavoring F (leftKinds κ e)) (φ₂ : Flavoring F (rightKinds κ e)) :
    flL κ e (joinF (fvSplit κ e) φ₁ φ₂) = φ₁ :=
  funext fun t => joinF_inl _ _ _ t

omit [Fintype F] [DecidableEq F] in
theorem flR_joinF (φ₁ : Flavoring F (leftKinds κ e)) (φ₂ : Flavoring F (rightKinds κ e)) :
    flR κ e (joinF (fvSplit κ e) φ₁ φ₂) = φ₂ :=
  funext fun t => joinF_inr _ _ _ t

omit [Fintype F] [DecidableEq F] in
theorem openLine_of_preserves {M nA' : ℕ} {κ' : Fin M → Wick.VertexKind}
    {C : Contraction 1 nA' κ'} {a : Wick.FermionVertex κ'} (ha : C.1.1 (.inr a) = .inl 0)
    (Φ : Lepton.Flavors F) {φ : Flavoring F κ'} (hφ : Preserves Φ C φ) : φ a = Φ.openLine := by
  have := hφ (.inr a)
  rw [ha] at this
  exact this.symm

variable (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
  (C₁ : Contraction 1 nA (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e))
  {a : Wick.FermionVertex (leftKinds κ e)} {c : Wick.FermionVertex (rightKinds κ e)}
  (ha : C₁.1.1 (.inr a) = .inl 0) (hc : C₂.1.1 (.inl 0) = .inr c) (he : IsShuffle e)

open scoped Classical in
/-- **The regulated amplitude of `glueIn` factorizes** over the bridge indices. -/
theorem regulatedAmplitude_glueIn {x : Wick.FermionVertex (leftKinds κ e)}
    {y : Wick.FermionVertex (rightKinds κ e)} (hx : C₁.1.1 (.inl 0) = .inr x)
    (hy : C₂.1.1 (.inr y) = .inl 0) (g : Grading κ) (pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (k₁ : Line C₁ → Fin 4 → ℝ) (k₂ : Line C₂ → Fin 4 → ℝ)
    (r : Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude P Φ D (glueIn e C₁ C₂) g pIn kIn
        ((lineSplitIn C₁ C₂ ha hc he).splitMom k₁ k₂ r) αOut βIn μ =
      ∑ γ, ∑ δ, regulatedAmplitude P Φ D C₁ (gradL κ e g) ![r] kIn k₁ αOut ![γ] μ *
        ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r γ δ) *
        regulatedAmplitude P Φ D C₂ (gradR κ e g) pIn ![] k₂ ![δ] βIn ![] := by
  unfold regulatedAmplitude
  simp only [Finset.sum_filter]
  rw [sum4_comm, sum_joinF (fvSplit κ e)]
  refine Finset.sum_congr rfl fun φ₁ _ => Finset.sum_congr rfl fun φ₂ _ => ?_
  rw [if_congr (preserves_glueIn_iff C₁ C₂ ha hc Φ _) rfl rfl, flL_joinF, flR_joinF]
  by_cases h₁ : Preserves Φ C₁ φ₁
  · by_cases h₂ : Preserves Φ C₂ φ₂
    · have hp : Preserves Φ (glueIn e C₁ C₂) (joinF (fvSplit κ e) φ₁ φ₂) := by
        rw [preserves_glueIn_iff C₁ C₂ ha hc Φ, flL_joinF, flR_joinF]
        exact ⟨h₁, h₂⟩
      simp only [h₁, h₂, and_self, ite_true]
      rw [loopWeight_glueIn C₁ C₂ ha hc Φ hp, flL_joinF, flR_joinF,
        contractionAmplitude_glueIn P Φ D C₁ C₂ ha hc he hx hy, flL_joinF, flR_joinF,
        openLine_of_preserves ha Φ h₁]
      simp only [Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
      ring
    · simp [h₂]
  · simp [h₁]

end QED.GradedProof.X1C

end
