/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CAmpGlueOut
public import QED.GradedProof.X1CLoopOut
public import QED.GradedProof.X1CValIn
public import QED.GradedProof.X1CRouteOut

/-!
# (X₁) piece C: the regulated amplitude and the value of `glueOut` factorize

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C3; the mirror of `X1CRegIn`, `X1CValIn`.

* `regulatedAmplitude_glueOut`: (G₄) of `glueOut e C₁ C₂` at the split assignment of
  `lineSplitOut` is `∑_{γ δ} R₂(βIn = γ) · (1/i) S̃_{γδ}(r') · R₁(αOut = δ)`.
* `contractionValue_glueOut`: the value (G₅) of `glueOut e C₁ C₂` at `(r', r, q)`, `r' = r + q`,
  is `∑_{γ δ} V₂(βIn = γ) · (1/i) S̃_{γδ}(r') · V₁(αOut = δ)`, with `V₂` the value of the
  self-energy piece at `(r', r')` and `V₁` that of `C₁` at `(r', r, q)`, given (T₉′) of the
  piece integrands at every bridge index.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X1C

open QED.WickModel (Params Contraction Line loopCount lineMomentum₂ VerticesConnected
  ExternalsAttached)
open QED.Graded
open QED.TwoLoop.ClassLimit (jointEnergyFirstIntegral_const_mul
  jointEnergyFirstIntegrable_const_mul)

variable {N N₁ N₂ nA : ℕ} {F : Type} [Fintype F] [DecidableEq F] {κ : Fin N → Wick.VertexKind}
  {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N} (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)

section Reg

variable (C₁ : Contraction 1 nA (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e))
  {a : Wick.FermionVertex (leftKinds κ e)} {c : Wick.FermionVertex (rightKinds κ e)}
  (ha : C₁.1.1 (.inl 0) = .inr a) (hc : C₂.1.1 (.inr c) = .inl 0) (he : IsShuffle e)

open scoped Classical in
/-- **The regulated amplitude of `glueOut` factorizes** over the bridge indices. -/
theorem regulatedAmplitude_glueOut {x : Wick.FermionVertex (rightKinds κ e)}
    {y : Wick.FermionVertex (leftKinds κ e)} (hx : C₂.1.1 (.inl 0) = .inr x)
    (hy : C₁.1.1 (.inr y) = .inl 0) (g : Grading κ) (pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (k₁ : Line C₁ → Fin 4 → ℝ) (k₂ : Line C₂ → Fin 4 → ℝ)
    (r' : Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude P Φ D (glueOut e C₁ C₂) g pIn kIn
        ((lineSplitOut C₁ C₂ ha hc he).splitMom k₁ k₂ r') αOut βIn μ =
      ∑ γ, ∑ δ, regulatedAmplitude P Φ D C₂ (gradR κ e g) ![r'] ![] k₂ αOut ![γ] ![] *
        ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r' γ δ) *
        regulatedAmplitude P Φ D C₁ (gradL κ e g) pIn kIn k₁ ![δ] βIn μ := by
  unfold regulatedAmplitude
  simp only [Finset.sum_filter]
  rw [sum4_comm, sum_joinF (fvSplit κ e), Finset.sum_comm]
  refine Finset.sum_congr rfl fun φ₂ _ => Finset.sum_congr rfl fun φ₁ _ => ?_
  rw [if_congr (preserves_glueOut_iff C₁ C₂ ha hc Φ _) rfl rfl, flL_joinF, flR_joinF]
  by_cases h₁ : Preserves Φ C₁ φ₁
  · by_cases h₂ : Preserves Φ C₂ φ₂
    · have hp : Preserves Φ (glueOut e C₁ C₂) (joinF (fvSplit κ e) φ₁ φ₂) := by
        rw [preserves_glueOut_iff C₁ C₂ ha hc Φ, flL_joinF, flR_joinF]
        exact ⟨h₁, h₂⟩
      simp only [h₁, h₂, and_self, ite_true]
      rw [loopWeight_glueOut C₁ C₂ ha hc Φ hp, flL_joinF, flR_joinF,
        contractionAmplitude_glueOut P Φ D C₁ C₂ ha hc he k₁ k₂ r' hx hy, flL_joinF, flR_joinF,
        openLine_of_preserves hc Φ h₂]
      simp only [Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
      ring
    · simp [h₂]
  · simp [h₁]

end Reg

variable (C₁ : Contraction 1 1 (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e))
  {a : Wick.FermionVertex (leftKinds κ e)} {c : Wick.FermionVertex (rightKinds κ e)}
  (ha : C₁.1.1 (.inl 0) = .inr a) (hc : C₂.1.1 (.inr c) = .inl 0) (he : IsShuffle e)

include ha hc he in
/-- **The value of `glueOut` factorizes** over the bridge indices. -/
theorem contractionValue_glueOut {x : Wick.FermionVertex (rightKinds κ e)}
    {y : Wick.FermionVertex (leftKinds κ e)} (hx : C₂.1.1 (.inl 0) = .inr x)
    (hy : C₁.1.1 (.inr y) = .inl 0) (hV : VerticesConnected (glueOut e C₁ C₂))
    (hV₁ : VerticesConnected C₁) (hV₂ : VerticesConnected C₂) (hA₁ : ExternalsAttached C₁)
    (hA₂ : ExternalsAttached C₂) {r' r q : Fin 4 → ℝ} (hmom : r' = r + q) (g : Grading κ)
    (αOut βIn μ : Fin 1 → Fin 4)
    (hT₁ : ∀ δ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₁) fun ℓ =>
      twoPiInv (loopCount C₁) * regulatedAmplitude P Φ D C₁ (gradL κ e g) ![r] ![q]
        (lineMomentum₂ C₁ ![r'] ![r] ![q] ℓ) ![δ] βIn μ)
    (hT₂ : ∀ γ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₂) fun ℓ =>
      twoPiInv (loopCount C₂) * regulatedAmplitude P Φ D C₂ (gradR κ e g) ![r'] ![]
        (lineMomentum₂ C₂ ![r'] ![r'] ![] ℓ) αOut ![γ] ![]) :
    contractionValue P Φ D (glueOut e C₁ C₂) g ![r'] ![r] ![q] αOut βIn μ =
      ∑ γ, ∑ δ, contractionValue P Φ D C₂ (gradR κ e g) ![r'] ![r'] ![] αOut ![γ] ![] *
        ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r' γ δ) *
        contractionValue P Φ D C₁ (gradL κ e g) ![r'] ![r] ![q] ![δ] βIn μ := by
  set Bm : Fin 4 → Fin 4 → ℂ := fun γ δ =>
    (1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r' γ δ with hBm
  set A : Fin 4 × Fin 4 → (Fin (loopCount C₁) → Fin 4 → ℝ) → ℂ := fun z ℓ =>
    twoPiInv (loopCount C₁) * regulatedAmplitude P Φ D C₁ (gradL κ e g) ![r] ![q]
      (lineMomentum₂ C₁ ![r'] ![r] ![q] ℓ) ![z.2] βIn μ with hA
  set B : Fin 4 × Fin 4 → (Fin (loopCount C₂) → Fin 4 → ℝ) → ℂ := fun z ℓ =>
    Bm z.1 z.2 * (twoPiInv (loopCount C₂) * regulatedAmplitude P Φ D C₂ (gradR κ e g) ![r'] ![]
      (lineMomentum₂ C₂ ![r'] ![r'] ![] ℓ) αOut ![z.1] ![]) with hB
  have hL := (lineSplitOut C₁ C₂ ha hc he).loopCount_split hV hV₁ hV₂ (Fin.pos a.1) (Fin.pos c.1)
  have key := jointEnergyFirstIntegral_glueOut C₁ C₂ ha hc hx he hV hV₁ hV₂ hA₁ hA₂ hmom
    (fun k => twoPiInv (loopCount C₁ + loopCount C₂) *
      regulatedAmplitude P Φ D (glueOut e C₁ C₂) g ![r] ![q] k αOut βIn μ)
  have hpt : ∀ ℓ : Fin (loopCount C₁ + loopCount C₂) → Fin 4 → ℝ,
      twoPiInv (loopCount C₁ + loopCount C₂) * regulatedAmplitude P Φ D (glueOut e C₁ C₂) g ![r]
        ![q] ((lineSplitOut C₁ C₂ ha hc he).splitMom
          (lineMomentum₂ C₁ ![r'] ![r] ![q] fun s => ℓ (Fin.castAdd _ s))
          (lineMomentum₂ C₂ ![r'] ![r'] ![] fun s => ℓ (Fin.natAdd _ s)) r') αOut βIn μ =
      ∑ z ∈ Finset.univ, A z (fun s => ℓ (Fin.castAdd _ s)) * B z (fun s => ℓ (Fin.natAdd _ s)) :=
    fun ℓ => by
      rw [regulatedAmplitude_glueOut P Φ D C₁ C₂ ha hc he hx hy, twoPiInv_add,
        Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun δ _ => ?_
      simp only [hA, hB, hBm]
      ring
  unfold contractionValue
  rw [hL]
  change QED.TwoLoop.jointEnergyFirstIntegral _ (fun ℓ => twoPiInv (loopCount C₁ + loopCount C₂) *
    regulatedAmplitude P Φ D (glueOut e C₁ C₂) g ![r] ![q]
      (lineMomentum₂ (glueOut e C₁ C₂) ![r'] ![r] ![q] ℓ) αOut βIn μ) = _
  rw [key, funext hpt, jointEnergyFirstIntegral_sum_mul Finset.univ A B
    (fun z _ => hT₁ z.2) (fun z _ => jointEnergyFirstIntegrable_const_mul _ (hT₂ z.1)),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
  rw [hB]
  dsimp only
  rw [jointEnergyFirstIntegral_const_mul (Bm γ δ)]
  ring

end QED.GradedProof.X1C

end
