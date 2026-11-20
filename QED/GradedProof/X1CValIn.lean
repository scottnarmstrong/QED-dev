/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CRegIn
public import QED.GradedProof.X1CRouteIn
public import QED.GradedProof.X1CFactor
public import QED.TwoLoop.ClassLimitVP
public import QED.Frozen.Graded.ContractionValue

/-!
# (X₁) piece C: the value of `glueIn` factorizes

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C3 (value factorization).

`contractionValue_glueIn`: for `r' = r + q`, connected `glueIn e C₁ C₂`, `C₁`, `C₂` with attached
externals, and pieces whose value integrands satisfy (T₉′) at every bridge index, the value (G₅)
of the glue is `∑_{γ δ} V₁(βIn = γ) · (1/i) S̃_{γδ}(r) · V₂(αOut = δ)`, with `V₁` the value of
`C₁` at `(r', r, q)` and `V₂` the value of the self-energy piece `C₂` at `(r, r)`. The routing is
`jointEnergyFirstIntegral_glueIn`, the integrand `regulatedAmplitude_glueIn`, and the separated
integrals `X1C.jointEnergyFirstIntegral_sum_mul`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X1C

open QED.WickModel (Params Contraction Line loopCount lineMomentum₂ VerticesConnected
  ExternalsAttached)
open QED.Graded
open QED.TwoLoop.ClassLimit (jointEnergyFirstIntegral_const_mul
  jointEnergyFirstIntegrable_const_mul)

/-- The normalization `(2π)^{-4L}` of (G₅). -/
noncomputable abbrev twoPiInv (L : ℕ) : ℂ := (((2 * Real.pi) ^ (4 * L) : ℝ) : ℂ)⁻¹

theorem twoPiInv_add (L₁ L₂ : ℕ) : twoPiInv (L₁ + L₂) = twoPiInv L₁ * twoPiInv L₂ := by
  simp only [twoPiInv, mul_add, pow_add]
  push_cast
  rw [mul_inv]

variable {N N₁ N₂ : ℕ} {F : Type} [Fintype F] [DecidableEq F] {κ : Fin N → Wick.VertexKind}
  {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}
  (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
  (C₁ : Contraction 1 1 (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e))
  {a : Wick.FermionVertex (leftKinds κ e)} {c : Wick.FermionVertex (rightKinds κ e)}
  (ha : C₁.1.1 (.inr a) = .inl 0) (hc : C₂.1.1 (.inl 0) = .inr c) (he : IsShuffle e)

include ha hc he in
/-- **The value of `glueIn` factorizes** over the bridge indices. -/
theorem contractionValue_glueIn {x : Wick.FermionVertex (leftKinds κ e)}
    {y : Wick.FermionVertex (rightKinds κ e)} (hx : C₁.1.1 (.inl 0) = .inr x)
    (hy : C₂.1.1 (.inr y) = .inl 0) (hV : VerticesConnected (glueIn e C₁ C₂))
    (hV₁ : VerticesConnected C₁) (hV₂ : VerticesConnected C₂) (hA₁ : ExternalsAttached C₁)
    (hA₂ : ExternalsAttached C₂) {r' r q : Fin 4 → ℝ} (hmom : r' = r + q) (g : Grading κ)
    (αOut βIn μ : Fin 1 → Fin 4)
    (hT₁ : ∀ γ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₁) fun ℓ =>
      twoPiInv (loopCount C₁) * regulatedAmplitude P Φ D C₁ (gradL κ e g) ![r] ![q]
        (lineMomentum₂ C₁ ![r'] ![r] ![q] ℓ) αOut ![γ] μ)
    (hT₂ : ∀ δ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₂) fun ℓ =>
      twoPiInv (loopCount C₂) * regulatedAmplitude P Φ D C₂ (gradR κ e g) ![r] ![]
        (lineMomentum₂ C₂ ![r] ![r] ![] ℓ) ![δ] βIn ![]) :
    contractionValue P Φ D (glueIn e C₁ C₂) g ![r'] ![r] ![q] αOut βIn μ =
      ∑ γ, ∑ δ, contractionValue P Φ D C₁ (gradL κ e g) ![r'] ![r] ![q] αOut ![γ] μ *
        ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r γ δ) *
        contractionValue P Φ D C₂ (gradR κ e g) ![r] ![r] ![] ![δ] βIn ![] := by
  set Bm : Fin 4 → Fin 4 → ℂ := fun γ δ =>
    (1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r γ δ with hBm
  set A : Fin 4 × Fin 4 → (Fin (loopCount C₁) → Fin 4 → ℝ) → ℂ := fun z ℓ =>
    Bm z.1 z.2 * (twoPiInv (loopCount C₁) * regulatedAmplitude P Φ D C₁ (gradL κ e g) ![r] ![q]
      (lineMomentum₂ C₁ ![r'] ![r] ![q] ℓ) αOut ![z.1] μ) with hA
  set B : Fin 4 × Fin 4 → (Fin (loopCount C₂) → Fin 4 → ℝ) → ℂ := fun z ℓ =>
    twoPiInv (loopCount C₂) * regulatedAmplitude P Φ D C₂ (gradR κ e g) ![r] ![]
      (lineMomentum₂ C₂ ![r] ![r] ![] ℓ) ![z.2] βIn ![] with hB
  have hL := (lineSplitIn C₁ C₂ ha hc he).loopCount_split hV hV₁ hV₂ (Fin.pos a.1) (Fin.pos c.1)
  have key := jointEnergyFirstIntegral_glueIn C₁ C₂ ha hx hc he hV hV₁ hV₂ hA₁ hA₂ hmom
    (fun k => twoPiInv (loopCount C₁ + loopCount C₂) *
      regulatedAmplitude P Φ D (glueIn e C₁ C₂) g ![r] ![q] k αOut βIn μ)
  have hpt : ∀ ℓ : Fin (loopCount C₁ + loopCount C₂) → Fin 4 → ℝ,
      twoPiInv (loopCount C₁ + loopCount C₂) * regulatedAmplitude P Φ D (glueIn e C₁ C₂) g ![r]
        ![q] ((lineSplitIn C₁ C₂ ha hc he).splitMom
          (lineMomentum₂ C₁ ![r'] ![r] ![q] fun s => ℓ (Fin.castAdd _ s))
          (lineMomentum₂ C₂ ![r] ![r] ![] fun s => ℓ (Fin.natAdd _ s)) r) αOut βIn μ =
      ∑ z ∈ Finset.univ, A z (fun s => ℓ (Fin.castAdd _ s)) * B z (fun s => ℓ (Fin.natAdd _ s)) :=
    fun ℓ => by
      rw [regulatedAmplitude_glueIn P Φ D C₁ C₂ ha hc he hx hy, twoPiInv_add,
        Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun δ _ => ?_
      simp only [hA, hB, hBm]
      ring
  unfold contractionValue
  rw [hL]
  change QED.TwoLoop.jointEnergyFirstIntegral _ (fun ℓ => twoPiInv (loopCount C₁ + loopCount C₂) *
    regulatedAmplitude P Φ D (glueIn e C₁ C₂) g ![r] ![q]
      (lineMomentum₂ (glueIn e C₁ C₂) ![r'] ![r] ![q] ℓ) αOut βIn μ) = _
  rw [key, funext hpt, jointEnergyFirstIntegral_sum_mul Finset.univ A B
    (fun z _ => jointEnergyFirstIntegrable_const_mul _ (hT₁ z.1)) (fun z _ => hT₂ z.2),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
  simp only [hA, hB]
  rw [jointEnergyFirstIntegral_const_mul]
  ring

end QED.GradedProof.X1C

end
