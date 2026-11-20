/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CAmpP
public import QED.GradedProof.X1CLoopP
public import QED.GradedProof.X1CValIn

/-!
# (X₁) piece C: the regulated amplitude and the value of `glueP` factorize

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C3.

* `regulatedAmplitude_glueP`: (G₄) of `glueP e C₁ C₂` at the split assignment of `lineSplitP` is
  `∑_{ν ρ} R₁(μ = ν) · (1/i) D̃_{νρ}(q) · R₂(μ = (μ₀, ρ))`.
* `contractionValue_glueP`: the value (G₅) of `glueP e C₁ C₂` at `(r', r, q)`, `r' = r + q`, is
  `∑_{ν ρ} V₁(μ = ν) · (1/i) D̃_{νρ}(q) · V₂(μ = (μ₀, ρ))`, with `V₁` the value of `C₁` at
  `(r', r, q)` and `V₂` that of the vacuum polarization piece at `(q, -q)`, given (T₉′) of the
  piece integrands at every bridge index. The bridge line is found by `exists_bridgeP`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X1C

open QED.WickModel (Params Contraction Line PhotonLine loopCount lineMomentum₂
  VerticesConnected ExternalsAttached)
open QED.Graded
open QED.TwoLoop.ClassLimit (jointEnergyFirstIntegral_const_mul
  jointEnergyFirstIntegrable_const_mul)

variable {N N₁ N₂ : ℕ} {F : Type} [Fintype F] [DecidableEq F] {κ : Fin N → Wick.VertexKind}
  {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N} (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
  (C₁ : Contraction 1 1 (leftKinds κ e)) (C₂ : Contraction 0 2 (rightKinds κ e))
  {w₁ w₂ : Wick.PhotonSlot (rightKinds κ e)} (hw₁ : C₂.1.2 (.inl 0) = .inr w₁)
  (hw : C₂.1.2 (.inl 1) = .inr w₂) (he : IsShuffle e)

open scoped Classical in
include hw₁ in
/-- **The regulated amplitude of `glueP` factorizes** over the bridge indices. -/
theorem regulatedAmplitude_glueP {b : PhotonLine (glueP e C₁ C₂)}
    (hb : b.1 = psSplit κ e (.inl (extSlot C₁)) ∨ b.1 = psSplit κ e (.inr w₂))
    (k₁ : Line C₁ → Fin 4 → ℝ) (k₂ : Line C₂ → Fin 4 → ℝ) {q Pm : Fin 4 → ℝ}
    (hP : (b.1 = psSplit κ e (.inl (extSlot C₁)) ∧ Pm = -q) ∨
      (b.1 = psSplit κ e (.inr w₂) ∧ Pm = q))
    {x y : Wick.FermionVertex (leftKinds κ e)} (hx : C₁.1.1 (.inl 0) = .inr x)
    (hy : C₁.1.1 (.inr y) = .inl 0) (g : Grading κ) (pIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    regulatedAmplitude P Φ D (glueP e C₁ C₂) g pIn ![q]
        ((lineSplitP C₁ C₂ hw he hb).splitMom k₁ k₂ Pm) αOut βIn μ =
      ∑ ν, ∑ ρ, regulatedAmplitude P Φ D C₁ (gradL κ e g) pIn ![q] k₁ αOut βIn ![ν] *
        ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε q ν ρ) *
        regulatedAmplitude P Φ D C₂ (gradR κ e g) ![] ![q, -q] k₂ ![] ![] ![μ 0, ρ] := by
  unfold regulatedAmplitude
  simp only [Finset.sum_filter]
  rw [sum4_comm, sum_joinF (fvSplit κ e)]
  refine Finset.sum_congr rfl fun φ₁ _ => Finset.sum_congr rfl fun φ₂ _ => ?_
  rw [if_congr (preserves_glueP_iff C₁ C₂ Φ _) rfl rfl, flL_joinF, flR_joinF]
  by_cases h₁ : Preserves Φ C₁ φ₁
  · by_cases h₂ : Preserves Φ C₂ φ₂
    · have hp : Preserves Φ (glueP e C₁ C₂) (joinF (fvSplit κ e) φ₁ φ₂) := by
        rw [preserves_glueP_iff C₁ C₂ Φ, flL_joinF, flR_joinF]
        exact ⟨h₁, h₂⟩
      simp only [h₁, h₂, and_self, ite_true]
      rw [loopWeight_glueP C₁ C₂ Φ hp, flL_joinF, flR_joinF,
        contractionAmplitude_glueP P Φ D C₁ C₂ hw₁ hw he hb k₁ k₂ hP hx hy, flL_joinF,
        flR_joinF]
      simp only [Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
      ring
    · simp [h₂]
  · simp [h₁]

include hw₁ hw he in
theorem contractionValue_glueP_aux {b : PhotonLine (glueP e C₁ C₂)}
    (hb : b.1 = psSplit κ e (.inl (extSlot C₁)) ∨ b.1 = psSplit κ e (.inr w₂))
    {r' r q Pm : Fin 4 → ℝ}
    (hP : (b.1 = psSplit κ e (.inl (extSlot C₁)) ∧ Pm = -q) ∨
      (b.1 = psSplit κ e (.inr w₂) ∧ Pm = q))
    {x y : Wick.FermionVertex (leftKinds κ e)} (hx : C₁.1.1 (.inl 0) = .inr x)
    (hy : C₁.1.1 (.inr y) = .inl 0) (hV : VerticesConnected (glueP e C₁ C₂))
    (hV₁ : VerticesConnected C₁) (hV₂ : VerticesConnected C₂) (hA₁ : ExternalsAttached C₁)
    (hA₂ : ExternalsAttached C₂) (hmom : r' = r + q) (g : Grading κ)
    (αOut βIn μ : Fin 1 → Fin 4)
    (hT₁ : ∀ ν, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₁) fun ℓ =>
      twoPiInv (loopCount C₁) * regulatedAmplitude P Φ D C₁ (gradL κ e g) ![r] ![q]
        (lineMomentum₂ C₁ ![r'] ![r] ![q] ℓ) αOut βIn ![ν])
    (hT₂ : ∀ ρ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₂) fun ℓ =>
      twoPiInv (loopCount C₂) * regulatedAmplitude P Φ D C₂ (gradR κ e g) ![] ![q, -q]
        (lineMomentum₂ C₂ ![] ![] ![q, -q] ℓ) ![] ![] ![μ 0, ρ]) :
    contractionValue P Φ D (glueP e C₁ C₂) g ![r'] ![r] ![q] αOut βIn μ =
      ∑ ν, ∑ ρ, contractionValue P Φ D C₁ (gradL κ e g) ![r'] ![r] ![q] αOut βIn ![ν] *
        ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε q ν ρ) *
        contractionValue P Φ D C₂ (gradR κ e g) ![] ![] ![q, -q] ![] ![] ![μ 0, ρ] := by
  set Bm : Fin 4 → Fin 4 → ℂ := fun ν ρ =>
    (1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε q ν ρ with hBm
  set A : Fin 4 × Fin 4 → (Fin (loopCount C₁) → Fin 4 → ℝ) → ℂ := fun z ℓ =>
    Bm z.1 z.2 * (twoPiInv (loopCount C₁) * regulatedAmplitude P Φ D C₁ (gradL κ e g) ![r] ![q]
      (lineMomentum₂ C₁ ![r'] ![r] ![q] ℓ) αOut βIn ![z.1]) with hA
  set B : Fin 4 × Fin 4 → (Fin (loopCount C₂) → Fin 4 → ℝ) → ℂ := fun z ℓ =>
    twoPiInv (loopCount C₂) * regulatedAmplitude P Φ D C₂ (gradR κ e g) ![] ![q, -q]
      (lineMomentum₂ C₂ ![] ![] ![q, -q] ℓ) ![] ![] ![μ 0, z.2] with hB
  have hL := (lineSplitP C₁ C₂ hw he hb).loopCount_split hV hV₁ hV₂ (Fin.pos (extSlot C₁).1)
    (Fin.pos w₂.1)
  have key := jointEnergyFirstIntegral_glueP C₁ C₂ hw₁ hw he hV hV₁ hV₂ hA₁ hA₂ hmom hb hP
    (fun k => twoPiInv (loopCount C₁ + loopCount C₂) *
      regulatedAmplitude P Φ D (glueP e C₁ C₂) g ![r] ![q] k αOut βIn μ)
  have hpt : ∀ ℓ : Fin (loopCount C₁ + loopCount C₂) → Fin 4 → ℝ,
      twoPiInv (loopCount C₁ + loopCount C₂) * regulatedAmplitude P Φ D (glueP e C₁ C₂) g ![r]
        ![q] ((lineSplitP C₁ C₂ hw he hb).splitMom
          (lineMomentum₂ C₁ ![r'] ![r] ![q] fun s => ℓ (Fin.castAdd _ s))
          (lineMomentum₂ C₂ ![] ![] ![q, -q] fun s => ℓ (Fin.natAdd _ s)) Pm) αOut βIn μ =
      ∑ z ∈ Finset.univ, A z (fun s => ℓ (Fin.castAdd _ s)) * B z (fun s => ℓ (Fin.natAdd _ s)) :=
    fun ℓ => by
      rw [regulatedAmplitude_glueP P Φ D C₁ C₂ hw₁ hw he hb _ _ hP hx hy, twoPiInv_add,
        Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun δ _ => ?_
      simp only [hA, hB, hBm]
      ring
  unfold contractionValue
  rw [hL]
  change QED.TwoLoop.jointEnergyFirstIntegral _ (fun ℓ => twoPiInv (loopCount C₁ + loopCount C₂) *
    regulatedAmplitude P Φ D (glueP e C₁ C₂) g ![r] ![q]
      (lineMomentum₂ (glueP e C₁ C₂) ![r'] ![r] ![q] ℓ) αOut βIn μ) = _
  rw [key, funext hpt, jointEnergyFirstIntegral_sum_mul Finset.univ A B
    (fun z _ => jointEnergyFirstIntegrable_const_mul _ (hT₁ z.1)) (fun z _ => hT₂ z.2),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
  simp only [hA, hB]
  rw [jointEnergyFirstIntegral_const_mul]
  ring

include hw₁ hw he in
/-- **The value of `glueP` factorizes** over the bridge indices. -/
theorem contractionValue_glueP {r' r q : Fin 4 → ℝ} {x y : Wick.FermionVertex (leftKinds κ e)}
    (hx : C₁.1.1 (.inl 0) = .inr x) (hy : C₁.1.1 (.inr y) = .inl 0)
    (hV : VerticesConnected (glueP e C₁ C₂)) (hV₁ : VerticesConnected C₁)
    (hV₂ : VerticesConnected C₂) (hA₁ : ExternalsAttached C₁) (hA₂ : ExternalsAttached C₂)
    (hmom : r' = r + q) (g : Grading κ) (αOut βIn μ : Fin 1 → Fin 4)
    (hT₁ : ∀ ν, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₁) fun ℓ =>
      twoPiInv (loopCount C₁) * regulatedAmplitude P Φ D C₁ (gradL κ e g) ![r] ![q]
        (lineMomentum₂ C₁ ![r'] ![r] ![q] ℓ) αOut βIn ![ν])
    (hT₂ : ∀ ρ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₂) fun ℓ =>
      twoPiInv (loopCount C₂) * regulatedAmplitude P Φ D C₂ (gradR κ e g) ![] ![q, -q]
        (lineMomentum₂ C₂ ![] ![] ![q, -q] ℓ) ![] ![] ![μ 0, ρ]) :
    contractionValue P Φ D (glueP e C₁ C₂) g ![r'] ![r] ![q] αOut βIn μ =
      ∑ ν, ∑ ρ, contractionValue P Φ D C₁ (gradL κ e g) ![r'] ![r] ![q] αOut βIn ![ν] *
        ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε q ν ρ) *
        contractionValue P Φ D C₂ (gradR κ e g) ![] ![] ![q, -q] ![] ![] ![μ 0, ρ] := by
  obtain ⟨b, hb⟩ := exists_bridgeP C₁ C₂ hw
  rcases hb with hb' | hb'
  · exact contractionValue_glueP_aux P Φ D C₁ C₂ hw₁ hw he (b := b) (.inl hb') (Pm := -q)
      (.inl ⟨hb', rfl⟩) hx hy hV hV₁ hV₂ hA₁ hA₂ hmom g αOut βIn μ hT₁ hT₂
  · exact contractionValue_glueP_aux P Φ D C₁ C₂ hw₁ hw he (b := b) (.inr hb') (Pm := q)
      (.inr ⟨hb', rfl⟩) hx hy hV hV₁ hV₂ hA₁ hA₂ hmom g αOut βIn μ hT₁ hT₂

end QED.GradedProof.X1C

end
