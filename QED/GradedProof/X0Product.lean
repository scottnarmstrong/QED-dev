/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# (X₀): (T₉′) for a product in separated loop momenta

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), steps X0d/X0e. If
`A` satisfies (T₉′) in `L₁` loop momenta and `B` in `L₂`, then `ℓ ↦ A(ℓ₁) B(ℓ₂)`, with
`ℓ₁ = (ℓ₀, …, ℓ_{L₁-1})` and `ℓ₂ = (ℓ_{L₁}, …)`, satisfies (T₉′) in `L₁ + L₂` loop momenta
(`jointEnergyFirstIntegrable_mul`): split the energies and spatial momenta into the two blocks
(`splitE`, measure preserving), and apply Fubini to the product.
-/

@[expose] public section

open MeasureTheory

namespace QED.GradedProof.X0

/-- Splitting a family over `Fin (L₁ + L₂)` into its two blocks, as a measurable equivalence. -/
noncomputable def splitE (X : Type) [MeasurableSpace X] (L₁ L₂ : ℕ) :
    (Fin (L₁ + L₂) → X) ≃ᵐ (Fin L₁ → X) × (Fin L₂ → X) :=
  (MeasurableEquiv.piCongrLeft (fun _ => X) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi fun _ => X)

theorem splitE_apply (X : Type) [MeasurableSpace X] (L₁ L₂ : ℕ) (w : Fin (L₁ + L₂) → X) :
    splitE X L₁ L₂ w = (fun s => w (Fin.castAdd L₂ s), fun s => w (Fin.natAdd L₁ s)) := by
  simp only [splitE, MeasurableEquiv.trans_apply, MeasurableEquiv.coe_sumPiEquivProdPi]
  ext s
  · simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply]
  · simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply]

theorem measurePreserving_splitE (X : Type) [MeasureSpace X]
    [SigmaFinite (volume : Measure X)] (L₁ L₂ : ℕ) :
    MeasurePreserving (splitE X L₁ L₂) volume volume :=
  ((volume_measurePreserving_piCongrLeft (fun _ => X) finSumFinEquiv).symm _).trans
    (volume_measurePreserving_sumPiEquivProdPi _)

/-- **(T₉′) for a product in separated loop momenta.** -/
theorem jointEnergyFirstIntegrable_mul {L₁ L₂ : ℕ} {A : (Fin L₁ → Fin 4 → ℝ) → ℂ}
    {B : (Fin L₂ → Fin 4 → ℝ) → ℂ} (hA : QED.TwoLoop.jointEnergyFirstIntegrable L₁ A)
    (hB : QED.TwoLoop.jointEnergyFirstIntegrable L₂ B) :
    QED.TwoLoop.jointEnergyFirstIntegrable (L₁ + L₂) fun ℓ =>
      A (fun s => ℓ (Fin.castAdd L₂ s)) * B (fun s => ℓ (Fin.natAdd L₁ s)) := by
  have hT := measurePreserving_splitE ℝ L₁ L₂
  have hV := measurePreserving_splitE (Fin 3 → ℝ) L₁ L₂
  set a : (Fin L₁ → Fin 3 → ℝ) → (Fin L₁ → ℝ) → ℂ :=
    fun v t => A fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ) with ha
  set b : (Fin L₂ → Fin 3 → ℝ) → (Fin L₂ → ℝ) → ℂ :=
    fun v t => B fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ) with hb
  have hfun : ∀ v : Fin (L₁ + L₂) → Fin 3 → ℝ, (fun t : Fin (L₁ + L₂) → ℝ =>
      A (fun s => (fun s' => (Fin.cons (t s') (v s') : Fin 4 → ℝ)) (Fin.castAdd L₂ s)) *
        B (fun s => (fun s' => (Fin.cons (t s') (v s') : Fin 4 → ℝ)) (Fin.natAdd L₁ s))) =
      (fun z : (Fin L₁ → ℝ) × (Fin L₂ → ℝ) => a (splitE _ L₁ L₂ v).1 z.1 *
        b (splitE _ L₁ L₂ v).2 z.2) ∘ splitE ℝ L₁ L₂ := fun v => by
    funext t
    simp only [Function.comp_apply, splitE_apply, ha, hb]
  have hint : ∀ v : Fin (L₁ + L₂) → Fin 3 → ℝ, ∫ t : Fin (L₁ + L₂) → ℝ,
      A (fun s => (fun s' => (Fin.cons (t s') (v s') : Fin 4 → ℝ)) (Fin.castAdd L₂ s)) *
        B (fun s => (fun s' => (Fin.cons (t s') (v s') : Fin 4 → ℝ)) (Fin.natAdd L₁ s)) =
      (∫ t, a (splitE _ L₁ L₂ v).1 t) * ∫ t, b (splitE _ L₁ L₂ v).2 t := fun v => by
    rw [hfun v, Function.comp_def, hT.integral_comp' (fun z : (Fin L₁ → ℝ) × (Fin L₂ → ℝ) =>
      a (splitE _ L₁ L₂ v).1 z.1 * b (splitE _ L₁ L₂ v).2 z.2)]
    exact integral_prod_mul (μ := volume) (ν := volume) _ _
  refine ⟨fun v => ?_, ?_⟩
  · rw [hfun v]
    exact (hT.integrable_comp_emb (splitE ℝ L₁ L₂).measurableEmbedding).mpr
      ((hA.1 _).mul_prod (hB.1 _))
  · simp_rw [hint]
    have h := (hV.integrable_comp_emb (splitE (Fin 3 → ℝ) L₁ L₂).measurableEmbedding).mpr
      (hA.2.mul_prod hB.2)
    refine h.congr (Filter.Eventually.of_forall fun v => ?_)
    rfl

end QED.GradedProof.X0

end
