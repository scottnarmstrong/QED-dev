/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0Product
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegral
public import QED.TwoLoop.JointIntegralInvariance

/-!
# (X₁) piece C: the value of a product in separated loop momenta

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C. A one-particle-reducible contraction (a leg or photon-leg correction)
has an integrand that, after a unimodular change of loop momenta, is a sum over the indices of the
joining line of products `A(ℓ₁) B(ℓ₂)` in separated blocks of loop momenta. The joint
energy-first integral (T₉) of such a product is the product of the integrals
(`jointEnergyFirstIntegral_mul`), with no integrability assumption: both stages are Fubini for a
product of functions of separate variables (`MeasureTheory.integral_prod_mul`), which holds
unconditionally. Integrability (T₉′) of the factors is needed only to move the sum over the
joining indices out of the integral.

## Main statements

* `QED.GradedProof.X1C.jointEnergyFirstIntegral_mul`.
* `QED.GradedProof.X1C.jointEnergyFirstIntegral_sum_mul`: with (T₉′) for the factors, the sum
  over the joining indices moves out: `∑ᵢ Aᵢ(ℓ₁) Bᵢ(ℓ₂)` has value `∑ᵢ (T₉)(Aᵢ) (T₉)(Bᵢ)`.
* `QED.GradedProof.X1C.jointEnergyFirstIntegral_eq_zero_of_odd`: the value of an odd integrand
  is `0` (the tadpoles), again with no integrability assumption.
* `QED.GradedProof.X1C.jointEnergyFirstIntegral_mul_eq_zero_of_odd`: a product in separated loop
  momenta with an odd factor has value `0`.
-/

@[expose] public section

open MeasureTheory

namespace QED.GradedProof.X1C

open QED.GradedProof.X0 (splitE splitE_apply measurePreserving_splitE)

/-- **The joint energy-first integral of a product in separated loop momenta** is the product of
the joint energy-first integrals, for all `A`, `B` (no integrability needed). -/
theorem jointEnergyFirstIntegral_mul {L₁ L₂ : ℕ} (A : (Fin L₁ → Fin 4 → ℝ) → ℂ)
    (B : (Fin L₂ → Fin 4 → ℝ) → ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegral (L₁ + L₂) (fun ℓ =>
      A (fun s => ℓ (Fin.castAdd L₂ s)) * B (fun s => ℓ (Fin.natAdd L₁ s))) =
      QED.TwoLoop.jointEnergyFirstIntegral L₁ A * QED.TwoLoop.jointEnergyFirstIntegral L₂ B := by
  have hT := measurePreserving_splitE ℝ L₁ L₂
  have hV := measurePreserving_splitE (Fin 3 → ℝ) L₁ L₂
  set a : (Fin L₁ → Fin 3 → ℝ) → (Fin L₁ → ℝ) → ℂ :=
    fun v t => A fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ) with ha
  set b : (Fin L₂ → Fin 3 → ℝ) → (Fin L₂ → ℝ) → ℂ :=
    fun v t => B fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ) with hb
  have hint : ∀ v : Fin (L₁ + L₂) → Fin 3 → ℝ, ∫ t : Fin (L₁ + L₂) → ℝ,
      A (fun s => (fun s' => (Fin.cons (t s') (v s') : Fin 4 → ℝ)) (Fin.castAdd L₂ s)) *
        B (fun s => (fun s' => (Fin.cons (t s') (v s') : Fin 4 → ℝ)) (Fin.natAdd L₁ s)) =
      (∫ t, a (splitE _ L₁ L₂ v).1 t) * ∫ t, b (splitE _ L₁ L₂ v).2 t := fun v => by
    have hfun : (fun t : Fin (L₁ + L₂) → ℝ =>
        A (fun s => (fun s' => (Fin.cons (t s') (v s') : Fin 4 → ℝ)) (Fin.castAdd L₂ s)) *
          B (fun s => (fun s' => (Fin.cons (t s') (v s') : Fin 4 → ℝ)) (Fin.natAdd L₁ s))) =
        (fun z : (Fin L₁ → ℝ) × (Fin L₂ → ℝ) => a (splitE _ L₁ L₂ v).1 z.1 *
          b (splitE _ L₁ L₂ v).2 z.2) ∘ splitE ℝ L₁ L₂ := by
      funext t
      simp only [Function.comp_apply, splitE_apply, ha, hb]
    rw [hfun, Function.comp_def, hT.integral_comp' (fun z : (Fin L₁ → ℝ) × (Fin L₂ → ℝ) =>
      a (splitE _ L₁ L₂ v).1 z.1 * b (splitE _ L₁ L₂ v).2 z.2)]
    exact integral_prod_mul (μ := volume) (ν := volume) _ _
  unfold QED.TwoLoop.jointEnergyFirstIntegral
  simp_rw [hint]
  have hout := hV.integral_comp' (fun z : (Fin L₁ → Fin 3 → ℝ) × (Fin L₂ → Fin 3 → ℝ) =>
    (∫ t, a z.1 t) * ∫ t, b z.2 t)
  refine hout.trans ?_
  exact integral_prod_mul (μ := volume) (ν := volume) (fun w => ∫ t, a w t)
    (fun w => ∫ t, b w t)

/-- The joint energy-first integral of a finite sum of integrands satisfying (T₉′). -/
theorem jointEnergyFirstIntegral_finsetSum {ι : Type*} (s : Finset ι) {L : ℕ}
    (G : ι → (Fin L → Fin 4 → ℝ) → ℂ)
    (h : ∀ i ∈ s, QED.TwoLoop.jointEnergyFirstIntegrable L (G i)) :
    QED.TwoLoop.jointEnergyFirstIntegral L (fun ℓ => ∑ i ∈ s, G i ℓ) =
      ∑ i ∈ s, QED.TwoLoop.jointEnergyFirstIntegral L (G i) := by
  unfold QED.TwoLoop.jointEnergyFirstIntegral
  have hin : ∀ v : Fin L → Fin 3 → ℝ, ∫ t : Fin L → ℝ,
      ∑ i ∈ s, G i (fun s' => (Fin.cons (t s') (v s') : Fin 4 → ℝ)) =
      ∑ i ∈ s, ∫ t : Fin L → ℝ, G i (fun s' => (Fin.cons (t s') (v s') : Fin 4 → ℝ)) :=
    fun v => integral_finsetSum s fun i hi => (h i hi).1 v
  simp only [hin]
  exact integral_finsetSum s fun i hi => (h i hi).2

/-- **The sum over the joining indices of products in separated loop momenta**: if every factor
satisfies (T₉′), the value of `∑ᵢ Aᵢ(ℓ₁) Bᵢ(ℓ₂)` is `∑ᵢ (T₉)(Aᵢ) · (T₉)(Bᵢ)`. -/
theorem jointEnergyFirstIntegral_sum_mul {ι : Type*} (s : Finset ι) {L₁ L₂ : ℕ}
    (A : ι → (Fin L₁ → Fin 4 → ℝ) → ℂ) (B : ι → (Fin L₂ → Fin 4 → ℝ) → ℂ)
    (hA : ∀ i ∈ s, QED.TwoLoop.jointEnergyFirstIntegrable L₁ (A i))
    (hB : ∀ i ∈ s, QED.TwoLoop.jointEnergyFirstIntegrable L₂ (B i)) :
    QED.TwoLoop.jointEnergyFirstIntegral (L₁ + L₂) (fun ℓ => ∑ i ∈ s,
      A i (fun s' => ℓ (Fin.castAdd L₂ s')) * B i (fun s' => ℓ (Fin.natAdd L₁ s'))) =
      ∑ i ∈ s, QED.TwoLoop.jointEnergyFirstIntegral L₁ (A i) *
        QED.TwoLoop.jointEnergyFirstIntegral L₂ (B i) := by
  rw [jointEnergyFirstIntegral_finsetSum s _ fun i hi =>
    QED.GradedProof.X0.jointEnergyFirstIntegrable_mul (hA i hi) (hB i hi)]
  exact Finset.sum_congr rfl fun i _ => jointEnergyFirstIntegral_mul (A i) (B i)

/-- **The value of an odd integrand is `0`**, for every integrand (the reflection `ℓ ↦ -ℓ`
preserves (T₉), `QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_neg`). -/
theorem jointEnergyFirstIntegral_eq_zero_of_odd {L : ℕ} (F : (Fin L → Fin 4 → ℝ) → ℂ)
    (hF : ∀ ℓ, F (-ℓ) = -F ℓ) : QED.TwoLoop.jointEnergyFirstIntegral L F = 0 := by
  have h := QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_neg L F
  simp only [hF] at h
  unfold QED.TwoLoop.jointEnergyFirstIntegral at h
  simp only [integral_neg] at h
  unfold QED.TwoLoop.jointEnergyFirstIntegral
  exact CharZero.eq_neg_self_iff.1 h.symm

/-- **A product in separated loop momenta with an odd first factor has value `0`** (a tadpole
side `A` of zero momentum inflow, odd in its own loop momenta). -/
theorem jointEnergyFirstIntegral_mul_eq_zero_of_odd {L₁ L₂ : ℕ} (A : (Fin L₁ → Fin 4 → ℝ) → ℂ)
    (B : (Fin L₂ → Fin 4 → ℝ) → ℂ) (hA : ∀ ℓ, A (-ℓ) = -A ℓ) :
    QED.TwoLoop.jointEnergyFirstIntegral (L₁ + L₂) (fun ℓ =>
      A (fun s => ℓ (Fin.castAdd L₂ s)) * B (fun s => ℓ (Fin.natAdd L₁ s))) = 0 := by
  rw [jointEnergyFirstIntegral_mul, jointEnergyFirstIntegral_eq_zero_of_odd A hA, zero_mul]

end QED.GradedProof.X1C

end
