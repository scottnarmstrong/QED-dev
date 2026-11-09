/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.EnergyFirstIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Translations and reflection of the energy-first integral

The energy-first integral `QED.OneLoop.energyFirstIntegral F = ∫ d³v (∫ dt F(t, v))` is
invariant under a shift `ℓ ↦ ℓ - c` of the loop momentum and under the reflection `ℓ ↦ -ℓ`. Both
stages are Lebesgue integrals, which are translation and reflection invariant even for
non-integrable data (both sides are then `0`), so no hypothesis on `F` is needed.

## Main statements

* `QED.OneLoop.energyFirstIntegral_sub_right_eq_self`: invariance under `ℓ ↦ ℓ - c`.
* `QED.OneLoop.energyFirstIntegral_add_right_eq_self`: invariance under `ℓ ↦ ℓ + c`.
* `QED.OneLoop.energyFirstIntegral_neg_eq_self`: invariance under `ℓ ↦ -ℓ`.
-/

@[expose] public section

open MeasureTheory

namespace QED.OneLoop

/-- The energy-first integral is invariant under the shift `ℓ ↦ ℓ - c` of the loop momentum,
for every integrand. -/
theorem energyFirstIntegral_sub_right_eq_self (F : (Fin 4 → ℝ) → ℂ) (c : Fin 4 → ℝ) :
    energyFirstIntegral (fun ℓ => F (ℓ - c)) = energyFirstIntegral F := by
  unfold energyFirstIntegral
  have h : ∀ (t : ℝ) (v : Fin 3 → ℝ), (Fin.cons t v : Fin 4 → ℝ) - c =
      Fin.cons (t - c 0) (v - Fin.tail c) := fun t v => by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]
  simp_rw [h]
  rw [← integral_sub_right_eq_self (fun v : Fin 3 → ℝ => ∫ t : ℝ, F (Fin.cons t v))
    (Fin.tail c)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun v =>
    integral_sub_right_eq_self (fun t : ℝ => F (Fin.cons t (v - Fin.tail c))) (c 0))

/-- The energy-first integral is invariant under the shift `ℓ ↦ ℓ + c` of the loop momentum,
for every integrand. -/
theorem energyFirstIntegral_add_right_eq_self (F : (Fin 4 → ℝ) → ℂ) (c : Fin 4 → ℝ) :
    energyFirstIntegral (fun ℓ => F (ℓ + c)) = energyFirstIntegral F := by
  simpa [sub_neg_eq_add] using energyFirstIntegral_sub_right_eq_self F (-c)

/-- The energy-first integral is invariant under the reflection `ℓ ↦ -ℓ` of the loop momentum,
for every integrand. -/
theorem energyFirstIntegral_neg_eq_self (F : (Fin 4 → ℝ) → ℂ) :
    energyFirstIntegral (fun ℓ => F (-ℓ)) = energyFirstIntegral F := by
  unfold energyFirstIntegral
  have h : ∀ (t : ℝ) (v : Fin 3 → ℝ), -(Fin.cons t v : Fin 4 → ℝ) = Fin.cons (-t) (-v) :=
    fun t v => by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
  simp_rw [h]
  rw [← integral_neg_eq_self (fun v : Fin 3 → ℝ => ∫ t : ℝ, F (Fin.cons t v))]
  exact integral_congr_ae (Filter.Eventually.of_forall fun v =>
    integral_neg_eq_self (fun t : ℝ => F (Fin.cons t (-v))) volume)

end QED.OneLoop

end
