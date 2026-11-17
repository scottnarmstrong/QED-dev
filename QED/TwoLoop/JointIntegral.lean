/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.JointEnergyFirstIntegral
public import QED.Frozen.OneLoop.EnergyFirstIntegral

/-!
# The joint energy-first integral at zero and one loops

The joint energy-first integral (T₉) of packet T1 (decision D-38) for `L = 0` and `L = 1`.

* `QED.TwoLoop.jointEnergyFirstIntegral_zero`: with no loop momenta it is the value of the
  integrand at the empty family.
* `QED.TwoLoop.jointEnergyFirstIntegral_one_eq`: with one loop momentum it is the frozen
  energy-first integral (D), for every integrand (the content of (T₁₂)).
-/

public section

open MeasureTheory

namespace QED.TwoLoop

/-- The joint energy-first integral of no loop momenta is the value at the empty family. -/
theorem jointEnergyFirstIntegral_zero (F : (Fin 0 → Fin 4 → ℝ) → ℂ) :
    jointEnergyFirstIntegral 0 F = F Fin.elim0 := by
  unfold jointEnergyFirstIntegral
  simp only [volume_pi, Measure.pi_of_empty (x := Fin.elim0), integral_dirac]
  congr 1
  funext s
  exact s.elim0

/-- The joint energy-first integral of one loop momentum is the frozen energy-first integral (D),
for every integrand. -/
theorem jointEnergyFirstIntegral_one_eq (F : (Fin 4 → ℝ) → ℂ) :
    jointEnergyFirstIntegral 1 (fun ℓ => F (ℓ 0)) = QED.OneLoop.energyFirstIntegral F := by
  unfold jointEnergyFirstIntegral QED.OneLoop.energyFirstIntegral
  have hin : ∀ v : Fin 1 → Fin 3 → ℝ, ∫ t : Fin 1 → ℝ, F (Fin.cons (t 0) (v 0)) =
      ∫ t : ℝ, F (Fin.cons t (v 0)) := fun v =>
    (volume_preserving_funUnique (Fin 1) ℝ).integral_comp'
      (g := fun t : ℝ => F (Fin.cons t (v 0)))
  simp_rw [hin]
  exact (volume_preserving_funUnique (Fin 1) (Fin 3 → ℝ)).integral_comp'
    (g := fun v : Fin 3 → ℝ => ∫ t : ℝ, F (Fin.cons t v))

end QED.TwoLoop

end
