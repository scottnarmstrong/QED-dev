/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.VacuumPolarizationLimit
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The photon counterterm in closed form

The on-shell condition `Π(0) = 0` (62.11) fixes the photon counterterm to `δ₃ = Π_loop(0)`
(`QED.WickModel.vacuumPolarizationLoop_onShell_iff`). This file evaluates `Π_loop(0)`: at `s = 0`
every Feynman mass is `M_f²`, and `∫₀¹ x (1 - x) dx = 1/6`, so

`Π_loop(0) = (e² / (12 π²)) ∑_f c_f log M_f²`,

the Pauli–Villars analogue of the source's (62.24).
-/

@[expose] public section

open Real

namespace QED.WickModel

/-- The one-loop vacuum-polarization coefficient at `k² = 0`:
`Π_loop(0) = (e² / (12 π²)) ∑_f c_f log M_f²`, the regulated analogue of (62.24). -/
theorem vacuumPolarizationLoop_zero (P : Params) :
    vacuumPolarizationLoop P 0 =
      P.e ^ 2 / (12 * π ^ 2) * ∑ f, P.loopCoeff f * Real.log (P.mass f ^ 2) := by
  have hint : ∫ x in (0 : ℝ)..1, x * (1 - x) = 1 / 6 := by
    have h : (fun x : ℝ => x * (1 - x)) = fun x => x - x ^ 2 := by
      funext x
      ring
    rw [h, intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
      (intervalIntegral.intervalIntegrable_pow 2), integral_id, integral_pow]
    norm_num
  unfold vacuumPolarizationLoop vacuumPolarizationFeynmanMass
  simp only [mul_zero, add_zero]
  rw [intervalIntegral.integral_mul_const, hint]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end QED.WickModel

end
