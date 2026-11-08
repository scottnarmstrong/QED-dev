/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Basic.Complex.Basic

@[expose] public section

open MeasureTheory

namespace QED.OneLoop

/-- (D) The energy-first iterated integral of prescription M1 (`docs/REGULARIZATION.md`,
section 4): `∫ d³ℓ (∫ dℓ⁰ F(ℓ⁰, ℓ⃗))`, the energy integral innermost. Index `0` is time.
Like Mathlib's Bochner integral it returns `0` on non-integrable data, so source-facing
statements that use it assert the integrability of both stages explicitly. -/
noncomputable def energyFirstIntegral (F : (Fin 4 → ℝ) → ℂ) : ℂ :=
  ∫ v : Fin 3 → ℝ, ∫ t : ℝ, F (Fin.cons t v : Fin 4 → ℝ)

end QED.OneLoop

end
