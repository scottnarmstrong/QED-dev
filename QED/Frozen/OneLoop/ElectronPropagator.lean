/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.Dirac

@[expose] public section

open Matrix Complex

namespace QED.OneLoop

/-- (A) The free electron propagator `S̃(p̸) = (-p̸ + m) / (p² + m² - iε)` of the primary
source (rule 9, p. 349; stated after (62.12), p. 371), mostly-plus metric. Only `ε > 0`
(the Feynman prescription) is source-facing; at `ε = 0` Lean's `0⁻¹ = 0` makes the value
meaningless on the mass shell. -/
noncomputable def electronPropagator (m ε : ℝ) (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (((Minkowski.dot p p + m ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹ • ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash p)

end QED.OneLoop

end
