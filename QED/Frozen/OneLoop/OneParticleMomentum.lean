/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace QED.OneLoop

/-- (W₀) The on-shell four-momentum `(ω, k⃗)` of a one-electron state with spatial momentum `k⃗`,
`ω = √(m² + |k⃗|²)` (3.11). -/
noncomputable def oneParticleMomentum (m : ℝ) (k : Fin 3 → ℝ) : Fin 4 → ℝ :=
  Fin.cons (Real.sqrt (m ^ 2 + ∑ j, k j ^ 2)) k

end QED.OneLoop

end
