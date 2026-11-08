/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.Minkowski
public import Mathlib.Basic.Complex.Basic

@[expose] public section

open Complex

namespace QED.OneLoop

/-- (B) The regulated Feynman-gauge photon propagator `Δ̃_{μν}(k)`: the source's (62.29)
with photon mass `m_γ`, minus the Pauli–Villars term of mass `Λ` (decision D-5):
`g_{μν} [1 / (k² + m_γ² - iε) - 1 / (k² + Λ² - iε)]`. Only `ε > 0` is source-facing. -/
noncomputable def photonPropagator (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  ((Minkowski.metric μ ν : ℝ) : ℂ) *
    ((((Minkowski.dot k k + mγ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹
      - (((Minkowski.dot k k + Λ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹)

end QED.OneLoop

end
