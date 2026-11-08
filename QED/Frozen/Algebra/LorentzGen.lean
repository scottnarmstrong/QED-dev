/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Algebra.Gamma
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

open Matrix Complex

namespace QED.Dirac

/-- The Lorentz generators `S^{μν} = (i/4) [γ^μ, γ^ν]` (eq. (40.3)). -/
noncomputable def lorentzGen (μ ν : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  (I / 4) • (gamma μ * gamma ν - gamma ν * gamma μ)

end QED.Dirac

end
