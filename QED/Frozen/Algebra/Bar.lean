/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Algebra.Beta
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

@[expose] public section

open Matrix Complex

namespace QED.Dirac

/-- The Dirac adjoint `ū = u† β` of a column spinor, as a row vector (eq. (38.7)). -/
def bar (u : Fin 4 → ℂ) : Fin 4 → ℂ := star u ᵥ* beta

end QED.Dirac

end
