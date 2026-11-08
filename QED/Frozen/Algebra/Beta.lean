/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

open Matrix Complex

namespace QED.Dirac

/-- The matrix `β` of the Dirac adjoint `Ψ̄ = Ψ† β` (eq. (38.8)). -/
def beta : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

end QED.Dirac

end
