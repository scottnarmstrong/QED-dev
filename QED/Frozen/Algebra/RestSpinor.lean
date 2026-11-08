/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

open Matrix Complex

namespace QED.Dirac

/-- Rest spinors `u_±(0)` of eq. (38.6), for `m > 0`; spin label `0 ↦ +` (spin up along `z`,
`S_z u_+(0) = +½ u_+(0)`, (38.3)), `1 ↦ -`. -/
noncomputable def restSpinor (m : ℝ) : Fin 2 → Fin 4 → ℂ
  | 0 => ![(Real.sqrt m : ℂ), 0, (Real.sqrt m : ℂ), 0]
  | 1 => ![0, (Real.sqrt m : ℂ), 0, (Real.sqrt m : ℂ)]

end QED.Dirac

end
