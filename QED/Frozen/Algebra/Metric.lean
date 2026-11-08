/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace QED.Minkowski

/-- The Minkowski metric `g_{μν} = diag(-1, 1, 1, 1)` (mostly plus). -/
def metric (μ ν : Fin 4) : ℝ :=
  if μ = ν then (if μ = 0 then -1 else 1) else 0

end QED.Minkowski

end
