/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Algebra.Metric
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace QED.Minkowski

/-- The Minkowski bilinear form `p·k = g_{μν} p^μ k^ν`. -/
def dot (p k : Fin 4 → ℝ) : ℝ :=
  ∑ μ, ∑ ν, metric μ ν * p μ * k ν

end QED.Minkowski

end
