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

/-- Covariant components `p_μ = g_{μν} p^ν`. -/
def lower (p : Fin 4 → ℝ) (μ : Fin 4) : ℝ :=
  ∑ ν, metric μ ν * p ν

end QED.Minkowski

end
