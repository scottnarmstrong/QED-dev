/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Algebra.Gamma
public import QED.Frozen.Algebra.Lower

@[expose] public section

open Matrix Complex

namespace QED.Dirac

/-- Feynman slash `p̸ = γ^μ p_μ` of a real four-vector, with `p_μ` the covariant
components for the mostly-plus metric. -/
def slash (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ μ, ((Minkowski.lower p μ : ℝ) : ℂ) • gamma μ

end QED.Dirac

end
