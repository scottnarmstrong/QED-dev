/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.OneLoopBridge

/-!
# The `d`-dimensional Dirac-trace scheme of projected numerators

**Scheme convention (not a theorem).** In dimensional regularization the Dirac algebra of a
projected numerator is continued in `d` by the conventional `d`-dimensional trace algebra:
`{γ^μ, γ^ν} = 2 g^{μν}`, `g^μ_μ = d`, `tr 1 = 4`, no `γ₅`. Applied to a projected numerator it
gives a polynomial in `d` (with the scalar products of the momenta and the Feynman parameters as
the other variables) that agrees with the four-dimensional trace at `d = 4`. This polynomial is
a choice of scheme, not a consequence of the model: the model is four-dimensional and only
the value at `d = 4` is fixed by it. Different consistent continuations change the
`O(d - 4)` part of the numerator; such a change can move finite terms only where it multiplies
a pole in `d - 4`.

This file collects the projected numerators used by the model ↔ dimensional-regularization
bridge so that one ruling covers all of them. For each:
* a named, exposed definition, whose docstring states the `d`-dimensional numerator;
* a proved theorem that at `d = 4` it equals the numerator of the model's four-dimensional
  trace.

## Projected numerators

* One loop, Pauli projection at `q = 0` (`m = 1`): `QED.DimReg.OneLoopBridge.pauliNum`,
  `N_d(w) = 2w(1 - w) + (4 - d) w²` (defined in `QED/DimReg/OneLoopBridge.lean`, derivation in
  its module docstring); restated as `oneLoopPauliNum_eq`, with the `d = 4` check
  `oneLoopPauliNum_four` against the numerator `2w((1 - w) - (1 - w)²) m²` of the model's
  `QED.OneLoop.VertexLimit.pauliIntegrand`.
-/

@[expose] public section

namespace QED.DimReg.TwoLoopBridgeTrace

open QED.DimReg.OneLoopBridge

/-- **Scheme (one loop, Pauli projection at `q = 0`).** The `d`-dimensional Pauli numerator of
the one-loop vertex, from the `d`-dimensional contractions
`γ^ν a̸ γ^μ b̸ γ_ν = -2 b̸ γ^μ a̸ + (4 - d) a̸ γ^μ b̸` and the Gordon identity, as a function of the
total electron weight `w` (`m = 1`): `N_d(w) = 2w(1 - w) + (4 - d) w²`. -/
theorem oneLoopPauliNum_eq (d : ℂ) (w : ℝ) :
    pauliNum d w = 2 * w * (1 - w) + (4 - d) * (w : ℂ) ^ 2 := rfl

/-- **The `d = 4` check (one loop).** At `d = 4` the scheme numerator, times the Jacobian `w`
and `m²`, is the numerator `2w((1 - w) - (1 - w)²) m²` of the model's four-dimensional trace
(`QED.OneLoop.VertexLimit.pauliIntegrand`). -/
theorem oneLoopPauliNum_four (w m : ℝ) :
    (w : ℂ) * pauliNum 4 w * (m : ℂ) ^ 2 =
      ((2 * w * ((1 - w) - (1 - w) ^ 2) * m ^ 2 : ℝ) : ℂ) :=
  pauliNum_four w m

/-- The part of the one-loop numerator set by the scheme rather than by the model:
`N_d - N_4 = (4 - d) w²`. -/
theorem oneLoopPauliNum_sub_four (d : ℂ) (w : ℝ) :
    pauliNum d w - pauliNum 4 w = (4 - d) * (w : ℂ) ^ 2 := by
  simp only [pauliNum]
  ring

end QED.DimReg.TwoLoopBridgeTrace
