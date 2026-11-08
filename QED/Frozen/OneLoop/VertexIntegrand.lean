/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.ElectronPropagator
public import QED.Frozen.OneLoop.PhotonPropagator
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

open Matrix Complex

namespace QED.OneLoop

/-- (C) The integrand of `i V^μ_{1 loop}(p', p)` (note the factor `i`) in the primary source's
(62.40), including the measure factor `1/(2π)⁴`:
`(ie)³ (1/i)³ (2π)⁻⁴ [γ^ρ S̃(p̸' + ℓ̸) γ^μ S̃(p̸ + ℓ̸) γ^ν] Δ̃_{νρ}(ℓ)`,
with the propagators (A) and (B); `p` is the incoming and `p'` the outgoing electron
momentum, in the source's argument order `(p', p)`. Only `ε > 0` is source-facing. -/
noncomputable def vertexIntegrand (e m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((I * e) ^ 3 * (1 / I) ^ 3 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹) •
    ∑ ν, ∑ ρ, photonPropagator mγ Λ ε ℓ ν ρ •
      (Dirac.gamma ρ * electronPropagator m ε (p' + ℓ) * Dirac.gamma μ *
        electronPropagator m ε (p + ℓ) * Dirac.gamma ν)

end QED.OneLoop

end
