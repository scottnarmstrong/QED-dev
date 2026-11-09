/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.Params
public import QED.Frozen.WickModel.ParamsMass
public import QED.Frozen.WickModel.ParamsLoopCoeff
public import QED.Frozen.OneLoop.ElectronPropagator
public import QED.Frozen.OneLoop.PhotonPropagator
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The one-loop two-point integrands

The integrands of the one-loop self-energy and vacuum polarization, written as in the source.
They are working objects for the proofs of packet 6b (decisions D-23, D-25), not frozen
declarations. They include the loop measure `(2π)⁻⁴`.

* `selfEnergyIntegrand`: the integrand of the loop term of `i Σ(p̸)` in (62.28),
  `(i e)² (1/i)² γ^ν S̃(p̸ + ℓ̸) γ^μ Δ̃_{μν}(ℓ)`.
* `vacuumPolarizationIntegrand`: the integrand of the loop term of `i Π^{μν}(k)` in (62.12),
  `(-1) (i e)² (1/i)² Tr[S̃(ℓ̸ + k̸) γ^μ S̃(ℓ̸) γ^ν]`, with the fermion loop regulated by the
  Pauli–Villars flavors of decision D-22: `∑_f c_f` times the loop of mass `M_f`.
-/

@[expose] public section

open Complex

namespace QED.WickModel

/-- The integrand of the loop term of `i Σ(p̸)` in (62.28), including `(2π)⁻⁴`:
`(i e)² (1/i)² (2π)⁻⁴ ∑_{μν} Δ̃_{μν}(ℓ) γ^ν S̃(p + ℓ) γ^μ`. -/
noncomputable def selfEnergyIntegrand (P : Params) (ε : ℝ) (p ℓ : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ((I * P.e) ^ 2 * (1 / I) ^ 2 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹) •
    ∑ μ, ∑ ν, QED.OneLoop.photonPropagator P.mγ P.Λ ε ℓ μ ν •
      (Dirac.gamma ν * QED.OneLoop.electronPropagator P.m ε (p + ℓ) * Dirac.gamma μ)

/-- The integrand of the loop term of `i Π^{μν}(k)` in (62.12), including `(2π)⁻⁴`, with the
fermion loop regulated by the Pauli–Villars flavors (decision D-22):
`(-1) (i e)² (1/i)² (2π)⁻⁴ ∑_f c_f Tr[S̃_f(ℓ + k) γ^μ S̃_f(ℓ) γ^ν]`. -/
noncomputable def vacuumPolarizationIntegrand (P : Params) (ε : ℝ) (k ℓ : Fin 4 → ℝ)
    (μ ν : Fin 4) : ℂ :=
  (-1) * (I * P.e) ^ 2 * (1 / I) ^ 2 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
    ∑ f, (P.loopCoeff f : ℂ) *
      Matrix.trace (QED.OneLoop.electronPropagator (P.mass f) ε (ℓ + k) * Dirac.gamma μ *
        QED.OneLoop.electronPropagator (P.mass f) ε ℓ * Dirac.gamma ν)

end QED.WickModel

end
