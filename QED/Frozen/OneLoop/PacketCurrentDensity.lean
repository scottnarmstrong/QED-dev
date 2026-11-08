/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.OneLoop.OneParticle
public import QED.Frozen.OneLoop.VertexFunction
public import QED.Frozen.Algebra.Bar
public import QED.Frozen.Algebra.Spinor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

open Matrix Complex MeasureTheory

namespace QED.OneLoop

/-- (W₁) The current density `⟨e|J²(x)|e⟩` at time `0` of the one-electron wave packet
`|e⟩ = ∫ d̃k f(k⃗) b₊†(k⃗)|0⟩` with spin up along `z` (64.4), for the real rotationally invariant
profile `f(k⃗) = φ(|k⃗|²/λ²)` (decision D-17), following (64.8)–(64.9):
`∫ d̃k ∫ d̃k' f(k⃗') f(k⃗) e^{i(k⃗ - k⃗')·x⃗} ū₊(k') V²(k', k) u₊(k)`, with
`d̃k = d³k/((2π)³ 2ω)` (3.18), the one-particle normalization (41.5), and `V` the vertex
function (J). The one-electron matrix elements `⟨k'|J^μ(0)|k⟩` of the current are taken to be
the sandwiches `ū₊(k') V^μ(k', k) u₊(k)` of the amputated vertex between on-shell spinors, with
unit electron residues and no photon-leg factor (obligation O-3), as in the response definition
(R₀); no form-factor values are inserted (ruling D-9). -/
noncomputable def packetCurrentDensity (e Z₁ m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ)
    (hΛ : 0 < Λ) (φ : ℝ → ℝ) (lam : ℝ) (x : Fin 3 → ℝ) : ℂ :=
  ∫ k : Fin 3 → ℝ, ∫ k' : Fin 3 → ℝ,
    ((φ ((∑ j, k' j ^ 2) / lam ^ 2) * φ ((∑ j, k j ^ 2) / lam ^ 2)
      / ((2 * Real.pi) ^ 3 * (2 * oneParticleMomentum m k 0)
        * ((2 * Real.pi) ^ 3 * (2 * oneParticleMomentum m k' 0))) : ℝ) : ℂ)
    * Complex.exp (I * ((∑ j, (k j - k' j) * x j : ℝ) : ℂ))
    * (Dirac.bar (Dirac.spinor m (oneParticleMomentum m k') 0) ⬝ᵥ
        (vertexFunction e Z₁ m mγ Λ hm hmγ hΛ (oneParticleMomentum m k') (oneParticleMomentum m k)
          (dot_oneParticleMomentum m k') (dot_oneParticleMomentum m k)
          (oneParticleMomentum_pos hm k') (oneParticleMomentum_pos hm k) 2
          *ᵥ Dirac.spinor m (oneParticleMomentum m k) 0))

end QED.OneLoop

end
