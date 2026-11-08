/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Algebra.Slash
public import QED.Frozen.Algebra.LorentzGen
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

@[expose] public section

open Matrix Complex

namespace QED.OneLoop

/-- (G₀) The on-shell form-factor decomposition of the primary source's (63.18). The pair
`F = (A, B)` decomposes the vertex `V^μ` at momenta `(p', p)` if
`ū' V^μ u = e ū' [A γ^μ - (i/m) B S^{μν} q_ν] u`, with `q = p' - p` and
`S^{μν} = (i/4)[γ^μ, γ^ν]`, for every `μ`, every column `u` with `(p̸ + m) u = 0`, and every
row `ū'` with `ū' (p̸' + m) = 0`. For the full vertex, `A` and `B` are the form factors
`F₁(q²)` and `F₂(q²)`. Source-facing for `m > 0` and on-shell `p`, `p'`: there these solution
spaces are spanned by `u_s(p)` and `ū_{s'}(p')` ((38.1), (38.16)), so the predicate is (63.18)
for all spins `s, s'`. Off shell it is vacuous. -/
def IsFormFactorPair (e m : ℝ) (p' p : Fin 4 → ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (F : ℂ × ℂ) : Prop :=
  ∀ (μ : Fin 4) (u w : Fin 4 → ℂ), Dirac.slash p *ᵥ u = -((m : ℂ) • u) →
    w ᵥ* Dirac.slash p' = -((m : ℂ) • w) →
    w ⬝ᵥ (V μ *ᵥ u) = (e : ℂ) * (w ⬝ᵥ ((F.1 • Dirac.gamma μ - (I / (m : ℂ) * F.2) •
      ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • Dirac.lorentzGen μ ν) *ᵥ u))

end QED.OneLoop

end
