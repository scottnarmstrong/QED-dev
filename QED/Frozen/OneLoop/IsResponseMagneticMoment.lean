/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.VertexFunction
public import QED.Frozen.Algebra.Bar
public import QED.Frozen.Algebra.Spinor
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

open Matrix Complex

namespace QED.OneLoop

/-- (R₀) **The magnetic moment, response definition** (author ruling D-9). It is read off from
the vertex function (J) in the field of the primary source's p. 383, used in (64.6)–(64.7): the
constant magnetic field `B` along `z` with vector potential `A = (0, B x, 0)`, whose interaction
`-∫ J·A` couples the current component `J²` to momentum transfer along `x`. For Breit-frame
on-shell momenta `p = (E, -q/2, 0, 0)`, `p' = (E, q/2, 0, 0)` with `q > 0`, and the spin-up
spinors `u₊ = u_0(p)`, `ū₊' = ū_0(p')` (spin up along `z`, (38.6), (38.12)), the static-field
matrix element `ū₊(p') V²(p', p) u₊(p)` equals `2 i m μ q + o(q)` as `q → 0⁺`. In this geometry
the matrix element has no spin-independent part (the convection term `(p + p')²` and any `q²`
term vanish), so `μ` is the coefficient of its spin-dependent, linear-in-`q` part. For the tree
vertex `e γ^μ` this gives the Bohr magneton `e/(2m)`, that is `g = 2` in (64.16). The predicate is
defined for every counterterm `Z₁`; the physical one is fixed by the charge condition (K₀). -/
def IsResponseMagneticMoment (e Z₁ m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (μ : ℝ) : Prop :=
  ∀ η > 0, ∃ δ > 0, ∀ (q : ℝ) (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0),
    0 < q → q < δ → p' 1 = q / 2 → p 1 = -(q / 2) → p' 2 = 0 → p 2 = 0 → p' 3 = 0 →
    p 3 = 0 →
    ‖Dirac.bar (Dirac.spinor m p' 0) ⬝ᵥ
        (vertexFunction e Z₁ m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 2 *ᵥ Dirac.spinor m p 0)
      - 2 * I * m * μ * q‖ ≤ η * q

end QED.OneLoop

end
