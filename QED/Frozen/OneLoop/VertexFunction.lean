/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.VertexOneLoop

@[expose] public section

open Matrix Complex

namespace QED.OneLoop

/-- (J) The regulated vertex function `V^μ(p', p)` of the primary source's (62.39) through order
`e³`: the counterterm-corrected tree vertex `Z₁ e γ^μ` plus the one-loop vertex (F). The
counterterm coefficient `Z₁` is a parameter here; the charge condition (K₀) fixes it. Defined for
`m, m_γ, Λ > 0` and on-shell positive-energy momenta `p`, `p'`. -/
noncomputable def vertexFunction (e Z₁ m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((Z₁ * e : ℝ) : ℂ) • Dirac.gamma μ + vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 μ

end QED.OneLoop

end
