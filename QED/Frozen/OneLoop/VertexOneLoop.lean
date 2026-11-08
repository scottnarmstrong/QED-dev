/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.VertexLimitExists

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory

namespace QED.OneLoop

/-- (F) The regulated one-loop vertex `V^μ_{1 loop}(p', p)` of the primary source's
(62.39)–(62.40), as a `4 × 4` matrix for each `μ`, with the regulators of decision D-5
(photon mass `m_γ`, Pauli–Villars mass `Λ`). The integrand (C) is that of `i V^μ_{1 loop}`,
so each entry is `1/i` times the unique `ε → 0⁺` limit of its energy-first integral
(prescription M1), which exists by theorem (E). Defined for `m, m_γ, Λ > 0` and on-shell
positive-energy momenta `p`, `p'`. -/
noncomputable def vertexOneLoop (e m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => (1 / I) *
    (vertexLimit_existsUnique e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 μ i j).2.exists.choose

end QED.OneLoop

end
