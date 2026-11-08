/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.VertexIntegrand
public import QED.Frozen.OneLoop.EnergyFirstIntegral
public import Mathlib.Topology.Order.Basic
public import Mathlib.Order.Filter.Basic
import QED.OneLoop.VertexEnergyFirst

/-!
# Provider for `QED.OneLoop.vertexLimit_existsUnique`

This module proves the frozen theorem goal `QED.OneLoop.vertexLimit_existsUnique` (packet 1,
decision D-11) as `QED.Provider.OneLoop.vertexLimit_existsUnique`, with the exact frozen
statement. The frozen anchor is sealed with this theorem (2026-11-08) and has passed an
independent refute-first audit. This module must never import the frozen anchor.

The analysis is in `QED.OneLoop.VertexEnergyFirst`: Feynman parameters, the closed-form energy
integral, the uniform Pauli–Villars bound, and dominated convergence.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open QED.OneLoop QED.OneLoop.VertexLimit

namespace QED.Provider.OneLoop

/-- **Well-definedness of the regulated one-loop vertex.** This is the proposition of the
frozen goal `QED.OneLoop.vertexLimit_existsUnique`, with the same binders in the same order.
The data binders are implicit and the hypotheses are `by assumption` auto-parameters, so that
the frozen anchor is sealed by the bare term
`by exact QED.Provider.OneLoop.vertexLimit_existsUnique` that the frozen-anchor guard
requires (decision D-13). `autoParam T _` is reducibly `T`, so the proposition is unchanged. -/
theorem vertexLimit_existsUnique {e m mγ Λ : ℝ} (hm : 0 < m := by assumption)
    (hmγ : 0 < mγ := by assumption) (hΛ : 0 < Λ := by assumption) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2 := by assumption)
    (hp : Minkowski.dot p p = -m ^ 2 := by assumption) (hp0' : 0 < p' 0 := by assumption)
    (hp0 : 0 < p 0 := by assumption) {μ i j : Fin 4} :
    (∀ ε > 0,
      (∀ v : Fin 3 → ℝ,
        Integrable fun t : ℝ => vertexIntegrand e m mγ Λ ε p' p μ (Fin.cons t v : Fin 4 → ℝ) i j) ∧
      Integrable fun v : Fin 3 → ℝ =>
        ∫ t : ℝ, vertexIntegrand e m mγ Λ ε p' p μ (Fin.cons t v : Fin 4 → ℝ) i j) ∧
    ∃! V : ℂ, Tendsto
      (fun ε : ℝ => energyFirstIntegral fun ℓ => vertexIntegrand e m mγ Λ ε p' p μ ℓ i j)
      (𝓝[>] 0) (𝓝 V) := by
  have hlim := tendsto_energyFirstIntegral_vertexIntegrand (e := e) hm hmγ hΛ hp' hp hp0' hp0 μ i j
  refine ⟨fun ε hε => ⟨fun v => integrable_time_vertexIntegrand hε e m mγ Λ p' p μ i j v, ?_⟩,
    ⟨_, hlim, fun V hV => tendsto_nhds_unique hV hlim⟩⟩
  exact (integrable_spatialG hm hmγ hΛ hp' hp hp0' hp0 μ i j hε).congr
    (Eventually.of_forall fun v => (integral_vertexIntegrand_time hε e m mγ Λ p' p μ i j v).symm)

end QED.Provider.OneLoop

end
