/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.VertexOneLoop
public import Mathlib.Topology.Order.Basic
public import Mathlib.Order.Filter.Basic

/-!
# Provider for `QED.OneLoop.tendsto_energyFirstIntegral_iff_vertexOneLoop`

Proves the characterization (F′) of the one-loop vertex (packet 2, decision D-14) as
`QED.Provider.OneLoop.tendsto_energyFirstIntegral_iff_vertexOneLoop`, with the binder convention
of decision D-13. This module must never import the frozen anchor.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open QED.OneLoop

namespace QED.Provider.OneLoop

/-- The characterization (F′), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem tendsto_energyFirstIntegral_iff_vertexOneLoop {e m mγ Λ : ℝ} (hm : 0 < m := by assumption)
    (hmγ : 0 < mγ := by assumption) (hΛ : 0 < Λ := by assumption) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2 := by assumption)
    (hp : Minkowski.dot p p = -m ^ 2 := by assumption) (hp0' : 0 < p' 0 := by assumption)
    (hp0 : 0 < p 0 := by assumption)
    {μ i j : Fin 4} {V : ℂ} :
    Tendsto (fun ε : ℝ => energyFirstIntegral fun ℓ => vertexIntegrand e m mγ Λ ε p' p μ ℓ i j)
        (𝓝[>] 0) (𝓝 V) ↔
      V = I * vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 μ i j := by
  have h := (QED.OneLoop.vertexLimit_existsUnique e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 μ i j).2
  have hc : I * vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 μ i j = h.exists.choose := by
    simp only [vertexOneLoop, Matrix.of_apply]
    field_simp
  rw [hc]
  exact ⟨fun hV => h.unique hV h.exists.choose_spec, fun hV => hV ▸ h.exists.choose_spec⟩

end QED.Provider.OneLoop

end
