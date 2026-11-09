/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.VertexOneLoopSpec
public import QED.OneLoop.VertexOffShell

/-!
# The off-shell vertex limit at the shell

`QED.OneLoop.VertexOffShell.exists_tendsto_vertexIntegral_offShell` gives, near on-shell
positive-energy momenta `(p', p)`, the limit `V r' r` of the energy-first integral of the
regulated one-loop vertex as `ε → 0⁺`, continuous at `(p', p)`. This module records the
integrability of both energy-first stages at the nearby momenta and identifies the value at the
shell with the frozen one-loop vertex through its frozen characterization
`QED.OneLoop.tendsto_energyFirstIntegral_iff_vertexOneLoop`:
`V p' p = i V^μ_{1 loop}(p', p)_{ij}`.

## Main statements

* `exists_tendsto_vertexIntegral_offShell_spec`: the off-shell limit with integrability, continuity
  at the shell, and the on-shell value `V p' p = I * vertexOneLoop … μ i j`.

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open QED.OneLoop QED.OneLoop.VertexLimit

namespace QED.OneLoop.VertexOffShell

/-- **The one-loop vertex limit off the mass shell, with its on-shell value.** Near on-shell
positive-energy momenta `(p', p)` there are `δ > 0` and `V` such that, for all momenta `(r', r)`
within `δ` of `(p', p)`, both stages of the energy-first integral of each entry of the regulated
one-loop vertex integrand are integrable at every `ε > 0` and the energy-first integral converges
to `V r' r` as `ε → 0⁺`; `V` is continuous at `(p', p)`, and its value there is the frozen
one-loop vertex entry `i V^μ_{1 loop}(p', p)_{ij}`. -/
theorem exists_tendsto_vertexIntegral_offShell_spec {e m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ)
    (hΛ : 0 < Λ) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ i j : Fin 4) :
    ∃ δ > 0, ∃ V : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℂ,
      (∀ r' r : Fin 4 → ℝ, dist r' p' < δ → dist r p < δ →
        (∀ ε > 0,
          (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
            vertexIntegrand e m mγ Λ ε r' r μ (Fin.cons t v : Fin 4 → ℝ) i j) ∧
          Integrable fun v : Fin 3 → ℝ =>
            ∫ t : ℝ, vertexIntegrand e m mγ Λ ε r' r μ (Fin.cons t v : Fin 4 → ℝ) i j) ∧
        Tendsto (fun ε : ℝ => energyFirstIntegral fun ℓ =>
            vertexIntegrand e m mγ Λ ε r' r μ ℓ i j) (𝓝[>] 0) (𝓝 (V r' r))) ∧
      ContinuousAt (fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => V x.1 x.2) (p', p) ∧
      V p' p = I * vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 μ i j := by
  have hlim := eventually_tendsto_energyFirstIntegral (e := e) hm hmγ hΛ hp' hp hp0' hp0 μ i j
  have hint := eventually_integrable_energyFirst (e := e) hm hmγ hΛ hp' hp hp0' hp0 μ i j
  have hcont := continuousAt_integral_spatialG_zero (e := e) hm hmγ hΛ hp' hp hp0' hp0 μ i j
  have hval := (tendsto_energyFirstIntegral_iff_vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp
    hp0' hp0 μ i j _).1 hlim.self_of_nhds
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hint.and hlim)
  refine ⟨δ, hδ, fun r' r => ∫ v, spatialG e m mγ Λ 0 r' r μ i j v, ?_, ?_, ?_⟩
  · intro r' r hr' hr
    have hd : dist (r', r) (p', p) < δ := by
      rw [Prod.dist_eq]
      exact max_lt hr' hr
    have h := hball hd
    exact h
  · exact hcont
  · exact hval

end QED.OneLoop.VertexOffShell

end
