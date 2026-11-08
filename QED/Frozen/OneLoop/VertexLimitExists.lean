-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.VertexIntegrand
public import QED.Frozen.OneLoop.EnergyFirstIntegral
public import QED.Provider.OneLoop.VertexLimitExists
public import Mathlib.Topology.Order.Basic
public import Mathlib.Order.Filter.Basic

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory

namespace QED.OneLoop

/-- (E) **Well-definedness of the regulated one-loop vertex (packet 1 theorem goal).**
For an electron of mass `m > 0`, photon regulator masses `m_γ > 0`, `Λ > 0`, and
on-shell positive-energy electron momenta `p`, `p'` (`p² = p'² = -m²`), each matrix entry
of the (62.40) integrand has, for every `ε > 0`, an integrable energy integrand at each
spatial momentum and an energy integral that is integrable over `ℝ³`, and the energy-first
integral has a unique limit as `ε → 0⁺`. -/
theorem vertexLimit_existsUnique (e m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ i j : Fin 4) :
    (∀ ε > 0,
      (∀ v : Fin 3 → ℝ,
        Integrable fun t : ℝ => vertexIntegrand e m mγ Λ ε p' p μ (Fin.cons t v : Fin 4 → ℝ) i j) ∧
      Integrable fun v : Fin 3 → ℝ =>
        ∫ t : ℝ, vertexIntegrand e m mγ Λ ε p' p μ (Fin.cons t v : Fin 4 → ℝ) i j) ∧
    ∃! V : ℂ, Tendsto (fun ε : ℝ => energyFirstIntegral fun ℓ => vertexIntegrand e m mγ Λ ε p' p μ ℓ i j)
      (𝓝[>] 0) (𝓝 V) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.OneLoop.vertexLimit_existsUnique
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.OneLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
