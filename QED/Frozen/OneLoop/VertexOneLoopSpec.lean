-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.VertexOneLoop
public import QED.Provider.OneLoop.VertexOneLoopSpec
public import Mathlib.Topology.Order.Basic
public import Mathlib.Order.Filter.Basic

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory

namespace QED.OneLoop

/-- (F′) Characterization of (F): `V` is the `ε → 0⁺` limit of the energy-first integral of
the `(i, j)` entry of the integrand (C) exactly when `V = i V^μ_{1 loop}(p', p)_{ij}`. -/
theorem tendsto_energyFirstIntegral_iff_vertexOneLoop (e m mγ Λ : ℝ) (hm : 0 < m)
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ i j : Fin 4)
    (V : ℂ) :
    Tendsto (fun ε : ℝ => energyFirstIntegral fun ℓ => vertexIntegrand e m mγ Λ ε p' p μ ℓ i j)
        (𝓝[>] 0) (𝓝 V) ↔
      V = I * vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 μ i j :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.OneLoop.tendsto_energyFirstIntegral_iff_vertexOneLoop
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.OneLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
