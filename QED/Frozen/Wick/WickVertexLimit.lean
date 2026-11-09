-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.WickVertex
public import QED.Frozen.OneLoop.VertexFunction
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.Basic
public import QED.Provider.Wick.WickVertexLimit
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm

@[expose] public section

open Complex Filter Topology

namespace QED.Wick

/-- (W₂) **The vertex function is the Wick vertex (packet 5 headline goal).** For `m, m_γ, Λ > 0`
and on-shell positive-energy momenta, `(1/i)` times the Wick vertex (V₂₂) tends, as `ε → 0⁺`,
entry by entry to the vertex function (J) with counterterm `Z₁ = 1 + δ₁`, for every value of
the two-point counterterms. -/
theorem tendsto_wickVertex (e δ₁ δ₂ δm δ₃ m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ i j : Fin 4) :
    Tendsto (fun ε => (1 / I) * wickVertex e δ₁ δ₂ δm δ₃ m mγ Λ ε p' p μ i j) (𝓝[>] 0)
      (𝓝 (QED.OneLoop.vertexFunction e (1 + δ₁) m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 μ i j)) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Wick

end
-- FROZEN_ANCHOR_SUFFIX_END
