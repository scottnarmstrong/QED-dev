-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.VertexOneLoop
public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.Provider.OneLoop.PauliFormFactorLimit
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory

namespace QED.OneLoop

/-- (I) **The one-loop anomaly (packet 2 headline goal).** For `e ≠ 0`, the order-`e²` Pauli
form factor of the one-loop vertex (F) tends to `e²/(8π²)`, that is `α/(2π)` with
`α = e²/(4π)` (63.22), jointly as `q² → 0⁺` over on-shell positive-energy pairs, `m_γ → 0⁺`,
and `Λ → ∞`. The limit is uniform over the pairs: `δ` and `R` depend only on `e`, `m`, and `η`.
Near the limit a form-factor pair (G₀) exists, and every such pair has its second component
within `η` of `e²/(8π²)`. The joint limit implies the iterated order of limits of decision D-5.
It replaces `F₂(0)` without presupposing that `F₂` depends on `(p', p)` only through `q²`. -/
theorem isFormFactorPair_vertexOneLoop_pauli_limit (e m : ℝ) (he : e ≠ 0) (hm : 0 < m) (η : ℝ)
    (hη : 0 < η) :
    ∃ δ > 0, ∃ R : ℝ, ∀ (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ) (p' p : Fin 4 → ℝ)
      (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
      (hp0' : 0 < p' 0) (hp0 : 0 < p 0),
      0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < δ →
      mγ < δ → R < Λ →
      (∃ F : ℂ × ℂ,
        IsFormFactorPair e m p' p (vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0) F) ∧
      ∀ F : ℂ × ℂ,
        IsFormFactorPair e m p' p (vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0) F →
        ‖F.2 - ((e ^ 2 / (8 * Real.pi ^ 2) : ℝ) : ℂ)‖ < η :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.OneLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
