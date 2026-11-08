-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.VertexOneLoop
public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.Provider.OneLoop.FormFactorExistsUnique

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory

namespace QED.OneLoop

/-- (G) **Form factors of the one-loop vertex (packet 2 theorem goal).** For `e ≠ 0` and on-shell
positive-energy momenta with spacelike momentum transfer (`q² > 0`, equivalently `p ≠ p'`), the
one-loop vertex (F) has exactly one form-factor pair (G₀). Its first component is the `γ^μ`
coefficient of the loop diagram alone (the counterterm `(Z₁ - 1) e γ^μ` of (62.39) adds to it);
its second is the order-`e²` Pauli form factor, to which the counterterm does not contribute. -/
theorem existsUnique_isFormFactorPair_vertexOneLoop (e m mγ Λ : ℝ) (he : e ≠ 0) (hm : 0 < m)
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) :
    ∃! F : ℂ × ℂ,
      IsFormFactorPair e m p' p (vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0) F :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.OneLoop.existsUnique_isFormFactorPair_vertexOneLoop
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.OneLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
