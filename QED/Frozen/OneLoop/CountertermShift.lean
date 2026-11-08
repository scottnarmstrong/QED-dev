-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.VertexFunction
public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.Provider.OneLoop.CountertermShift

@[expose] public section

open Matrix Complex

namespace QED.OneLoop

/-- (N) **The counterterm shifts only `F₁` (packet 3 theorem goal; obligation O-8).** For every
real `Z₁` and on-shell positive-energy momenta, `(A, B)` is a form-factor pair (G₀) of the
one-loop vertex (F) exactly when `(Z₁ + A, B)` is a form-factor pair of the vertex function (J). -/
theorem isFormFactorPair_vertexOneLoop_iff_vertexFunction (e Z₁ m mγ Λ : ℝ) (hm : 0 < m)
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (F : ℂ × ℂ) :
    IsFormFactorPair e m p' p (vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0) F ↔
      IsFormFactorPair e m p' p (vertexFunction e Z₁ m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0)
        ((Z₁ : ℂ) + F.1, F.2) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.OneLoop.isFormFactorPair_vertexOneLoop_iff_vertexFunction
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.OneLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
