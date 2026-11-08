/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.VertexFunction
public import QED.Frozen.OneLoop.IsFormFactorPair
import QED.OneLoop.ChargeCondition

/-!
# Provider for `QED.OneLoop.isFormFactorPair_vertexOneLoop_iff_vertexFunction`

Proves packet 3's theorem goal (N) (decision D-15) as
`QED.Provider.OneLoop.isFormFactorPair_vertexOneLoop_iff_vertexFunction`, with the binder convention
of decision D-13. Until the frozen anchor is sealed, this module is quarantined; it must never
import the frozen anchor.
-/

@[expose] public section

open Matrix Complex
open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration
open scoped Real

namespace QED.Provider.OneLoop

/-- Packet 3's (N), with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem isFormFactorPair_vertexOneLoop_iff_vertexFunction {e Z₁ m mγ Λ : ℝ}
    (hm : 0 < m := by assumption)
    (hmγ : 0 < mγ := by assumption) (hΛ : 0 < Λ := by assumption) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2 := by assumption)
    (hp : Minkowski.dot p p = -m ^ 2 := by assumption) (hp0' : 0 < p' 0 := by assumption)
    (hp0 : 0 < p 0 := by assumption) {F : ℂ × ℂ} :
    IsFormFactorPair e m p' p (vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0) F ↔
      IsFormFactorPair e m p' p (vertexFunction e Z₁ m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0)
        ((Z₁ : ℂ) + F.1, F.2) :=
  isFormFactorPair_vertexOneLoop_iff_vertexFunction_aux hm hmγ hΛ hp' hp hp0' hp0 F

end QED.Provider.OneLoop

end
