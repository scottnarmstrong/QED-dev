/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.VertexOneLoop
public import QED.Frozen.OneLoop.IsFormFactorPair
import QED.OneLoop.FormFactorPair

/-!
# Provider for `QED.OneLoop.existsUnique_isFormFactorPair_vertexOneLoop`

Proves packet 2's theorem goal (G) (decision D-14) as
`QED.Provider.OneLoop.existsUnique_isFormFactorPair_vertexOneLoop`, with the binder convention of
decision D-13. Existence is the closed-form sandwich of the one-loop vertex; uniqueness is the
independence of the two on-shell structures. The frozen anchor is sealed with this theorem (2026-11-08) and passed an
independent refute-first audit. This module must never import the frozen anchor.
-/

@[expose] public section

open Matrix Complex
open QED.OneLoop QED.OneLoop.VertexLimit

namespace QED.Provider.OneLoop

/-- Packet 2's (G), with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem existsUnique_isFormFactorPair_vertexOneLoop {e m mγ Λ : ℝ}
    (he : e ≠ 0 := by assumption) (hm : 0 < m := by assumption)
    (hmγ : 0 < mγ := by assumption) (hΛ : 0 < Λ := by assumption) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2 := by assumption)
    (hp : Minkowski.dot p p = -m ^ 2 := by assumption) (hp0' : 0 < p' 0 := by assumption)
    (hp0 : 0 < p 0 := by assumption)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p) := by assumption) :
    ∃! F : ℂ × ℂ,
      IsFormFactorPair e m p' p (vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0) F :=
  ⟨_, isFormFactorPair_vertexOneLoop hm hmγ hΛ hp' hp hp0' hp0,
    fun _ hF => eq_of_isFormFactorPair_vertexOneLoop he hm hmγ hΛ hp' hp hp0' hp0 hq hF⟩

end QED.Provider.OneLoop

end
