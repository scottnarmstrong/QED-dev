/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.Grading
public import QED.Frozen.Wick.VertexKindOrder
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace QED.Graded

/-- (G₂″) **The order in `e` of a graded vertex sequence**: (V₁) for each vertex, plus `2 k` for
each counterterm vertex of level `k`. A level-`k` counterterm vertex has order `2 (k + 1)`
(`fermionCt`, `photonCt`) or `2 (k + 1) + 1` (`gaugeCt`, which also carries one `e`); at level `0`
this is (V₁). -/
def gradedOrder {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ) : ℕ :=
  ∑ t, (κ t).order + ∑ t : CtVertex κ, 2 * g t

end QED.Graded

end
