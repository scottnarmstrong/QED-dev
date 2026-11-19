/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.CtVertex

@[expose] public section

namespace QED.Graded

/-- (G₂′) **A grading of a vertex sequence `κ`** (ruling S1, provisional: a decoration over the
frozen `Wick.VertexKind`, as flavours were added in Stage 0): the level `k` of each counterterm
vertex, so that its coefficient is the level-`k` coefficient `e^{2(k+1)} d k` of (G₀). The
interaction Lagrangian `L₁` has one counterterm term of each kind for every level, so a sequence
of graded vertex kinds is exactly a pair `(κ, g)`. -/
abbrev Grading {N : ℕ} (κ : Fin N → Wick.VertexKind) : Type :=
  CtVertex κ → ℕ

end QED.Graded

end
