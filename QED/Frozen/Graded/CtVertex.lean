/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.VertexKind
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace QED.Graded

/-- (G₂) The counterterm vertices of `κ`: the vertices of kind `gaugeCt`, `fermionCt` or
`photonCt` of (V₀). -/
abbrev CtVertex {N : ℕ} (κ : Fin N → Wick.VertexKind) : Type :=
  {t : Fin N // κ t ≠ .gauge}

end QED.Graded

end
