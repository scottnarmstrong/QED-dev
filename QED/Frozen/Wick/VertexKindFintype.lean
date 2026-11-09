/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.VertexKind
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace QED.Wick

/-- (V₀′) The four vertex kinds form a finite type. -/
instance VertexKind.instFintype : Fintype VertexKind :=
  ⟨{.gauge, .gaugeCt, .fermionCt, .photonCt}, fun x => by cases x <;> simp⟩

end QED.Wick

end
