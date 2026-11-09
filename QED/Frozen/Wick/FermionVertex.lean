/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.VertexKind
public import Mathlib.Data.Nat.Notation

@[expose] public section

namespace QED.Wick

/-- (V₃) The vertices of a labelled vertex sequence `κ` that carry a `Ψ̄ Ψ` pair. -/
abbrev FermionVertex {N : ℕ} (κ : Fin N → VertexKind) : Type :=
  {t : Fin N // κ t ≠ .photonCt}

end QED.Wick

end
