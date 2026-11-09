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

/-- (V₂) The number of photon fields `A` of a vertex. Every vertex except `photonCt` has exactly
one `Ψ̄` and one `Ψ`; `photonCt` has none. -/
def VertexKind.photonSlots : VertexKind → ℕ
  | .gauge => 1
  | .gaugeCt => 1
  | .fermionCt => 0
  | .photonCt => 2

end QED.Wick

end
