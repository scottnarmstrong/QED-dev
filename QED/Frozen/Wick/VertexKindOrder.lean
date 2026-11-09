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

/-- (V₁) The order of a vertex in the charge `e`: the counterterm coefficients `Z_i - 1` count as
order `e²` (decision D-19), so `(Z₁ - 1) e Ψ̄ A̸ Ψ` has order `3`. -/
def VertexKind.order : VertexKind → ℕ
  | .gauge => 1
  | .gaugeCt => 3
  | .fermionCt => 2
  | .photonCt => 2

end QED.Wick

end
