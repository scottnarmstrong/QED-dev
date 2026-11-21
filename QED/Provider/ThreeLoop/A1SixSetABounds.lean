/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.A1SixSetA
import QED.Chain.SetAConst

/-!
# Provider for `QED.ThreeLoop.a1SixSetA_bounds`

Proves the frozen theorem goal (A₃) (Phase 5 Stage 3a/3b packet, decision D-58) as
`QED.Provider.ThreeLoop.a1SixSetA_bounds`: the frozen constant (A₂) is the helper constant
`QED.Chain.aSetA` by unfolding, whose enclosure `QED.Chain.aSetA_bounds` is proved from
kernel-checked bounds on `π`, `ln 2`, `ζ(3)` and `Li₄(1/2)`. This module must never import the
frozen anchor.
-/

public section

namespace QED.Provider.ThreeLoop

/-- (A₃) (decision D-13 convention; no binders). The frozen constant (A₂) unfolds to the helper
constant `QED.Chain.aSetA`. -/
theorem a1SixSetA_bounds :
    0.05287065247 < QED.ThreeLoop.a1SixSetA ∧ QED.ThreeLoop.a1SixSetA < 0.05287065248 :=
  QED.Chain.aSetA_bounds

end QED.Provider.ThreeLoop

end
