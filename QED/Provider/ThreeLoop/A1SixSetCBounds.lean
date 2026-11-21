/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.A1SixSetC
import QED.Chain.SetCConst

/-!
# Provider for `QED.ThreeLoop.a1SixSetC_bounds`

Proves the frozen theorem goal (Sc₅) (Phase 5 Stage 3a/3b packet, decision D-58) as
`QED.Provider.ThreeLoop.a1SixSetC_bounds`: the frozen constant is the helper constant
`QED.Chain.aSetC` by unfolding, whose enclosure `QED.Chain.aSetC_bounds` is proved from
kernel-checked bounds on its transcendental constants. This module must never import the frozen
anchor.
-/

public section

namespace QED.Provider.ThreeLoop

/-- (Sc₅) (decision D-13 convention; no binders). The frozen constant unfolds to the helper
constant `QED.Chain.aSetC`. -/
theorem a1SixSetC_bounds :
    -0.15017228210 < QED.ThreeLoop.a1SixSetC ∧ QED.ThreeLoop.a1SixSetC < -0.15017228209 :=
  QED.Chain.aSetC_bounds

end QED.Provider.ThreeLoop

end
