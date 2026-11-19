/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.A1SixLR
import QED.Polylog.A1Six

/-!
# Provider for `QED.ThreeLoop.a1SixLR_bounds`

Proves the frozen theorem goal (R₂) (decision D-54) as `QED.Provider.ThreeLoop.a1SixLR_bounds`:
the frozen constant (R₁) is the helper constant `QED.Polylog.a1SixLR` by unfolding, whose
enclosure `QED.Polylog.a1SixLR_bounds_fine` is proved from kernel-checked bounds on `π`, `ln 2`,
`ζ(3)`, `ζ(5)` and `Li₄(1/2)`. This module must never import the frozen anchor.
-/

public section

namespace QED.Provider.ThreeLoop

/-- (R₂) (decision D-13 convention; no binders). The frozen constant (R₁) unfolds to the helper
constant `QED.Polylog.a1SixLR`. -/
theorem a1SixLR_bounds :
    1.1812414565871995 < QED.ThreeLoop.a1SixLR ∧ QED.ThreeLoop.a1SixLR < 1.1812414565872003 := by
  have e : QED.ThreeLoop.a1SixLR = QED.Polylog.a1SixLR := by
    unfold QED.ThreeLoop.a1SixLR QED.Polylog.a1SixLR QED.Polylog.Li QED.Polylog.zeta3
      QED.Polylog.zeta5
    rfl
  exact e ▸ QED.Polylog.a1SixLR_bounds_fine

end QED.Provider.ThreeLoop

end
