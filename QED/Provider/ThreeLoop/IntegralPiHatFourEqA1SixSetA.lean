/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.PiHatFour
public import QED.Frozen.ThreeLoop.A1SixSetA
import QED.Chain.SetAValue

/-!
# Provider for `QED.ThreeLoop.integral_piHatFour_eq_a1SixSetA`

Proves the frozen theorem goal (A₇) (Phase 5 Stage 3a/3b packet, decision D-58) as
`QED.Provider.ThreeLoop.integral_piHatFour_eq_a1SixSetA`, with the binder convention of decision
D-13 (no binders): the frozen Källén–Sabry function and constant (A₂) are the helper ones
`QED.Chain.piHat4` and `QED.Chain.aSetA` by unfolding, and the identity is the helper theorem
`QED.Chain.integral_setA_eq_aSetA`. This module must never import the frozen anchor.
-/

public section

namespace QED.Provider.ThreeLoop

/-- (A₇) (decision D-13 convention; no binders). -/
theorem integral_piHatFour_eq_a1SixSetA :
    ∫ x in (0 : ℝ)..1, (1 - x) * QED.ThreeLoop.piHatFour (x ^ 2 / (1 - x)) =
      QED.ThreeLoop.a1SixSetA :=
  QED.Chain.integral_setA_eq_aSetA

end QED.Provider.ThreeLoop

end
