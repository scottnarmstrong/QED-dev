-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.A1SixSetC
public import QED.Provider.ThreeLoop.A1SixSetCBounds

@[expose] public section

namespace QED.ThreeLoop

/-- (Sc₅) **The set (c) constant to eleven decimals** (decision D-49.3):
`-0.15017228210 < A₁⁽⁶⁾(c) < -0.15017228209`. -/
theorem a1SixSetC_bounds : -0.15017228210 < a1SixSetC ∧ a1SixSetC < -0.15017228209 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.ThreeLoop.a1SixSetC_bounds
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.ThreeLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
