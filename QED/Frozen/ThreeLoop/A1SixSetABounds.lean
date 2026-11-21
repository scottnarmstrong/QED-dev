-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.A1SixSetA
public import QED.Provider.ThreeLoop.A1SixSetABounds

@[expose] public section

namespace QED.ThreeLoop

/-- (A₃) **The set (a) constant to eleven decimals** (decision D-49.3: a companion enclosure for
every exact constant): `0.05287065247 < A₁⁽⁶⁾(a) < 0.05287065248`. -/
theorem a1SixSetA_bounds : 0.05287065247 < a1SixSetA ∧ a1SixSetA < 0.05287065248 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.ThreeLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
