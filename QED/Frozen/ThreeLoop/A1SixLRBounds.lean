-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.A1SixLR
public import QED.Provider.ThreeLoop.A1SixLRBounds

@[expose] public section

namespace QED.ThreeLoop

/-- (R₂) **`A₁⁽⁶⁾` of Laporta–Remiddi to sixteen significant digits** (decision D-54.2): the
constant (R₁) lies strictly between `1.1812414565871995` and `1.1812414565872003`, consistent with
the published value `1.181 241 456 587 …` (Laporta–Remiddi 1996, eq. (5); Passera 2007, eq. (14))
and with a 40-digit evaluation `1.181 241 456 587 200 006 2 …`. -/
theorem a1SixLR_bounds : 1.1812414565871995 < a1SixLR ∧ a1SixLR < 1.1812414565872003 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.ThreeLoop.a1SixLR_bounds
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.ThreeLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
