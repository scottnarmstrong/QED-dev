-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.A1SixSetD
public import QED.Provider.ThreeLoop.A1SixSetDBounds

@[expose] public section

namespace QED.ThreeLoop

/-- (Sd₃) **`A₁⁽⁶⁾(d)` to fourteen significant digits**: the constant (Sd₂) lies strictly between
`0.37100529210722` and `0.37100529210723`, consistent with the published value `0.371005293`
(Jegerlehner–Nyffeler eq. (82)) and a 50-digit evaluation `0.371 005 292 107 220 840 821 1 …`. -/
theorem a1SixSetD_bounds : 0.37100529210722 < a1SixSetD ∧ a1SixSetD < 0.37100529210723 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.ThreeLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
