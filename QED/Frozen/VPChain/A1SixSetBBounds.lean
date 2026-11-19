-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.VPChain.A1SixSetB
public import QED.Provider.VPChain.A1SixSetBBounds

@[expose] public section

namespace QED.VPChain

/-- (C₆) **`A₁⁽⁶⁾(b)` to five significant digits** (obligation O3-14; the analogue of (U₂)): the
constant (C₅) lies strictly between `0.00255852` and `0.00255853`, consistent with the value
`0.002 558 524 936 5 …` of the chain integral (numerics, plan section 9). A check of the
transcription of (C₅): changing any numerator or denominator in it by one moves the value by
more than `10⁻³`. -/
theorem a1SixSetB_bounds : 0.00255852 < a1SixSetB ∧ a1SixSetB < 0.00255853 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.VPChain.a1SixSetB_bounds
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.VPChain

end
-- FROZEN_ANCHOR_SUFFIX_END
