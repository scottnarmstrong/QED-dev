-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.A1Four
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import QED.Provider.TwoLoop.A1FourBounds

@[expose] public section

namespace QED.TwoLoop

/-- (U₂) **A₁⁽⁴⁾ to four decimal places** (packet T2 theorem goal): the constant (U₁) lies
strictly between `-0.3285` and `-0.3284`, consistent with the published value
`-0.328 478 965 579 …` (Passera (2007) eq. (9)). A check of the transcription of (U₁): every
slip in a coefficient of (U₁) moves the value by at least `10⁻³`. -/
theorem a1Four_bounds : -0.3285 < a1Four ∧ a1Four < -0.3284 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.TwoLoop.a1Four_bounds
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.TwoLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
