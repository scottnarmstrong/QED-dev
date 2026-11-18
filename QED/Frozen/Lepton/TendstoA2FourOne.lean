-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.A2Four
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import QED.Provider.Lepton.TendstoA2FourOne

@[expose] public section

open Filter Topology

namespace QED.Lepton

/-- (U₃′) **The equal-mass limit** (Passera p. 2, after eq. (10): "for `x = 1`, eq. (10) gives
`A₂⁽⁴⁾(1) = 119/36 - π²/3`"): as `y → 1⁻`, `A₂⁽⁴⁾(y)` tends to the vacuum-polarization part of
`A₁⁽⁴⁾` (BMR-II (1.10); `QED.TwoLoop.VPUnit.integral_vpUnit`). A check of the transcription
that does not depend on the mass ratios. -/
theorem tendsto_a2Four_one :
    Tendsto a2Four (𝓝[<] 1) (𝓝 (119 / 36 - Real.pi ^ 2 / 3)) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Lepton.tendsto_a2Four_one
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Lepton

end
-- FROZEN_ANCHOR_SUFFIX_END
