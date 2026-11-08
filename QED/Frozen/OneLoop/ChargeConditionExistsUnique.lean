-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.Provider.OneLoop.ChargeConditionExistsUnique

@[expose] public section

open Matrix Complex

namespace QED.OneLoop

/-- (K) **The charge condition fixes the counterterm (packet 3 theorem goal).** For `e ≠ 0`,
`m > 0`, and regulators `m_γ, Λ > 0`, exactly one real `Z₁` satisfies the charge condition (K₀). -/
theorem existsUnique_isChargeNormalized (e m mγ Λ : ℝ) (he : e ≠ 0) (hm : 0 < m) (hmγ : 0 < mγ)
    (hΛ : 0 < Λ) : ∃! Z₁ : ℝ, IsChargeNormalized e Z₁ m mγ Λ hm hmγ hΛ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.OneLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
