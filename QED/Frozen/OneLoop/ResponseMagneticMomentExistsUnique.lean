-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.IsResponseMagneticMoment
public import QED.Provider.OneLoop.ResponseMagneticMomentExistsUnique

@[expose] public section

open Matrix Complex

namespace QED.OneLoop

/-- (R) **The magnetic moment is well defined (packet 4a theorem goal).** For `m > 0`,
regulators `m_γ, Λ > 0`, and every counterterm `Z₁`, exactly one real `μ` satisfies the response
definition (R₀). -/
theorem existsUnique_isResponseMagneticMoment (e Z₁ m mγ Λ : ℝ) (hm : 0 < m)
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    ∃! μ : ℝ, IsResponseMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ μ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.OneLoop.existsUnique_isResponseMagneticMoment
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.OneLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
