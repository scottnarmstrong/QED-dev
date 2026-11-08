-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.IsResponseMagneticMoment
public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.Provider.OneLoop.LandeFactorLimit

@[expose] public section

open Matrix Complex

namespace QED.OneLoop

/-- (R′) **The one-loop Landé factor (packet 4a headline goal).** For `e ≠ 0` and `m > 0`, with the
counterterm fixed by the charge condition (K₀), the Landé factor `g = 4 m μ / e` of (64.16) of the
response magnetic moment (R₀) tends to `2 (1 + e²/(8π²))`, the one-loop value `2 (1 + α/(2π))` of
(64.17), jointly as `m_γ → 0⁺` and `Λ → ∞`. The vertex function (J) is truncated at order `e³`, so
the limit is exact for that model, with no `O(α²)` term. Near the limit a charge-normalized
counterterm and a magnetic moment exist, and every such pair gives `g` within `η` of the limit. The
response definition takes `q → 0⁺` at fixed regulators, before the regulator limit, as in decision
D-5. -/
theorem landeFactor_isResponseMagneticMoment_limit (e m : ℝ) (he : e ≠ 0) (hm : 0 < m) (η : ℝ)
    (hη : 0 < η) :
    ∃ δ > 0, ∃ R : ℝ, ∀ (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ), mγ < δ → R < Λ →
      (∃ Z₁ μ : ℝ, IsChargeNormalized e Z₁ m mγ Λ hm hmγ hΛ ∧
        IsResponseMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ μ) ∧
      ∀ Z₁ μ : ℝ, IsChargeNormalized e Z₁ m mγ Λ hm hmγ hΛ →
        IsResponseMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ μ →
        |4 * m * μ / e - 2 * (1 + e ^ 2 / (8 * Real.pi ^ 2))| < η :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.OneLoop.landeFactor_isResponseMagneticMoment_limit
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.OneLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
