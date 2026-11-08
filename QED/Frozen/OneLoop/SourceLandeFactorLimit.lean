-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.SourceMagneticMoment
public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.Provider.OneLoop.SourceLandeFactorLimit
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Support

@[expose] public section

open scoped ContDiff

namespace QED.OneLoop

/-- (W₅) **The one-loop Landé factor, source definition (packet 4b headline goal).** For `e ≠ 0`,
`m > 0`, and a profile `φ` as in (W₄), with the counterterm fixed by the charge condition (K₀):
the Landé factor `g = 4 m μ / e` (64.16) of the source magnetic moment (W₃) approaches the
one-loop value `2 (1 + e²/(8π²)) = 2 (1 + α/(2π))` of (64.17). The packet limit `λ → 0⁺` is taken
first at fixed regulators (decision D-17), then `m_γ → 0⁺` and `Λ → ∞` jointly (decision D-5,
ruling D-9). The vertex function (J) is truncated at order `e³`, so the limit is exact for that
model, with no `O(α²)` term. Near the limit a charge-normalized counterterm exists, and for every
such counterterm `g` is within `η` of the limit for all sufficiently narrow packets. -/
theorem landeFactor_sourceMagneticMoment_limit (e m : ℝ) (he : e ≠ 0) (hm : 0 < m)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∃ t, 0 ≤ t ∧ φ t ≠ 0) (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∃ R : ℝ, ∀ (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ), mγ < δ → R < Λ →
      (∃ Z₁ : ℝ, IsChargeNormalized e Z₁ m mγ Λ hm hmγ hΛ) ∧
      ∀ Z₁ : ℝ, IsChargeNormalized e Z₁ m mγ Λ hm hmγ hΛ →
        ∃ lam₀ > 0, ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          ‖4 * (m : ℂ) * sourceMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ φ lam / e
            - 2 * (1 + e ^ 2 / (8 * Real.pi ^ 2))‖ < η :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.OneLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
