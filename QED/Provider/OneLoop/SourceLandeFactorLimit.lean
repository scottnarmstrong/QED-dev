/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.SourceMagneticMoment
public import QED.Frozen.OneLoop.IsChargeNormalized
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Support
import QED.Frozen.OneLoop.SourceMagneticMomentLimit
import QED.OneLoop.SourceLandeFactor

/-!
# Provider for `QED.OneLoop.landeFactor_sourceMagneticMoment_limit`

Proves packet 4b's headline goal (W₅) (decision D-18) as
`QED.Provider.OneLoop.landeFactor_sourceMagneticMoment_limit`, with the binder convention of
decision D-13. This module must never import the frozen anchor (W₅).

It applies `QED.OneLoop.landeFactor_sourceMagneticMoment_limit_of_tendsto`, which consumes the
sealed theorems (R) and (R′), to the packet limit given by the sealed theorem (W₄)
`QED.OneLoop.integrable_and_tendsto_sourceMagneticMoment`.
-/

@[expose] public section

open scoped ContDiff
open QED.OneLoop

namespace QED.Provider.OneLoop

/-- Packet 4b's (W₅), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem landeFactor_sourceMagneticMoment_limit {e m : ℝ} (he : e ≠ 0 := by assumption)
    (hm : 0 < m := by assumption) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ := by assumption)
    (hφc : HasCompactSupport φ := by assumption) (hφ0 : ∃ t, 0 ≤ t ∧ φ t ≠ 0 := by assumption)
    {η : ℝ} (hη : 0 < η := by assumption) :
    ∃ δ > 0, ∃ R : ℝ, ∀ (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ), mγ < δ → R < Λ →
      (∃ Z₁ : ℝ, IsChargeNormalized e Z₁ m mγ Λ hm hmγ hΛ) ∧
      ∀ Z₁ : ℝ, IsChargeNormalized e Z₁ m mγ Λ hm hmγ hΛ →
        ∃ lam₀ > 0, ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          ‖4 * (m : ℂ) * sourceMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ φ lam / e
            - 2 * (1 + e ^ 2 / (8 * Real.pi ^ 2))‖ < η :=
  landeFactor_sourceMagneticMoment_limit_of_tendsto e m he hm φ η hη
    fun Z₁ mγ Λ hmγ hΛ μ hμ =>
      (QED.OneLoop.integrable_and_tendsto_sourceMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ φ hφ hφc
        hφ0).2 μ hμ

end QED.Provider.OneLoop

end
