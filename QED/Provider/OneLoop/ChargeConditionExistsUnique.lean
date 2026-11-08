/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.IsChargeNormalized
import QED.OneLoop.ChargeCondition

/-!
# Provider for `QED.OneLoop.existsUnique_isChargeNormalized`

Proves packet 3's theorem goal (K) (decision D-15) as
`QED.Provider.OneLoop.existsUnique_isChargeNormalized`, with the binder convention of decision D-13.
The frozen anchor is sealed with this theorem (2026-11-08).
This module must never import the frozen anchor.
-/

@[expose] public section

open Matrix Complex
open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration
open scoped Real

namespace QED.Provider.OneLoop

/-- Packet 3's (K), with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem existsUnique_isChargeNormalized {e m mγ Λ : ℝ} (he : e ≠ 0 := by assumption)
    (hm : 0 < m := by assumption) (hmγ : 0 < mγ := by assumption)
    (hΛ : 0 < Λ := by assumption) : ∃! Z₁ : ℝ, IsChargeNormalized e Z₁ m mγ Λ hm hmγ hΛ :=
  ⟨_, isChargeNormalized_chargeZ hm hmγ hΛ,
    fun _ hZ => eq_chargeZ_of_isChargeNormalized he hm hmγ hΛ hZ⟩

end QED.Provider.OneLoop

end
