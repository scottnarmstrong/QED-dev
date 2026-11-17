/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.IsElectronOnShell
public import QED.Frozen.OneLoop.IsChargeNormalized
import QED.TwoLoop.WardIdentity

/-!
# Provider for `QED.WickModel.δ₁_eq_δ₂`

Proves the frozen theorem goal (WI₁) of packet T4 (decision D-40) as
`QED.Provider.TwoLoop.δ₁_eq_δ₂`, with the binder convention of decision D-13, from the Ward
identity on the parametric closed forms (`QED.TwoLoop.Ward.δ₁_eq_δ₂_of_isChargeNormalized`).
This module must never import the frozen anchor.
-/

@[expose] public section

namespace QED.Provider.TwoLoop

open QED.WickModel in
/-- Packet T4's (WI₁), with an implicit data binder and `by assumption` hypotheses
(decision D-13). -/
theorem δ₁_eq_δ₂ {P : Params} (he : P.e ≠ 0 := by assumption) (hm : 0 < P.m := by assumption)
    (hmγ : 0 < P.mγ := by assumption) (hΛ : 0 < P.Λ := by assumption)
    (hon : IsElectronOnShell P hm hmγ hΛ := by assumption)
    (hK : QED.OneLoop.IsChargeNormalized P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ :=
      by assumption) :
    P.δ₁ = P.δ₂ :=
  QED.TwoLoop.Ward.δ₁_eq_δ₂_of_isChargeNormalized P he hm hmγ hΛ hon hK

end QED.Provider.TwoLoop

end
