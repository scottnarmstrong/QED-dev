/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.OnePIFunction
public import QED.Frozen.WickModel.OnePIFunction
import QED.LeptonProof.EmbedOneZero

/-!
# Provider for `QED.Lepton.onePIFunction₂_one_zero`

Proves the frozen theorem goal `QED.Lepton.onePIFunction₂_one_zero` (Phase 5 Stage 0 packet,
decision D-50) as `QED.Provider.Lepton.onePIFunction₂_one_zero`, with the binder convention of
decision D-13, from the helper in `QED.LeptonProof.EmbedOneZero`. This module must never import the
frozen anchor.
-/

public section

namespace QED.Provider.Lepton

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem onePIFunction₂_one_zero {P : QED.WickModel.Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : QED.Lepton.Flavors F} (hΦ : Φ.mass Φ.openLine = P.m := by assumption) {K : ℕ}
    (hK : K ≤ 3 := by assumption) :
    QED.Lepton.onePIFunction₂ P Φ 1 0 K = QED.WickModel.onePIFunction P 1 0 K :=
  QED.Lepton.Proof.onePIFunction₂_one_zero' P Φ hΦ hK

end QED.Provider.Lepton

end
