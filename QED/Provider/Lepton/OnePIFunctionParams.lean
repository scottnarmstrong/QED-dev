/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.OnePIFunction
public import QED.Frozen.TwoLoop.OnePIFunction
import QED.LeptonProof.CoeffParams

/-!
# Provider for `QED.Lepton.onePIFunction₂_params`

Proves the frozen theorem goal `QED.Lepton.onePIFunction₂_params` (Phase 5 Stage 0 packet, decision
D-50) as `QED.Provider.Lepton.onePIFunction₂_params`, with the binder convention of decision D-13,
from the helper in `QED.LeptonProof.CoeffParams`. This module must never import the frozen anchor.
-/

public section

namespace QED.Provider.Lepton

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem onePIFunction₂_params {P : QED.WickModel.Params} :
    QED.Lepton.onePIFunction₂ P ⟨P.mass, P.loopCoeff, 0⟩ = QED.WickModel.onePIFunction₂ P :=
  QED.Lepton.Proof.onePIFunction₂_params' P

end QED.Provider.Lepton

end
