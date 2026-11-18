/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.VertexOrderFive
public import QED.Frozen.TwoLoop.VertexOrderFive
import QED.LeptonProof.CoeffParams

/-!
# Provider for `QED.Lepton.vertexOrderFive_params`

Proves the frozen theorem goal `QED.Lepton.vertexOrderFive_params` (Phase 5 Stage 0 packet, decision
D-50) as `QED.Provider.Lepton.vertexOrderFive_params`, with the binder convention of decision D-13,
from the helper in `QED.LeptonProof.CoeffParams`. This module must never import the frozen anchor.
-/

public section

namespace QED.Provider.Lepton

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem vertexOrderFive_params {P : QED.WickModel.Params} :
    QED.Lepton.vertexOrderFive P ⟨P.mass, P.loopCoeff, 0⟩ = QED.TwoLoop.vertexOrderFive P :=
  QED.Lepton.Proof.vertexOrderFive_params' P

end QED.Provider.Lepton

end
