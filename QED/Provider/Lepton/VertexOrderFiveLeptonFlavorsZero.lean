/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.VertexOrderFive
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Frozen.TwoLoop.VertexOrderFive
import QED.LeptonProof.EmbedRelabel

/-!
# Provider for `QED.Lepton.vertexOrderFive_leptonFlavors_zero`

Proves the frozen theorem goal `QED.Lepton.vertexOrderFive_leptonFlavors_zero` (Phase 5 Stage 0
packet, decision D-50) as `QED.Provider.Lepton.vertexOrderFive_leptonFlavors_zero`, with the binder
convention of decision D-13, from the helper in `QED.LeptonProof.EmbedRelabel`. This module must
never import the frozen anchor.
-/

public section

namespace QED.Provider.Lepton

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem vertexOrderFive_leptonFlavors_zero {P : QED.WickModel.Params}
    {H : Fin 0 → QED.Lepton.HeavyLepton} :
    QED.Lepton.vertexOrderFive P (QED.Lepton.leptonFlavors P H) = QED.TwoLoop.vertexOrderFive P :=
  QED.Lepton.Proof.vertexOrderFive_leptonFlavors_zero' P H

end QED.Provider.Lepton

end
