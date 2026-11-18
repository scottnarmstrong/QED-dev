/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.IsVertexOrderFiveLimit
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Frozen.TwoLoop.IsVertexOrderFiveLimit
import QED.LeptonProof.EmbedRelabel

/-!
# Provider for `QED.Lepton.isVertexOrderFiveLimit_leptonFlavors_zero_iff`

Proves the frozen theorem goal `QED.Lepton.isVertexOrderFiveLimit_leptonFlavors_zero_iff` (Phase 5
Stage 0 packet, decision D-50) as
`QED.Provider.Lepton.isVertexOrderFiveLimit_leptonFlavors_zero_iff`, with the binder convention of
decision D-13, from the helper in `QED.LeptonProof.EmbedRelabel`. This module must never import the
frozen anchor.
-/

public section

namespace QED.Provider.Lepton

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem isVertexOrderFiveLimit_leptonFlavors_zero_iff {P : QED.WickModel.Params}
    {H : Fin 0 → QED.Lepton.HeavyLepton} {p' p : Fin 4 → ℝ} {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} :
    QED.Lepton.IsVertexOrderFiveLimit P (QED.Lepton.leptonFlavors P H) p' p V ↔
      QED.TwoLoop.IsVertexOrderFiveLimit P p' p V :=
  QED.Lepton.Proof.isVertexOrderFiveLimit_leptonFlavors_zero_iff' P H p' p V

end QED.Provider.Lepton

end
