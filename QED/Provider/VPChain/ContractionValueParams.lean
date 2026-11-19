/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.ContractionValue
public import QED.Frozen.TwoLoop.ContractionValue
import QED.ChainProof.QuickMeaning

/-!
# Provider for `QED.VPChain.contractionValue₂_params`

Proves the frozen theorem goal `QED.VPChain.contractionValue₂_params` (Phase 5 Stage 1a packet,
decision D-53) as `QED.Provider.VPChain.contractionValue₂_params`, with the binder convention of
decision D-13, from the helper in `QED.ChainProof.QuickMeaning`. This module must never import the
frozen anchor.
-/

public section

open QED.WickModel (Params Contraction)
open QED.Lepton (contractionValue₂)

namespace QED.Provider.VPChain

open QED.VPChain

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem contractionValue₂_params {P : Params} {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    {C : Contraction nf nA κ} :
    contractionValue₂ P ⟨P.mass, P.loopCoeff, 0⟩ C = QED.WickModel.contractionValue₂ P C :=
  QED.ChainProof.contractionValue₂_params' P C

end QED.Provider.VPChain

end
