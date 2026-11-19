/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.VPChain.IsVPChain
public import QED.Frozen.WickModel.IsOnePI
public import QED.Frozen.TwoLoop.LoopCount
import QED.ChainProof.QuickRep

/-!
# Provider for `QED.VPChain.exists_isVPChain_two`

Proves the frozen theorem goal `QED.VPChain.exists_isVPChain_two` (Phase 5 Stage 1a packet, decision
D-53) as `QED.Provider.VPChain.exists_isVPChain_two`, with the binder convention of decision D-13,
from the helper in `QED.ChainProof.QuickRep`. This module must never import the frozen anchor.
-/

public section

open QED.WickModel (Contraction IsOnePI loopCount)

namespace QED.Provider.VPChain

open QED.VPChain

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem exists_isVPChain_two :
    ∃ C : Contraction 1 1 (fun _ : Fin 7 => Wick.VertexKind.gauge),
      IsOnePI C ∧ IsVPChain 2 C ∧ loopCount C = 3 :=
  QED.ChainProof.exists_isVPChain_two'

end QED.Provider.VPChain

end
