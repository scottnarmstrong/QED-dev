/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetA
public import QED.Frozen.VPChain.IsVPChain
import QED.ChainProof.SetALinkDisjoint

/-!
# Provider for `QED.ThreeLoop.not_isSetA_and_isVPChain_two`

Proves the frozen theorem goal (MA₂) (Phase 5 Stage 3a/3b packet, decision D-58) as
`QED.Provider.ThreeLoop.not_isSetA_and_isVPChain_two`, with the binder convention of decision
D-13, from `QED.ChainProof.SetALink.not_isSetA_and_isVPChain_two'`
(`QED/ChainProof/SetALinkDisjoint.lean`). This module must never import the frozen anchor.
-/

public section

open QED.WickModel (Contraction)

namespace QED.Provider.ThreeLoop

/-- (MA₂), with implicit data binders (decision D-13; no hypotheses). -/
theorem not_isSetA_and_isVPChain_two {N : ℕ} {κ : Fin N → Wick.VertexKind}
    {C : Contraction 1 1 κ} : ¬ (QED.ThreeLoop.IsSetA C ∧ VPChain.IsVPChain 2 C) :=
  QED.ChainProof.SetALink.not_isSetA_and_isVPChain_two' C

end QED.Provider.ThreeLoop

end
