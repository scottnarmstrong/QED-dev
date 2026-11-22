/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetC
public import QED.Frozen.ThreeLoop.IsSetA
public import QED.Frozen.VPChain.IsVPChain
public import QED.Frozen.Graded.GradedOrder
import QED.ChainProof.SetCLinkDisjoint

/-!
# Provider for `QED.ThreeLoop.isSetC_disjoint`

Proves the frozen theorem goal (MC₂) (Phase 5 Stage 3a/3b packet, decision D-58) as
`QED.Provider.ThreeLoop.isSetC_disjoint`, with the binder convention of decision D-13, from
`QED.ChainProof.SetCLink.isSetC_disjoint` (`QED/ChainProof/SetCLinkDisjoint.lean`). This module
must never import the frozen anchor.
-/

public section

open QED.WickModel (Contraction)

namespace QED.Provider.ThreeLoop

/-- (MC₂), with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem isSetC_disjoint {N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 1 1 κ}
    {g : Graded.Grading κ} (hg : Graded.gradedOrder κ g = 7 := by assumption) :
    ¬ (QED.ThreeLoop.IsSetC C g ∧ QED.ThreeLoop.IsSetA C) ∧
      ¬ (QED.ThreeLoop.IsSetC C g ∧ VPChain.IsVPChain 2 C) :=
  QED.ChainProof.SetCLink.isSetC_disjoint C g hg

end QED.Provider.ThreeLoop

end
