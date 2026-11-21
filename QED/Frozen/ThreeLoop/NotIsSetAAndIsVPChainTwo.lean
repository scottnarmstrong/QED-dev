-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetA
public import QED.Frozen.VPChain.IsVPChain
public import QED.Provider.ThreeLoop.NotIsSetAAndIsVPChainTwo

@[expose] public section

open QED.WickModel (Contraction)

namespace QED.ThreeLoop

/-- (MA₂) **Set (a) and set (b) are disjoint** (meaning theorem): no contraction is both in (A₁)
and a two-insertion chain (C₁). A chain has a photon line between its two insertions, so its
photon walk from `a` meets two insertions; (A₁) allows one. -/
theorem not_isSetA_and_isVPChain_two {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction 1 1 κ) : ¬ (IsSetA C ∧ VPChain.IsVPChain 2 C) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.ThreeLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
