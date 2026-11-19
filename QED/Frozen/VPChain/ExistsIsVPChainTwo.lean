-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.VPChain.IsVPChain
public import QED.Frozen.WickModel.IsOnePI
public import QED.Frozen.TwoLoop.LoopCount
public import QED.Provider.VPChain.ExistsIsVPChainTwo

@[expose] public section

open QED.WickModel (Contraction IsOnePI loopCount)

namespace QED.VPChain

/-- (M₄) **Set (b) has a genuine three-loop member** (non-vacuity of (C₁) at `n = 2`): there is a
contraction of seven gauge vertices satisfying (C₁) with `n = 2`, which is 1PI (X₁₈) and has three
loops (T₂): the open line with two bubbles on its photon. Its value (F₇) is therefore a joint
energy-first integral over three loop momenta. -/
theorem exists_isVPChain_two :
    ∃ C : Contraction 1 1 (fun _ : Fin 7 => Wick.VertexKind.gauge),
      IsOnePI C ∧ IsVPChain 2 C ∧ loopCount C = 3 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.VPChain

end
-- FROZEN_ANCHOR_SUFFIX_END
