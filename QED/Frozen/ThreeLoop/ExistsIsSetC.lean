-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetC
public import QED.Frozen.WickModel.IsOnePI
public import QED.Frozen.TwoLoop.LoopCount
public import QED.Provider.ThreeLoop.ExistsIsSetC

@[expose] public section

open QED.WickModel (Contraction IsOnePI loopCount)

namespace QED.ThreeLoop

/-- (MC₁) **Set (c) is not empty at three loops** (meaning theorem; the analogue of (M₄)): a 1PI
contraction with seven `gauge` vertices (graded order `7`, no counterterm vertex, so any grading)
satisfies (Sc₃) and has three loops. Expected by `decide +kernel` on the ladder representative with
the bubble on its outer photon. -/
theorem exists_isSetC :
    ∃ C : Contraction 1 1 (fun _ : Fin 7 => Wick.VertexKind.gauge),
      ∀ g : Graded.Grading (fun _ : Fin 7 => Wick.VertexKind.gauge),
        IsOnePI C ∧ IsSetC C g ∧ loopCount C = 3 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.ThreeLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
