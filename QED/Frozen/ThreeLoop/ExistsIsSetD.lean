-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetD
public import QED.Frozen.WickModel.IsOnePI
public import QED.Frozen.TwoLoop.LoopCount
public import QED.Provider.ThreeLoop.ExistsIsSetD

@[expose] public section

open QED.WickModel (Contraction IsOnePI loopCount)

namespace QED.ThreeLoop

/-- (MD₁) **Set (d) is not empty at three loops** (meaning theorem; the analogue of (MA₁)): a
contraction with seven `gauge` vertices (graded order `7`, no counterterm vertex) is 1PI,
satisfies (Sd₁), and has three loops. Expected by `decide +kernel` on a representative. -/
theorem exists_isSetD :
    ∃ C : Contraction 1 1 (fun _ : Fin 7 => Wick.VertexKind.gauge),
      IsOnePI C ∧ IsSetD C ∧ loopCount C = 3 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.ThreeLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
