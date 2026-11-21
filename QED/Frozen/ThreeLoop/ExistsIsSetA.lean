-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetA
public import QED.Frozen.WickModel.IsOnePI
public import QED.Frozen.TwoLoop.LoopCount
public import QED.Provider.ThreeLoop.ExistsIsSetA

@[expose] public section

open QED.WickModel (Contraction IsOnePI loopCount)

namespace QED.ThreeLoop

/-- (MA₁) **Set (a) is not empty at three loops** (meaning theorem; the analogue of (M₄)): a 1PI
contraction with seven `gauge` vertices (graded order `7`, no counterterm vertex) satisfies (A₁)
and has three loops. Expected by `decide +kernel` on the vertex-type representative. -/
theorem exists_isSetA :
    ∃ C : Contraction 1 1 (fun _ : Fin 7 => Wick.VertexKind.gauge),
      IsOnePI C ∧ IsSetA C ∧ loopCount C = 3 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.ThreeLoop.exists_isSetA
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.ThreeLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
