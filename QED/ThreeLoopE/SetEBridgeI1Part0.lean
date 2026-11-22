/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEBridgeI1All

/-!
# The `f3c` reduction of the numerator integral `2 I₁`: part checks 0-7

Each part of the label split of the `f3c` certificate cancels at `x₀`, checked by `decide +kernel`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert.Sector

theorem f3cI1Part0 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 0)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 0) f3cI1Blocks 0 = true := by
  decide +kernel

theorem f3cI1Part1 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 1)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 1) f3cI1Blocks 1 = true := by
  decide +kernel

theorem f3cI1Part2 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 2)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 2) f3cI1Blocks 2 = true := by
  decide +kernel

theorem f3cI1Part3 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 3)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 3) f3cI1Blocks 3 = true := by
  decide +kernel

theorem f3cI1Part4 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 4)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 4) f3cI1Blocks 4 = true := by
  decide +kernel

theorem f3cI1Part5 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 5)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 5) f3cI1Blocks 5 = true := by
  decide +kernel

theorem f3cI1Part6 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 6)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 6) f3cI1Blocks 6 = true := by
  decide +kernel

theorem f3cI1Part7 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 7)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 7) f3cI1Blocks 7 = true := by
  decide +kernel

end QED.ThreeLoopE.SetECert
