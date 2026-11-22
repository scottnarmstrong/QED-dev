/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEBridgeI1All

/-!
# The `f3c` reduction of the numerator integral `2 I₁`: part checks 8-15

Each part of the label split of the `f3c` certificate cancels at `x₀`, checked by `decide +kernel`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert.Sector

theorem f3cI1Part8 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 8)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 8) f3cI1Blocks 8 = true := by
  decide +kernel

theorem f3cI1Part9 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 9)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 9) f3cI1Blocks 9 = true := by
  decide +kernel

theorem f3cI1Part10 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 10)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 10) f3cI1Blocks 10 = true := by
  decide +kernel

theorem f3cI1Part11 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 11)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 11) f3cI1Blocks 11 = true := by
  decide +kernel

theorem f3cI1Part12 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 12)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 12) f3cI1Blocks 12 = true := by
  decide +kernel

theorem f3cI1Part13 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 13)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 13) f3cI1Blocks 13 = true := by
  decide +kernel

theorem f3cI1Part14 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 14)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 14) f3cI1Blocks 14 = true := by
  decide +kernel

theorem f3cI1Part15 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 15)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 15) f3cI1Blocks 15 = true := by
  decide +kernel

end QED.ThreeLoopE.SetECert
