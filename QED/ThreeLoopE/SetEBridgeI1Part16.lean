/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEBridgeI1All

/-!
# The `f3c` reduction of the numerator integral `2 I₁`: part checks 16-23

Each part of the label split of the `f3c` certificate cancels at `x₀`, checked by `decide +kernel`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert.Sector

theorem f3cI1Part16 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 16)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 16) f3cI1Blocks 16 = true := by
  decide +kernel

theorem f3cI1Part17 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 17)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 17) f3cI1Blocks 17 = true := by
  decide +kernel

theorem f3cI1Part18 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 18)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 18) f3cI1Blocks 18 = true := by
  decide +kernel

theorem f3cI1Part19 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 19)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 19) f3cI1Blocks 19 = true := by
  decide +kernel

theorem f3cI1Part20 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 20)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 20) f3cI1Blocks 20 = true := by
  decide +kernel

theorem f3cI1Part21 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 21)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 21) f3cI1Blocks 21 = true := by
  decide +kernel

theorem f3cI1Part22 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 22)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 22) f3cI1Blocks 22 = true := by
  decide +kernel

theorem f3cI1Part23 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 23)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 23) f3cI1Blocks 23 = true := by
  decide +kernel

end QED.ThreeLoopE.SetECert
