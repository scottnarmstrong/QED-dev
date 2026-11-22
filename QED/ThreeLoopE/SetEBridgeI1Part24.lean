/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEBridgeI1All

/-!
# The `f3c` reduction of the numerator integral `2 I₁`: part checks 24-31

Each part of the label split of the `f3c` certificate cancels at `x₀`, checked by `decide +kernel`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert.Sector

theorem f3cI1Part24 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 24)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 24) f3cI1Blocks 24 = true := by
  decide +kernel

theorem f3cI1Part25 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 25)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 25) f3cI1Blocks 25 = true := by
  decide +kernel

theorem f3cI1Part26 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 26)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 26) f3cI1Blocks 26 = true := by
  decide +kernel

theorem f3cI1Part27 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 27)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 27) f3cI1Blocks 27 = true := by
  decide +kernel

theorem f3cI1Part28 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 28)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 28) f3cI1Blocks 28 = true := by
  decide +kernel

theorem f3cI1Part29 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 29)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 29) f3cI1Blocks 29 = true := by
  decide +kernel

theorem f3cI1Part30 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 30)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 30) f3cI1Blocks 30 = true := by
  decide +kernel

theorem f3cI1Part31 : partOk f3cI1Ctx f3cI1Den (rGetL (chunks f3cI1TargetL f3cI1Target) 31)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) 31) f3cI1Blocks 31 = true := by
  decide +kernel

end QED.ThreeLoopE.SetECert
