/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetECertF3hData2

/-!
# The `f3h` reduction of set (e): part checks 0-0

Each part of the label split of the `f3h` certificate cancels at `x₀`, checked by `decide +kernel`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert.Sector

theorem f3hPart0 :
    partOk f3hCtx f3hDen (rGetL (chunks f3hTargetL f3hTarget) 0)
      (rGetL (chunks f3hMsL f3hMs) 0) f3hBlocks 0 = true := by
  decide +kernel

end QED.ThreeLoopE.SetECert
