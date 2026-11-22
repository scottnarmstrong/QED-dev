/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetECertF3iData23

/-!
# The `f3i` reduction of set (e): part checks 9-9

Each part of the label split of the `f3i` certificate cancels at `x₀`, checked by `decide +kernel`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert.Sector

theorem f3iPart9 :
    partOk f3iCtx f3iDen (rGetL (chunks f3iTargetL f3iTarget) 9)
      (rGetL (chunks f3iMsL f3iMs) 9) f3iBlocks 9 = true := by
  decide +kernel

end QED.ThreeLoopE.SetECert
