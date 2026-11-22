/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetECertF3bData9

/-!
# The `f3b` reduction of set (e): part checks 1-1

Each part of the label split of the `f3b` certificate cancels at `x₀`, checked by `decide +kernel`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert.Sector

theorem f3bPart1 :
    partOk f3bCtx f3bDen (rGetL (chunks f3bTargetL f3bTarget) 1)
      (rGetL (chunks f3bMsL f3bMs) 1) f3bBlocks 1 = true := by
  decide +kernel

end QED.ThreeLoopE.SetECert
