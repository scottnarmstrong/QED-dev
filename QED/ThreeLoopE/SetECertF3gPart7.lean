/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetECertF3gData6

/-!
# The `f3g` reduction of set (e): part checks 7-7

Each part of the label split of the `f3g` certificate cancels at `x₀`, checked by `decide +kernel`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert.Sector

theorem f3gPart7 :
    partOk f3gCtx f3gDen (rGetL (chunks f3gTargetL f3gTarget) 7)
      (rGetL (chunks f3gMsL f3gMs) 7) f3gBlocks 7 = true := by
  decide +kernel

end QED.ThreeLoopE.SetECert
