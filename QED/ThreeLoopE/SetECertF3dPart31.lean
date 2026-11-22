/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetECertF3dData59

/-!
# The `f3d` reduction of set (e): part checks 31-31

Each part of the label split of the `f3d` certificate cancels at `x₀`, checked by `decide +kernel`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert.Sector

theorem f3dPart31 :
    partOk f3dCtx f3dDen (rGetL (chunks f3dTargetL f3dTarget) 31)
      (rGetL (chunks f3dMsL f3dMs) 31) f3dBlocks 31 = true := by
  decide +kernel

end QED.ThreeLoopE.SetECert
