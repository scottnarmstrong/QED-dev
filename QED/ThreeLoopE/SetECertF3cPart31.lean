/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetECertF3cAll

/-!
# The `f3c` reduction of set (e): part checks 31-31

Each part of the label split of the `f3c` certificate cancels at `x₀`, checked by `decide +kernel`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert.Sector

theorem f3cPart31 : partOk f3cCtx f3cDen (rGetL (chunks f3cTargetL f3cTarget) 31)
    (rGetL (chunks f3cMastersL f3cMasters) 31) f3cBlocks 31 = true := by
  decide +kernel

end QED.ThreeLoopE.SetECert
