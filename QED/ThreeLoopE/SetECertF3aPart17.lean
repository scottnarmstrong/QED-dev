/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetECertF3aData26

/-!
# The `f3a` reduction of set (e): part checks 17-17

Each part of the label split of the `f3a` certificate cancels at `x₀`, checked by `decide +kernel`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert.Sector

theorem f3aPart17 :
    partOk f3aCtx f3aDen (rGetL (chunks f3aTargetL f3aTarget) 17)
      (rGetL (chunks f3aMsL f3aMs) 17) f3aBlocks 17 = true := by
  decide +kernel

end QED.ThreeLoopE.SetECert
