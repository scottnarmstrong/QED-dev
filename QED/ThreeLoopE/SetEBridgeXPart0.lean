/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEBridgeXAll

/-!
# The `f3c` reduction of the sector-92 numerators: part checks 0-0

Each part of the label split of the `f3c` certificate cancels at `x₀`, checked by `decide +kernel`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert.Sector

theorem f3cXPart0 : partOk f3cXCtx f3cXDen (rGetL (chunks f3cXTargetL f3cXTarget) 0)
    (rGetL (chunks f3cXMastersL f3cXMasters) 0) f3cXBlocks 0 = true := by
  decide +kernel

end QED.ThreeLoopE.SetECert
