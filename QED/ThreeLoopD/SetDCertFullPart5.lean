/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDCertFullAll

/-!
# The set (d) reduction: part checks 5-5

Each part of the label split of the set (d) certificate cancels at `x₀`,
checked by `decide +kernel`.
-/

@[expose] public section

namespace QED.ThreeLoopD.SetDCertFull

open QED.Algebra.IBPCert.Sector

theorem sdPart5 : partOk sdCtx sdDen (rGetL (chunks sdTargetL sdTarget) 5)
    (rGetL (chunks sdMsL sdMs) 5) sdBlocks 5 = true := by
  decide +kernel

end QED.ThreeLoopD.SetDCertFull
