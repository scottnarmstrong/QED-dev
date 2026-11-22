/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDCertFullAll

/-!
# The set (d) reduction: part checks 7-7

Each part of the label split of the set (d) certificate cancels at `x₀`,
checked by `decide +kernel`.
-/

@[expose] public section

namespace QED.ThreeLoopD.SetDCertFull

open QED.Algebra.IBPCert.Sector

theorem sdPart7 : partOk sdCtx sdDen (rGetL (chunks sdTargetL sdTarget) 7)
    (rGetL (chunks sdMsL sdMs) 7) sdBlocks 7 = true := by
  decide +kernel

end QED.ThreeLoopD.SetDCertFull
