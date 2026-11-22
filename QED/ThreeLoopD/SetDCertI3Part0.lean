/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDCertI3All

/-!
# The set (d) dotted integral: part checks 0-0

Each part of the label split of the set (d) certificate cancels at `x₀`,
checked by `decide +kernel`.
-/

@[expose] public section

namespace QED.ThreeLoopD.SetDCertI3

open QED.Algebra.IBPCert.Sector

theorem sdPart0 : partOk sdCtx sdDen (rGetL (chunks sdTargetL sdTarget) 0)
    (rGetL (chunks sdMsL sdMs) 0) sdBlocks 0 = true := by
  decide +kernel

end QED.ThreeLoopD.SetDCertI3
