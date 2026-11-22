/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopFaceJobs

/-!
# Pieces 4, 5, 6 of the sector check of `G₇` (generated)

Kernel checks of `QED.DimReg.ThreeLoop.chkJob` on the pieces of
`QED.DimReg.ThreeLoopFaceJobs`.
-/

public section

namespace QED.DimReg.ThreeLoop

/-- Check 4 passes (930 leaves). -/
theorem faceChk4 : faceJobs4.all (fun x => chkJob x.1 x.2) = true := by
  decide +kernel

/-- Check 5 passes (904 leaves). -/
theorem faceChk5 : faceJobs5.all (fun x => chkJob x.1 x.2) = true := by
  decide +kernel

/-- Check 6 passes (820 leaves). -/
theorem faceChk6 : faceJobs6.all (fun x => chkJob x.1 x.2) = true := by
  decide +kernel

end QED.DimReg.ThreeLoop
