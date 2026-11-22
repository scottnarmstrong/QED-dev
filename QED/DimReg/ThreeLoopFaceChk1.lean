/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopFaceJobs

/-!
# Pieces 1, 2, 3 of the sector check of `G₇` (generated)

Kernel checks of `QED.DimReg.ThreeLoop.chkJob` on the pieces of
`QED.DimReg.ThreeLoopFaceJobs`.
-/

public section

namespace QED.DimReg.ThreeLoop

/-- Check 1 passes (898 leaves). -/
theorem faceChk1 : faceJobs1.all (fun x => chkJob x.1 x.2) = true := by
  decide +kernel

/-- Check 2 passes (919 leaves). -/
theorem faceChk2 : faceJobs2.all (fun x => chkJob x.1 x.2) = true := by
  decide +kernel

/-- Check 3 passes (892 leaves). -/
theorem faceChk3 : faceJobs3.all (fun x => chkJob x.1 x.2) = true := by
  decide +kernel

end QED.DimReg.ThreeLoop
