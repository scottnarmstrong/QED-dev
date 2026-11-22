/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopFaceJobs

/-!
# Pieces 7, 8, 9 of the sector check of `G₇` (generated)

Kernel checks of `QED.DimReg.ThreeLoop.chkJob` on the pieces of
`QED.DimReg.ThreeLoopFaceJobs`.
-/

public section

namespace QED.DimReg.ThreeLoop

/-- Check 7 passes (891 leaves). -/
theorem faceChk7 : faceJobs7.all (fun x => chkJob x.1 x.2) = true := by
  decide +kernel

/-- Check 8 passes (895 leaves). -/
theorem faceChk8 : faceJobs8.all (fun x => chkJob x.1 x.2) = true := by
  decide +kernel

/-- Check 9 passes (775 leaves). -/
theorem faceChk9 : faceJobs9.all (fun x => chkJob x.1 x.2) = true := by
  decide +kernel

end QED.DimReg.ThreeLoop
