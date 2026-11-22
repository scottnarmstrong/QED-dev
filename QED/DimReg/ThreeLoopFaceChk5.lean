/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopFaceJobs

/-!
# Pieces 13, 14, 15 of the sector check of `G₇` (generated)

Kernel checks of `QED.DimReg.ThreeLoop.chkJob` on the pieces of
`QED.DimReg.ThreeLoopFaceJobs`.
-/

public section

namespace QED.DimReg.ThreeLoop

/-- Check 13 passes (182 leaves). -/
theorem faceChk13 : faceJobs13.all (fun x => chkJob x.1 x.2) = true := by
  decide +kernel

/-- Check 14 passes (96 leaves). -/
theorem faceChk14 : faceJobs14.all (fun x => chkJob x.1 x.2) = true := by
  decide +kernel

/-- Check 15 passes (20 leaves). -/
theorem faceChk15 : faceJobs15.all (fun x => chkJob x.1 x.2) = true := by
  decide +kernel

end QED.DimReg.ThreeLoop
