/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopFaceJobs

/-!
# Pieces 10, 11, 12 of the sector check of `G₇` (generated)

Kernel checks of `QED.DimReg.ThreeLoop.chkJob` on the pieces of
`QED.DimReg.ThreeLoopFaceJobs`.
-/

public section

namespace QED.DimReg.ThreeLoop

/-- Check 10 passes (614 leaves). -/
theorem faceChk10 : faceJobs10.all (fun x => chkJob x.1 x.2) = true := by
  decide +kernel

/-- Check 11 passes (502 leaves). -/
theorem faceChk11 : faceJobs11.all (fun x => chkJob x.1 x.2) = true := by
  decide +kernel

/-- Check 12 passes (304 leaves). -/
theorem faceChk12 : faceJobs12.all (fun x => chkJob x.1 x.2) = true := by
  decide +kernel

end QED.DimReg.ThreeLoop
