/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkIntBData

/-!
# Set (c), family `B`: the basis criterion, orbits 6–11

Helper for the Phase 5 Stage 3 goal (HS₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setC`
(decision D-58). Kernel checks of the basis criterion
`QED.ChainProof.SetALinkV.critB (rowsB i) E 5` for the minimal exponent vectors `E ∈ esB i`
(`QED/ChainProof/SetCLinkIntBData.lean`), and the resulting
`QED.ChainProof.SetALinkV.BasisCrit` (`basisCrit_esB6`, …).
-/

@[expose] public section

namespace QED.ChainProof.SetCLink

open QED.ChainProof.SetALinkV

theorem critB_esB6 : ((esB 6).all fun E => critB (rowsB 6) E 5) = true := by
  decide +kernel

theorem basisCrit_esB6 : ∀ E ∈ esB 6, BasisCrit (rowsB 6) E 5 := fun E hE =>
  basisCrit_of_critB (List.all_eq_true.mp critB_esB6 E hE)

theorem critB_esB7 : ((esB 7).all fun E => critB (rowsB 7) E 5) = true := by
  decide +kernel

theorem basisCrit_esB7 : ∀ E ∈ esB 7, BasisCrit (rowsB 7) E 5 := fun E hE =>
  basisCrit_of_critB (List.all_eq_true.mp critB_esB7 E hE)

theorem critB_esB8 : ((esB 8).all fun E => critB (rowsB 8) E 5) = true := by
  decide +kernel

theorem basisCrit_esB8 : ∀ E ∈ esB 8, BasisCrit (rowsB 8) E 5 := fun E hE =>
  basisCrit_of_critB (List.all_eq_true.mp critB_esB8 E hE)

theorem critB_esB9 : ((esB 9).all fun E => critB (rowsB 9) E 5) = true := by
  decide +kernel

theorem basisCrit_esB9 : ∀ E ∈ esB 9, BasisCrit (rowsB 9) E 5 := fun E hE =>
  basisCrit_of_critB (List.all_eq_true.mp critB_esB9 E hE)

theorem critB_esB10 : ((esB 10).all fun E => critB (rowsB 10) E 5) = true := by
  decide +kernel

theorem basisCrit_esB10 : ∀ E ∈ esB 10, BasisCrit (rowsB 10) E 5 := fun E hE =>
  basisCrit_of_critB (List.all_eq_true.mp critB_esB10 E hE)

theorem critB_esB11 : ((esB 11).all fun E => critB (rowsB 11) E 5) = true := by
  decide +kernel

theorem basisCrit_esB11 : ∀ E ∈ esB 11, BasisCrit (rowsB 11) E 5 := fun E hE =>
  basisCrit_of_critB (List.all_eq_true.mp critB_esB11 E hE)

end QED.ChainProof.SetCLink

end
