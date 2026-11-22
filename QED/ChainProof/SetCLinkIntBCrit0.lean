/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkIntBData

/-!
# Set (c), family `B`: the basis criterion, orbits 0–5

Helper for the Phase 5 Stage 3 goal (HS₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setC`
(decision D-58). Kernel checks of the basis criterion
`QED.ChainProof.SetALinkV.critB (rowsB i) E 5` for the minimal exponent vectors `E ∈ esB i`
(`QED/ChainProof/SetCLinkIntBData.lean`), and the resulting
`QED.ChainProof.SetALinkV.BasisCrit` (`basisCrit_esB0`, …).
-/

@[expose] public section

namespace QED.ChainProof.SetCLink

open QED.ChainProof.SetALinkV

theorem critB_esB0 : ((esB 0).all fun E => critB (rowsB 0) E 5) = true := by
  decide +kernel

theorem basisCrit_esB0 : ∀ E ∈ esB 0, BasisCrit (rowsB 0) E 5 := fun E hE =>
  basisCrit_of_critB (List.all_eq_true.mp critB_esB0 E hE)

theorem critB_esB1 : ((esB 1).all fun E => critB (rowsB 1) E 5) = true := by
  decide +kernel

theorem basisCrit_esB1 : ∀ E ∈ esB 1, BasisCrit (rowsB 1) E 5 := fun E hE =>
  basisCrit_of_critB (List.all_eq_true.mp critB_esB1 E hE)

theorem critB_esB2 : ((esB 2).all fun E => critB (rowsB 2) E 5) = true := by
  decide +kernel

theorem basisCrit_esB2 : ∀ E ∈ esB 2, BasisCrit (rowsB 2) E 5 := fun E hE =>
  basisCrit_of_critB (List.all_eq_true.mp critB_esB2 E hE)

theorem critB_esB3 : ((esB 3).all fun E => critB (rowsB 3) E 5) = true := by
  decide +kernel

theorem basisCrit_esB3 : ∀ E ∈ esB 3, BasisCrit (rowsB 3) E 5 := fun E hE =>
  basisCrit_of_critB (List.all_eq_true.mp critB_esB3 E hE)

theorem critB_esB4 : ((esB 4).all fun E => critB (rowsB 4) E 5) = true := by
  decide +kernel

theorem basisCrit_esB4 : ∀ E ∈ esB 4, BasisCrit (rowsB 4) E 5 := fun E hE =>
  basisCrit_of_critB (List.all_eq_true.mp critB_esB4 E hE)

theorem critB_esB5 : ((esB 5).all fun E => critB (rowsB 5) E 5) = true := by
  decide +kernel

theorem basisCrit_esB5 : ∀ E ∈ esB 5, BasisCrit (rowsB 5) E 5 := fun E hE =>
  basisCrit_of_critB (List.all_eq_true.mp critB_esB5 E hE)

end QED.ChainProof.SetCLink

end
