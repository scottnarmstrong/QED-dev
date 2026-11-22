/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegXPartialFractions

/-!
# The divided differences in the crossed engine order

In each numerator term, first split the spectral line against the original
light element. A remaining equal mass at the element can be split against
the native Pauli–Villars partner after exchanging the base labels.
-/

public section

namespace QED.ChainProof.SetCRegX

/-- The divided differences obtained by splitting the spectral line first
give the same coefficient action as the recurrence in
`QED/ChainProof/SetCRegXPartialFractions.lean`. -/
theorem bubbleDividedDifference_eq_nativeOrder {a b c : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (fa fb fc da db : ℝ) :
    let D := massDividedDifference
    let ab := D a b fa fb
    let bc := D b c fb fc
    let aa := -da
    let bb := -db
    let aba := D b a ab aa
    let cba := D c a bc ab
    let abb := D a b ab bb
    let cbb := D c b bc bb
    let bba := D b a bb ab
    let abab := D a b aba bba
    let cbab := D c b cba bba
    bubbleDividedDifference a b c fa fb fc da db =
      D a c ab bc - a * D a c aba cba - b * D a c abb cbb + a * b * D a c abab cbab := by
  simp only [bubbleDividedDifference, massDividedDifference]
  rw [show a - b = -(b - a) by ring, show a - c = -(c - a) by ring,
    show b - c = -(c - b) by ring]
  field_simp [sub_ne_zero.mpr hab.symm, sub_ne_zero.mpr hac.symm, sub_ne_zero.mpr hbc.symm]
  ring

end QED.ChainProof.SetCRegX

end
