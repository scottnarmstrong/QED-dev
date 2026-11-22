/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9RemA1
public import QED.ThreeLoopD.SetDMastersI9Wire

/-!
# Set (d), master `I₉`: the expansion of `Rem` from the value of `∫ F₂`

`QED.ThreeLoopD.hasTruncLaurent_i9Rem_integrals` gives `Rem = ε ∫ F₁ + ε² ∫ F₂ + O(ε³)` and
`QED.ThreeLoopD.integral_i9RemF1_value` gives `∫ F₁ = -π²/2 - 9 ζ(3)`. Hence the target
expansion `QED.ThreeLoopD.i9RemLaurent` of `Rem` follows from the value
`∫ F₂ = -17π²/2 + 33 ζ(3) - 73π⁴/60 + 24π² log 2` alone.

## Main results

* `QED.ThreeLoopD.hasTruncLaurent_i9Rem_of_F2`.
-/

@[expose] public section

open MeasureTheory Set Real QED.Polylog

namespace QED.ThreeLoopD

/-- **The expansion of `Rem` from `∫ F₂`.** -/
theorem hasTruncLaurent_i9Rem_of_F2
    (h2 : ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), i9RemF2 z =
      -17 / 2 * π ^ 2 + 33 * zeta3 - 73 / 60 * π ^ 4 + 24 * π ^ 2 * Real.log 2) :
    HasTruncLaurent i9Rem i9RemLaurent 3 := by
  have h := hasTruncLaurent_i9Rem_integrals
  rw [integral_i9RemF1_value, h2] at h
  convert h using 1
  funext ε
  unfold i9RemLaurent
  push_cast
  ring

end QED.ThreeLoopD
