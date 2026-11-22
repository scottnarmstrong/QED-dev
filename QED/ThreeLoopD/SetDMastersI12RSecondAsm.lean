/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondD
public import QED.ThreeLoopD.SetDMastersI12RSecondDeriv
public import QED.ThreeLoopD.SetDMastersI12RSecondGood
public import QED.ThreeLoopD.SetDMastersI12RestWire

/-!
# Set (d), master `I₁₂`: the second Taylor coefficient of the remainder, assembled

By `QED.ThreeLoopD.iteratedDeriv_two_i12Rest_eq`,
`i12Rest''(0) / 2 = R₁'(0) + R_A'(0) + R_B'(0) + (T_A''(0) + T_B''(0)) / 2`. With
`R_A'(0) + R_B'(0) = Good + B₃ᵇ` (`QED.ThreeLoopD.deriv_i12RA3_add_deriv_i12RB3`) and
`R₁'(0) + B₃ᵇ = D` (`QED.ThreeLoopD.deriv_i12R1_add_i12B3bad_eq_of_E`), the coefficient is
`Good + D + (T_A''(0) + T_B''(0)) / 2`. This file reduces `r2` to its two remaining inputs: the
closed form of `E` and the value

  `T_A''(0) + T_B''(0) = 2 (-36 + 15π²/4 + 6ℓ + 9ℓ² + 3π²ℓ + 2ℓ³ + 45 ζ(3))`.

## Main results

* `QED.ThreeLoopD.iteratedDeriv_two_i12Rest_of`.
-/

@[expose] public section

open Real Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- **The second Taylor coefficient `r2` of the remainder**, from the closed form of `E` and the
value of `T_A''(0) + T_B''(0)`. -/
theorem iteratedDeriv_two_i12Rest_of
    (hE : ∀ y ∈ Ioc (0 : ℝ) (1 / 2), ∫ x in Ioo (0 : ℝ) 1, i12REx (y * (1 - y)) x = i12REcl y)
    (hT : deriv (deriv i12TA) 0 + deriv (deriv i12TB) 0 =
      ((2 * (-36 + 15 * π ^ 2 / 4 + 6 * log 2 + 9 * log 2 ^ 2 + 3 * π ^ 2 * log 2 +
        2 * log 2 ^ 3 + 45 * zeta3) : ℝ) : ℂ)) :
    iteratedDeriv 2 i12Rest 0 / (2 : ℕ).factorial = i12RestR2 := by
  have hD := deriv_i12R1_add_i12B3bad_eq_of_E hE
  have hG := deriv_i12RA3_add_deriv_i12RB3
  rw [iteratedDeriv_two_i12Rest_eq, hT, i12RestR2]
  push_cast at hD hG ⊢
  linear_combination hD + hG

end QED.ThreeLoopD
