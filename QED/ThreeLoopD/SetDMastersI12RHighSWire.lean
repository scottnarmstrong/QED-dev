/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighSGoodVal
public import QED.ThreeLoopD.SetDMastersI12RHighTValThree
public import QED.ThreeLoopD.SetDMastersI12RHighTValFour
public import QED.ThreeLoopD.SetDMastersI12RestWire

/-!
# Set (d), master `I₁₂`: the coefficients `r₃`, `r₄` reduced to the bad part of the bulk

By `QED.ThreeLoopD.iteratedDeriv_succ_i12Rest_eq_reg` and the split
`QED.ThreeLoopD.integral_i12HSW_split`,

  `i12Rest⁽ⁿ⁺¹⁾(0) = (n + 1) (∫ D₁ⁿ + ∫ Good_n + rest_n) + T_A⁽ⁿ⁺¹⁾(0) + T_B⁽ⁿ⁺¹⁾(0)`,

`rest_n = ∫_{Reg} (W_n - Good_n) - ∫_{(0,1) × (0,∞) × (0,1) \ Reg} Good_n`
(`QED.ThreeLoopD.i12HSRest`). The face terms are known in closed form
(`QED.ThreeLoopD.iteratedDeriv_i12TA_add_i12TB_three`,
`QED.ThreeLoopD.iteratedDeriv_i12TA_add_i12TB_four`) and so is the good part
(`QED.ThreeLoopD.integral_i12HSGoodDn_two`, `QED.ThreeLoopD.integral_i12HSGoodDn_three`). Hence
the set (d) identities `r₃ = i12Rest⁽³⁾(0)/3!`, `r₄ = i12Rest⁽⁴⁾(0)/4!` (hypotheses `h3`, `h4`
of `QED.ThreeLoopD.hasTruncLaurent_i12Rest_of_coeffs`) are each equivalent to one identity for
the bad part `Bad_n = (∫ D₁ⁿ + rest_n)/n!` of the bulk remainder:

  `Bad₂ = r₃ - T₃ - Good₂`, `Bad₃ = r₄ - T₄ - Good₃`,

with the explicit right sides `QED.ThreeLoopD.i12HSBad2 = -72.7060576576…` and
`QED.ThreeLoopD.i12HSBad3 = 136.163829062…` (`QED.ThreeLoopD.i12Rest_coeff_three_of_bad`,
`QED.ThreeLoopD.i12Rest_coeff_four_of_bad`). Both values agree with the independent numerical
evaluation of the bad part from its decomposition (to `1e-14` relative at order `3`).

## Main results

* `QED.ThreeLoopD.i12Rest_coeff_three_of_bad`, `QED.ThreeLoopD.i12Rest_coeff_four_of_bad`.
-/

@[expose] public section

open Complex Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- The rest of the bulk part at order `n`:
`∫_{Reg} (W_n - Good_n) - ∫_{(0,1) × (0,∞) × (0,1) \ Reg} Good_n`. -/
noncomputable def i12HSRest (n : ℕ) : ℝ :=
  (∫ z in i12HSReg, (i12HSW n z.1 z.2.1 z.2.2 - i12HSGoodDn n z.1 z.2.1 z.2.2)) -
    ∫ z in (Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1)) \ i12HSReg,
      i12HSGoodDn n z.1 z.2.1 z.2.2

/-- The target value of the bad part at order `2`: `r₃ - T₃ - Good₂`. -/
noncomputable def i12HSBad2 : ℝ :=
  -2 / 3 * Real.log 2 ^ 4 + 2 * Real.log 2 ^ 3 - 16 / 3 * Real.log 2 ^ 2 * Real.pi ^ 2
    - 17 * Real.log 2 ^ 2 + 23 / 12 * Real.log 2 * Real.pi ^ 2 + 36 * Real.log 2 * zeta3
    + 12 * Real.log 2 + 23 / 60 * Real.pi ^ 4 - 563 / 12 * Real.pi ^ 2 + 11 * zeta3
    + 36 * Li 4 (1 / 2) + 65377 / 216

/-- The target value of the bad part at order `3`: `r₄ - T₄ - Good₃`. -/
noncomputable def i12HSBad3 : ℝ :=
  -41 / 10 * Real.log 2 ^ 5 - 13 / 6 * Real.log 2 ^ 4 + 119 / 18 * Real.log 2 ^ 3 * Real.pi ^ 2
    + 7 * Real.log 2 ^ 3 - 5 / 24 * Real.log 2 ^ 2 * Real.pi ^ 2
    - 149 / 2 * Real.log 2 ^ 2 * zeta3 - 29 * Real.log 2 ^ 2
    + 169 / 120 * Real.log 2 * Real.pi ^ 4 + 1553 / 3 * Real.log 2 * Real.pi ^ 2
    - 63 / 4 * Real.log 2 * zeta3 - 144 * Real.log 2 * Li 4 (1 / 2) + 18 * Real.log 2
    - 553 / 480 * Real.pi ^ 4 + 209 / 12 * Real.pi ^ 2 * zeta3 - 8125 / 24 * Real.pi ^ 2
    - 13207 / 12 * zeta3 - 687 / 2 * zeta5 - 18 * Li 4 (1 / 2) - 108 * Li 5 (1 / 2)
    + 2044115 / 1296

/-- `i12Rest⁽ⁿ⁺¹⁾(0)` in terms of `∫ D₁ⁿ`, `∫ Good_n`, `rest_n` and the face terms. -/
theorem iteratedDeriv_succ_i12Rest_eq_rest (n : ℕ) :
    iteratedDeriv (n + 1) i12Rest 0 =
      (n + 1) * ((∫ z in i12Cube, (i12R1Dn n z.1 z.2.1 z.2.2 : ℂ)) +
        (((∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1),
          i12HSGoodDn n z.1 z.2.1 z.2.2) + i12HSRest n : ℝ) : ℂ)) +
      (iteratedDeriv (n + 1) i12TA 0 + iteratedDeriv (n + 1) i12TB 0) := by
  rw [iteratedDeriv_succ_i12Rest_eq_reg, (integral_i12HSW_split n).2.2,
    (iteratedDeriv_i12TA_eq_integral (n + 1)).2, (iteratedDeriv_i12TB_eq_integral (n + 1)).2,
    i12HSRest]
  ring

/-- **`r₃` from the bad part**: if `∫ D₁² + rest₂ = 2 Bad₂` then `i12Rest⁽³⁾(0)/3! = r₃`. -/
theorem i12Rest_coeff_three_of_bad
    (h : (∫ z in i12Cube, (i12R1Dn 2 z.1 z.2.1 z.2.2 : ℂ)) + (i12HSRest 2 : ℂ) =
      2 * (i12HSBad2 : ℂ)) :
    iteratedDeriv 3 i12Rest 0 / (3 : ℕ).factorial = i12RestR3 := by
  have e : iteratedDeriv 3 i12Rest 0 = _ := iteratedDeriv_succ_i12Rest_eq_rest 2
  rw [e, iteratedDeriv_i12TA_add_i12TB_three, integral_i12HSGoodDn_two]
  push_cast
  rw [show (∫ z in i12Cube, (i12R1Dn 2 z.1 z.2.1 z.2.2 : ℂ)) =
    2 * (i12HSBad2 : ℂ) - (i12HSRest 2 : ℂ) by rw [← h]; ring]
  simp only [i12HSBad2, i12HSGood2, i12RestR3, Nat.factorial]
  push_cast
  ring

/-- **`r₄` from the bad part**: if `∫ D₁³ + rest₃ = 6 Bad₃` then `i12Rest⁽⁴⁾(0)/4! = r₄`. -/
theorem i12Rest_coeff_four_of_bad
    (h : (∫ z in i12Cube, (i12R1Dn 3 z.1 z.2.1 z.2.2 : ℂ)) + (i12HSRest 3 : ℂ) =
      6 * (i12HSBad3 : ℂ)) :
    iteratedDeriv 4 i12Rest 0 / (4 : ℕ).factorial = i12RestR4 := by
  have e : iteratedDeriv 4 i12Rest 0 = _ := iteratedDeriv_succ_i12Rest_eq_rest 3
  rw [e, iteratedDeriv_i12TA_add_i12TB_four, integral_i12HSGoodDn_three]
  push_cast
  rw [show (∫ z in i12Cube, (i12R1Dn 3 z.1 z.2.1 z.2.2 : ℂ)) =
    6 * (i12HSBad3 : ℂ) - (i12HSRest 3 : ℂ) by rw [← h]; ring]
  simp only [i12HSBad3, i12HSGood3, i12RestR4, Nat.factorial]
  push_cast
  ring

end QED.ThreeLoopD
