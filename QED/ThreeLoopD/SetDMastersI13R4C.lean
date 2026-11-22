/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13R4B

/-!
# Set (d), master `I₁₃`: the fourth coefficients of the integrands of `Rem`

With `λ = log t` and the bubble coefficients `β₁, …, β₄` (`QED.ThreeLoopD.i13BubR_four`), the
fourth Taylor coefficients of the integrands of `Rem` are

  `p₄ = t (2β₄ + 2β₁β₃ + β₂² - λ (2β₃ + 2β₁β₂) + λ² (β₂ + β₁²/2) - λ³ β₁/3 + λ⁴/24)`

on `(0, 1)` (`QED.ThreeLoopD.i13Dsl_remInt1_four`) and `p₄ - a₄` on `(1, ∞)`, where `a₄`
(`QED.ThreeLoopD.i13A4r`, from `G₄ = -π⁴/40`) is a polynomial in `t, 1/t, λ` with the elementary
primitive `A₄` (`QED.ThreeLoopD.i13Prim4`), `A₄(1) = 13273/32 - 139π²/8 - 51ζ(3)`.

## Main results

* `QED.ThreeLoopD.i13Dsl_remInt1_four`, `QED.ThreeLoopD.i13Dsl_remInt2_four`.
* `QED.ThreeLoopD.hasDerivAt_i13Prim4`, `QED.ThreeLoopD.i13Prim4_one`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-- `p₄(t) = t (2β₄ + 2β₁β₃ + β₂² - λ (2β₃ + 2β₁β₂) + λ² (β₂ + β₁²/2) - λ³ β₁/3 + λ⁴/24)`. -/
noncomputable def i13P4 (t : ℝ) : ℝ :=
  t * (2 * i13Be4r t + 2 * i13Be1r t * i13Be3r t + i13Be2r t ^ 2 -
    Real.log t * (2 * i13Be3r t + 2 * i13Be1r t * i13Be2r t) +
    Real.log t ^ 2 * (i13Be2r t + i13Be1r t ^ 2 / 2) - Real.log t ^ 3 * i13Be1r t / 3 +
    Real.log t ^ 4 / 24)

/-- The fourth coefficient `a₄` of the large-`t` subtraction. -/
noncomputable def i13A4r (t : ℝ) : ℝ :=
    Real.log t ^ 4 * ((27 / 8) * t + (65 / 6) + (-5 / 2) / t) +
    Real.log t ^ 3 * ((-18) * t + (-20) + (188 / 3) / t) +
    Real.log t ^ 2 * ((54 - 3 / 2 * π ^ 2) * t + (16 - 14 / 3 * π ^ 2) + (-84 +
      4 / 3 * π ^ 2) / t) +
    Real.log t * ((-96 + 4 * π ^ 2 + 12 * zeta3) * t + (24 + 4 * π ^ 2 + 32 * zeta3) + (37 -
      16 * zeta3 - 14 * π ^ 2) / t) +
    ((80 - 16 * zeta3 - 4 * π ^ 2 - π ^ 4 / 45) * t + (-60 - 8 * zeta3 - 2 / 3 * π ^ 2 +
      π ^ 4 / 90) + (187 / 4 + 52 * zeta3 + π ^ 4 / 10 + 37 / 6 * π ^ 2) / t)

theorem i13GC_four : i13GC 4 = -1 / 40 * (π : ℂ) ^ 4 := i13GC_eq 4 (by norm_num)

theorem i13R1C_four (t : ℝ) :
    i13R1C t 4 = t * (2 * i13BubC t 4 + 2 * i13BubC t 1 * i13BubC t 3 + i13BubC t 2 ^ 2) -
      t * (Real.log t : ℂ) * (2 * i13BubC t 3 + 2 * i13BubC t 1 * i13BubC t 2) +
      t * (Real.log t : ℂ) ^ 2 * (i13BubC t 2 + i13BubC t 1 ^ 2 / 2) -
      t * (Real.log t : ℂ) ^ 3 * i13BubC t 1 / 3 + t * (Real.log t : ℂ) ^ 4 / 24 := by
  simp only [i13R1C, i13Cauchy, i13TpC, Finset.sum_range_succ, Finset.sum_range_zero,
    i13BubC_zero, Complex.cpow_one]
  norm_num [i13BubC_zero, Nat.factorial]
  ring

theorem i13AsymC_four {t : ℝ} (ht : 0 < t) : i13AsymC t 4 = (i13A4r t : ℂ) := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  simp only [i13AsymC, i13A0C, i13A1C, i13A2C, i13B0C, i13B1C, i13Cauchy, i13TpC,
    Finset.sum_range_succ, Finset.sum_range_zero, i13GC_zero, i13GC_one, i13GC_two, i13GC_three,
    i13GC_four, Complex.cpow_one, Complex.cpow_zero, Complex.cpow_neg_one]
  unfold i13A4r
  norm_num [i13GC_zero, i13GC_one, i13GC_two, i13GC_three, i13GC_four, Nat.factorial]
  field_simp
  ring

theorem i13BubC_four {t : ℝ} (ht : 0 < t) : i13BubC t 4 = (i13Be4r t : ℂ) := by
  rw [i13BubC_eq_bubR, i13BubR_four ht]

theorem i13Dsl_remInt1_four {t : ℝ} (ht : 0 < t) :
    i13Dsl (i13RemInt1 t) 4 0 = (i13P4 t : ℂ) := by
  rw [i13Dsl_remInt1 ht, i13R1C_four, i13BubC_one ht, i13BubC_two ht, i13BubC_three ht,
    i13BubC_four ht]
  unfold i13P4
  push_cast
  ring

theorem i13Dsl_remInt2_four {t : ℝ} (ht : 0 < t) :
    i13Dsl (i13RemInt2 t) 4 0 = ((i13P4 t - i13A4r t : ℝ) : ℂ) := by
  rw [i13Dsl_remInt2 ht, i13R1C_four, i13BubC_one ht, i13BubC_two ht, i13BubC_three ht,
    i13BubC_four ht, i13AsymC_four ht]
  unfold i13P4
  push_cast
  ring

/-! ### The primitive of `a₄` -/

/-- The primitive `A₄` of `a₄`, a polynomial in `t` and `log t`. -/
noncomputable def i13Prim4 (t : ℝ) : ℝ :=
    (27 / 16) * (t ^ 2 * Real.log t ^ 4) + (-99 / 8) * (t ^ 2 * Real.log t ^ 3) + (729 / 16 -
    3 / 4 * π ^ 2) * (t ^ 2 * Real.log t ^ 2) + (-1497 / 16 + 6 * zeta3 +
    11 / 4 * π ^ 2) * (t ^ 2 * Real.log t) + (2777 / 32 - 11 * zeta3 - 27 / 8 * π ^ 2 -
    π ^ 4 / 90) * (t ^ 2) + (65 / 6) * (t * Real.log t ^ 4) +
    (-190 / 3) * (t * Real.log t ^ 3) + (206 - 14 / 3 * π ^ 2) * (t * Real.log t ^ 2) + (-388 +
    32 * zeta3 + 40 / 3 * π ^ 2) * (t * Real.log t) + (328 - 40 * zeta3 - 14 * π ^ 2 +
    π ^ 4 / 90) * (t) + (-1 / 2) * (Real.log t ^ 5) + (47 / 3) * (Real.log t ^ 4) + (-28 +
    4 / 9 * π ^ 2) * (Real.log t ^ 3) + (37 / 2 - 8 * zeta3 - 7 * π ^ 2) * (Real.log t ^ 2) +
    (187 / 4 + 52 * zeta3 + π ^ 4 / 10 + 37 / 6 * π ^ 2) * (Real.log t)

theorem hasDerivAt_i13Prim4 {t : ℝ} (ht : 0 < t) : HasDerivAt i13Prim4 (i13A4r t) t := by
  have L := Real.hasDerivAt_log ht.ne'
  have X := hasDerivAt_id' t
  have e := (((((((((((((((((X.pow 2).mul (L.pow 4)).const_mul (27 / 16)).add (((X.pow 2).mul (L.pow
    3)).const_mul (-99 / 8))).add (((X.pow 2).mul (L.pow 2)).const_mul (729 / 16 -
    3 / 4 * π ^ 2))).add (((X.pow 2).mul L).const_mul (-1497 / 16 + 6 * zeta3 +
    11 / 4 * π ^ 2))).add (((X.pow 2)).const_mul (2777 / 32 - 11 * zeta3 - 27 / 8 * π ^ 2 -
    π ^ 4 / 90))).add ((X.mul (L.pow 4)).const_mul (65 / 6))).add ((X.mul (L.pow 3)).const_mul (-190
    / 3))).add ((X.mul (L.pow 2)).const_mul (206 -
    14 / 3 * π ^ 2))).add ((X.mul L).const_mul (-388 + 32 * zeta3 +
    40 / 3 * π ^ 2))).add ((X).const_mul (328 - 40 * zeta3 - 14 * π ^ 2 +
    π ^ 4 / 90))).add (((L.pow 5)).const_mul (-1 / 2))).add (((L.pow 4)).const_mul (47 / 3))).add
    (((L.pow 3)).const_mul (-28 + 4 / 9 * π ^ 2))).add (((L.pow 2)).const_mul (37 / 2 -
    8 * zeta3 - 7 * π ^ 2))).add ((L).const_mul (187 / 4 + 52 * zeta3 + π ^ 4 / 10 +
    37 / 6 * π ^ 2)))
  unfold i13Prim4
  refine e.congr_deriv ?_
  unfold i13A4r
  simp only [Pi.pow_apply]
  field_simp
  ring

theorem i13Prim4_one : i13Prim4 1 = 13273 / 32 - 139 * π ^ 2 / 8 - 51 * zeta3 := by
  unfold i13Prim4
  norm_num
  ring

end QED.ThreeLoopD
