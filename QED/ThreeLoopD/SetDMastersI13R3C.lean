/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13R3B

/-!
# Set (d), master `I₁₃`: the third coefficients of the integrands of `Rem`

With `λ = log t` and the bubble coefficients `β₁, β₂, β₃` (`QED.ThreeLoopD.i13BubR_three`), the
third Taylor coefficients of the integrands of `Rem` are

  `p₃ = t (2β₃ + 2β₁β₂ - λ (2β₂ + β₁²) + λ² β₁ - λ³/6)` on `(0, 1)`

(`QED.ThreeLoopD.i13Dsl_remInt1_three`) and `p₃ - a₃` on `(1, ∞)`, where `a₃`
(`QED.ThreeLoopD.i13A3r`, from `G₃ = -2ζ(3)`) is a polynomial in `t, 1/t, λ` with the elementary
primitive `A₃` (`QED.ThreeLoopD.i13Prim3`), `A₃(1) = 1523/16 - 17π²/4 - 10ζ(3)`.

## Main results

* `QED.ThreeLoopD.i13Dsl_remInt1_three`, `QED.ThreeLoopD.i13Dsl_remInt2_three`.
* `QED.ThreeLoopD.hasDerivAt_i13Prim3`, `QED.ThreeLoopD.i13Prim3_one`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-- `p₃(t) = t (2β₃ + 2β₁β₂ - λ (2β₂ + β₁²) + λ² β₁ - λ³/6)`, `λ = log t`. -/
noncomputable def i13P3 (t : ℝ) : ℝ :=
  t * (2 * i13Be3r t + 2 * i13Be1r t * i13Be2r t -
    Real.log t * (2 * i13Be2r t + i13Be1r t ^ 2) + Real.log t ^ 2 * i13Be1r t -
    Real.log t ^ 3 / 6)

/-- The third coefficient `a₃` of the large-`t` subtraction. -/
noncomputable def i13A3r (t : ℝ) : ℝ :=
  Real.log t ^ 3 * (-9 * t / 2 - 38 / 3 + 14 / (3 * t)) +
    Real.log t ^ 2 * (18 * t + 12 - 56 / t) +
    Real.log t * (π ^ 2 * t + 8 * π ^ 2 / 3 - 4 * π ^ 2 / (3 * t) - 36 * t + 8 + 30 / t) -
    4 * π ^ 2 * t / 3 - 2 * π ^ 2 / 3 + 13 * π ^ 2 / (3 * t) - 4 * t * zeta3 + 32 * t -
    8 * zeta3 - 28 + 8 * zeta3 / t + 43 / (2 * t)

theorem i13GC_three : i13GC 3 = -2 * (zeta3 : ℂ) := i13GC_eq 3 (by norm_num)

theorem i13R1C_three (t : ℝ) :
    i13R1C t 3 = t * (2 * i13BubC t 3 + 2 * i13BubC t 1 * i13BubC t 2) -
      t * (Real.log t : ℂ) * (2 * i13BubC t 2 + i13BubC t 1 ^ 2) +
      t * (Real.log t : ℂ) ^ 2 * i13BubC t 1 - t * (Real.log t : ℂ) ^ 3 / 6 := by
  simp only [i13R1C, i13Cauchy, i13TpC, Finset.sum_range_succ, Finset.sum_range_zero,
    i13BubC_zero, Complex.cpow_one]
  norm_num [i13BubC_zero, Nat.factorial]
  ring

theorem i13AsymC_three {t : ℝ} (ht : 0 < t) : i13AsymC t 3 = (i13A3r t : ℂ) := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  simp only [i13AsymC, i13A0C, i13A1C, i13A2C, i13B0C, i13B1C, i13Cauchy, i13TpC,
    Finset.sum_range_succ, Finset.sum_range_zero, i13GC_zero, i13GC_one, i13GC_two, i13GC_three,
    Complex.cpow_one, Complex.cpow_zero, Complex.cpow_neg_one]
  unfold i13A3r
  norm_num [i13GC_zero, i13GC_one, i13GC_two, i13GC_three, Nat.factorial]
  field_simp
  ring

theorem i13BubC_three {t : ℝ} (ht : 0 < t) : i13BubC t 3 = (i13Be3r t : ℂ) := by
  rw [i13BubC_eq_bubR, i13BubR_three ht]

theorem i13Dsl_remInt1_three {t : ℝ} (ht : 0 < t) :
    i13Dsl (i13RemInt1 t) 3 0 = (i13P3 t : ℂ) := by
  rw [i13Dsl_remInt1 ht, i13R1C_three, i13BubC_one ht, i13BubC_two ht, i13BubC_three ht]
  unfold i13P3
  push_cast
  ring

theorem i13Dsl_remInt2_three {t : ℝ} (ht : 0 < t) :
    i13Dsl (i13RemInt2 t) 3 0 = ((i13P3 t - i13A3r t : ℝ) : ℂ) := by
  rw [i13Dsl_remInt2 ht, i13R1C_three, i13BubC_one ht, i13BubC_two ht, i13BubC_three ht,
    i13AsymC_three ht]
  unfold i13P3
  push_cast
  ring

/-! ### The primitive of `a₃` -/

/-- The primitive `A₃` of `a₃`, a polynomial in `t` and `log t`. -/
noncomputable def i13Prim3 (t : ℝ) : ℝ :=
    (-9 / 4) * (t ^ 2 * Real.log t ^ 3) + (99 / 8) * (t ^ 2 * Real.log t ^ 2) + (-243 / 8 +
    π ^ 2 / 2) * (t ^ 2 * Real.log t) + (499 / 16 - 2 * zeta3 - 11 / 12 * π ^ 2) * (t ^ 2) +
    (-38 / 3) * (t * Real.log t ^ 3) + (50) * (t * Real.log t ^ 2) + (-92 +
    8 / 3 * π ^ 2) * (t * Real.log t) + (64 - 8 * zeta3 - 10 / 3 * π ^ 2) * (t) +
    (7 / 6) * (Real.log t ^ 4) + (-56 / 3) * (Real.log t ^ 3) + (15 -
    2 / 3 * π ^ 2) * (Real.log t ^ 2) + (43 / 2 + 8 * zeta3 + 13 / 3 * π ^ 2) * (Real.log t)

theorem hasDerivAt_i13Prim3 {t : ℝ} (ht : 0 < t) : HasDerivAt i13Prim3 (i13A3r t) t := by
  have L := Real.hasDerivAt_log ht.ne'
  have X := hasDerivAt_id' t
  have e := ((((((((((((((X.pow 2).mul (L.pow 3)).const_mul (-9 / 4)).add (((X.pow 2).mul (L.pow
    2)).const_mul (99 / 8))).add (((X.pow 2).mul L).const_mul (-243 / 8 +
    π ^ 2 / 2))).add (((X.pow 2)).const_mul (499 / 16 - 2 * zeta3 -
    11 / 12 * π ^ 2))).add ((X.mul (L.pow 3)).const_mul (-38 / 3))).add ((X.mul (L.pow 2)).const_mul
    (50))).add ((X.mul L).const_mul (-92 + 8 / 3 * π ^ 2))).add ((X).const_mul (64 - 8 * zeta3 -
    10 / 3 * π ^ 2))).add (((L.pow 4)).const_mul (7 / 6))).add (((L.pow 3)).const_mul (-56 /
    3))).add (((L.pow 2)).const_mul (15 - 2 / 3 * π ^ 2))).add ((L).const_mul (43 / 2 +
    8 * zeta3 + 13 / 3 * π ^ 2)))
  unfold i13Prim3
  refine e.congr_deriv ?_
  unfold i13A3r
  simp only [Pi.pow_apply]
  field_simp
  ring

theorem i13Prim3_one : i13Prim3 1 = 1523 / 16 - 17 * π ^ 2 / 4 - 10 * zeta3 := by
  unfold i13Prim3
  norm_num
  ring

end QED.ThreeLoopD
