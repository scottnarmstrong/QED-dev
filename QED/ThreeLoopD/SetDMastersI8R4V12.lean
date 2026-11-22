/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4V11

/-!
# Set (d), master `I₈`: continuity and values at `1` of the sub-pieces 156 to 157 of `Ψ₄`

Each sub-piece `Ψ₄⁽ⁿ⁾` is continuous on `(0, 1]` (the words beginning with `1` carry a factor
`1 - ξ`), and its value at `ξ = 1` follows from the values of the harmonic polylogarithms at `1`.

## Main results

* `QED.ThreeLoopD.continuousOn_i8Psi4s156`, `QED.ThreeLoopD.i8Psi4s156_one` and their
  companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- Chunk 0 of `i8Psi4s156` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s156S0 (x : ℝ) : ℝ :=
    (x ^ 4 - 19 / 2 * x ^ 3) / x ^ 2 +
    (x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero] x +
    (-3 / 2 * x ^ 3 + 17 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-x ^ 4 + 2 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (x ^ 3 - x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-2 * x ^ 3 + 8 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-8 * x ^ 2 - 2 * x ^ 4 + 4 * x ^ 3) / x ^ 2 * hpl [zero, one, one] x +
    (-2 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, one] x) +
    (-2 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one, zero] x) +
    (-2 * x ^ 3 + 6 * x ^ 2 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, one, one] x) +
    (-8) * hpl [zero, zero, one, one] x +
    (-8) * hpl [zero, one, zero, one] x +
    (-8) * hpl [zero, one, one, zero] x +
    (-4 * x ^ 4 + 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, one, one, one] x +
    (-4 * x ^ 2 + 4 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, one, one] x) +
    (-4 * x ^ 2 + 4 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, one, zero, one] x) +
    (-4 * x ^ 2 + 4 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, one, one, zero] x) +
    (8) * hpl [zero, zero, one, one, one] x +
    (8) * hpl [zero, one, zero, one, one] x +
    (8) * hpl [zero, one, one, zero, one] x

theorem continuousOn_i8Psi4s156S0 : ContinuousOn i8Psi4s156S0 (Ioc 0 1) := by
  unfold i8Psi4s156S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 - 19 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -3 / 2 * x ^ 3 + 17 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 3 + 8 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 2 - 2 * x ^ 4 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 3 + 6 * x ^ 2 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 4 + 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, one]))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 2 + 4 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one, one]))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 2 + 4 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 2 + 4 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero, one])))

/-- Chunk 1 of `i8Psi4s156` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s156S1 (x : ℝ) : ℝ :=
    (8) * hpl [zero, one, one, one, zero] x

theorem continuousOn_i8Psi4s156S1 : ContinuousOn i8Psi4s156S1 (Ioc 0 1) := by
  unfold i8Psi4s156S1
  exact (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, one, zero]))

theorem i8Psi4s156_eq_S (x : ℝ) : i8Psi4s156 x = i8Psi4s156S0 x + i8Psi4s156S1 x := by
  unfold i8Psi4s156 i8Psi4s156S0 i8Psi4s156S1 i8Psi4s156N0 i8Psi4s156N1 i8Psi4s156N2 i8Psi4s156N3
    i8Psi4s156N4 i8Psi4s156W
  ring

theorem continuousOn_i8Psi4s156 : ContinuousOn i8Psi4s156 (Ioc 0 1) := by
  rw [show i8Psi4s156 = fun x => i8Psi4s156S0 x + i8Psi4s156S1 x from funext i8Psi4s156_eq_S]
  exact (continuousOn_i8Psi4s156S0.add continuousOn_i8Psi4s156S1)

theorem i8Psi4s156_one : i8Psi4s156 1 = -17 / 2 - 16 * zeta5 - 6 * zeta3 + π ^ 2 / 6 +
    7 / 45 * π ^ 4 + 4 / 3 * π ^ 2 * zeta3 := by
  rw [i8Psi4s156_eq_S]
  unfold i8Psi4s156S0 i8Psi4s156S1
  rw [hpl_zero_at_one, hpl_zero_one_at_one, hpl_zero_one_one_at_one, hpl_zero_zero_one_one_at_one,
    hpl_zero_one_zero_one_at_one, hpl_zero_one_one_zero_at_one, hpl_zero_one_one_one_at_one,
    hpl_zero_zero_one_one_one_at_one, hpl_zero_one_zero_one_one_at_one,
    hpl_zero_one_one_zero_one_at_one, hpl_zero_one_one_one_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s157` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s157S0 (x : ℝ) : ℝ :=
    (x ^ 3 - x ^ 4 / 2) / x ^ 2 +
    (x ^ 3 - x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-2 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-4 * x ^ 2 + 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one, one] x) +
    (-16) * hpl [zero, one, one, one] x +
    (-8 * x ^ 2 + 8 * x ^ 3 + 16 * x) / x ^ 2 * ((1 - x) * hpl [one, one, one, one] x) +
    (16) * hpl [zero, one, one, one, one] x

theorem continuousOn_i8Psi4s157S0 : ContinuousOn i8Psi4s157S0 (Ioc 0 1) := by
  unfold i8Psi4s157S0
  exact (((((((i13_cont_coef (p := fun x => x ^ 3 - x ^ 4 / 2) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 3 - x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 2 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, one]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 2 + 8 * x ^ 3 + 16 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, one, one])))

theorem i8Psi4s157_eq_S (x : ℝ) : i8Psi4s157 x = i8Psi4s157S0 x := by
  unfold i8Psi4s157 i8Psi4s157S0 i8Psi4s157N0 i8Psi4s157N1 i8Psi4s157N2 i8Psi4s157N3 i8Psi4s157N4
    i8Psi4s157W
  ring

theorem continuousOn_i8Psi4s157 : ContinuousOn i8Psi4s157 (Ioc 0 1) := by
  rw [show i8Psi4s157 = fun x => i8Psi4s157S0 x from funext i8Psi4s157_eq_S]
  exact continuousOn_i8Psi4s157S0

theorem i8Psi4s157_one : i8Psi4s157 1 = 1 / 2 + 16 * zeta5 - 8 / 45 * π ^ 4 := by
  rw [i8Psi4s157_eq_S]
  unfold i8Psi4s157S0
  rw [hpl_zero_one_one_one_at_one, hpl_zero_one_one_one_one_at_one]
  norm_num
  ring

end QED.ThreeLoopD
