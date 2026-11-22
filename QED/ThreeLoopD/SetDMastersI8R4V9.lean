/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4V8

/-!
# Set (d), master `I₈`: continuity and values at `1` of the sub-pieces 128 to 137 of `Ψ₄`

Each sub-piece `Ψ₄⁽ⁿ⁾` is continuous on `(0, 1]` (the words beginning with `1` carry a factor
`1 - ξ`), and its value at `ξ = 1` follows from the values of the harmonic polylogarithms at `1`.

## Main results

* `QED.ThreeLoopD.continuousOn_i8Psi4s128`, `QED.ThreeLoopD.i8Psi4s128_one` and their
  companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- Chunk 0 of `i8Psi4s128k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s128k0S0 (x : ℝ) : ℝ :=
    (-x ^ 4 - 117 / 2 * x ^ 3) / x ^ 2 +
    (x ^ 4 / 2 + 15 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (3 / 2 * x ^ 3 + 87 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x ^ 4 + 6 * x ^ 2 + 14 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-x ^ 3 - 15 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-6 * x + 2 * x ^ 3 + 28 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [negOne, one, one] x +
    (4) * hpl [zero, zero, one] x +
    (4) * hpl [zero, one, zero] x +
    (-4 * x + 2 * x ^ 4 + 12 * x ^ 3 + 14 * x ^ 2) / x ^ 2 * hpl [zero, one, one] x +
    (-14 * x ^ 2 - 4 * x - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, one] x) +
    (-14 * x ^ 2 - 4 * x - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one, zero] x) +
    (-4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one, one] x +
    (-4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero, one] x +
    (-4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, one, one, zero] x +
    (-4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, negOne, one, one] x +
    (12) * hpl [zero, zero, one, one] x +
    (12) * hpl [zero, one, zero, one] x +
    (12) * hpl [zero, one, one, zero] x

theorem continuousOn_i8Psi4s128k0S0 : ContinuousOn i8Psi4s128k0S0 (Ioc 0 1) := by
  unfold i8Psi4s128k0S0
  exact (((((((((((((((((((i13_cont_coef (p := fun x => -x ^ 4 - 117 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 15 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 3 / 2 * x ^ 3 + 87 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 6 * x ^ 2 + 14 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 15 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -6 * x + 2 * x ^ 3 + 28 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x + 2 * x ^ 4 + 12 * x ^ 3 +
        14 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -14 * x ^ 2 - 4 * x - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -14 * x ^ 2 - 4 * x - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one, one]))).add
      ((i13_cont_coef (p := fun x => -4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, one, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero])))

theorem i8Psi4s128k0_eq_S (x : ℝ) : i8Psi4s128k0 x = i8Psi4s128k0S0 x := by
  unfold i8Psi4s128k0 i8Psi4s128k0S0 i8Psi4s128k0N0 i8Psi4s128k0N1 i8Psi4s128k0N2 i8Psi4s128k0N3
    i8Psi4s128k0N4 i8Psi4s128k0W
  ring

theorem continuousOn_i8Psi4s128k0 : ContinuousOn i8Psi4s128k0 (Ioc 0 1) := by
  rw [show i8Psi4s128k0 = fun x => i8Psi4s128k0S0 x from funext i8Psi4s128k0_eq_S]
  exact continuousOn_i8Psi4s128k0S0

theorem i8Psi4s128k0_one : i8Psi4s128k0 1 = -119 / 2 + 3 * Real.log 2 ^ 4 + 20 * zeta3 +
    72 * Li 4 (1 / 2) - 2 / 5 * π ^ 4 + 7 / 2 * π ^ 2 := by
  rw [i8Psi4s128k0_eq_S]
  unfold i8Psi4s128k0S0
  rw [hpl_zero_at_one, hpl_zero_one_at_one, hpl_negOne_one_one_at_one, hpl_zero_zero_one_at_one,
    hpl_zero_one_zero_at_one, hpl_zero_one_one_at_one, hpl_negOne_zero_one_one_at_one,
    hpl_negOne_one_zero_one_at_one, hpl_negOne_one_one_zero_at_one, hpl_zero_negOne_one_one_at_one,
    hpl_zero_zero_one_one_at_one, hpl_zero_one_zero_one_at_one, hpl_zero_one_one_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s128k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s128k1S0 (x : ℝ) : ℝ :=
    (-x ^ 4 - 147 / 2 * x ^ 3) / x ^ 2 +
    (x ^ 4 / 2 + 19 * x ^ 3 + 37 / 2 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (x ^ 4 / 2 + 19 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (x ^ 3 + 36 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x ^ 4 - 2 * x + 15 * x ^ 2 + 18 * x ^ 3) / x ^ 2 * hpl [negOne, one] x +
    (2) * hpl [zero, negOne] x +
    (x ^ 4 + 2 * x ^ 2 + 18 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-x ^ 3 - 19 * x ^ 2 - 2 * x) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (-x ^ 3 - 19 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-22 * x ^ 2 - 20 * x ^ 3 - 4 * x - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one] x +
    (-22 * x ^ 2 - 20 * x ^ 3 - 4 * x - 2 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero] x +
    (18) * hpl [zero, negOne, one] x +
    (4) * hpl [zero, zero, one] x +
    (18) * hpl [zero, one, negOne] x +
    (4) * hpl [zero, one, zero] x +
    (-2 - 18 * x - 18 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, one] x) +
    (-2 - 18 * x - 18 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one, negOne] x) +
    (20) * hpl [zero, negOne, zero, one] x +
    (20) * hpl [zero, negOne, one, zero] x +
    (-4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, one, negOne, one] x

theorem continuousOn_i8Psi4s128k1S0 : ContinuousOn i8Psi4s128k1S0 (Ioc 0 1) := by
  unfold i8Psi4s128k1S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -x ^ 4 -
    147 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 19 * x ^ 3 + 37 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 19 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + 36 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 2 * x + 15 * x ^ 2 + 18 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 2 * x ^ 2 + 18 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 19 * x ^ 2 - 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 19 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -22 * x ^ 2 - 20 * x ^ 3 - 4 * x -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -22 * x ^ 2 - 20 * x ^ 3 - 4 * x -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 18 * x - 18 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, one]))).add
      ((i13_cont_coef (p := fun x => -2 - 18 * x - 18 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, one])))

/-- Chunk 1 of `i8Psi4s128k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s128k1S1 (x : ℝ) : ℝ :=
    (-4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, one, one, negOne] x +
    (-4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero, one] x) +
    (-4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, one, zero] x)

theorem continuousOn_i8Psi4s128k1S1 : ContinuousOn i8Psi4s128k1S1 (Ioc 0 1) := by
  unfold i8Psi4s128k1S1
  exact ((((i13_cont_coef (p := fun x => -4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, negOne])).add
      ((i13_cont_coef (p := fun x => -4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero, one]))).add
      ((i13_cont_coef (p := fun x => -4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, one, zero])))

theorem i8Psi4s128k1_eq_S (x : ℝ) : i8Psi4s128k1 x = i8Psi4s128k1S0 x + i8Psi4s128k1S1 x := by
  unfold i8Psi4s128k1 i8Psi4s128k1S0 i8Psi4s128k1S1 i8Psi4s128k1N0 i8Psi4s128k1N1 i8Psi4s128k1N2
    i8Psi4s128k1N3 i8Psi4s128k1N4 i8Psi4s128k1W
  ring

theorem continuousOn_i8Psi4s128k1 : ContinuousOn i8Psi4s128k1 (Ioc 0 1) := by
  rw [show i8Psi4s128k1 = fun x => i8Psi4s128k1S0 x +
    i8Psi4s128k1S1 x from funext i8Psi4s128k1_eq_S]
  exact (continuousOn_i8Psi4s128k1S0.add continuousOn_i8Psi4s128k1S1)

theorem i8Psi4s128k1_one : i8Psi4s128k1 1 = -149 / 2 - 16 * Real.log 2 ^ 2 + 38 * Real.log 2 -
    π ^ 4 / 4 + 19 / 3 * π ^ 2 + 341 / 4 * zeta3 - 35 * Real.log 2 * zeta3 -
    12 * Real.log 2 * π ^ 2 + 5 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s128k1_eq_S]
  unfold i8Psi4s128k1S0 i8Psi4s128k1S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one,
    hpl_zero_one_at_one, hpl_negOne_zero_one_at_one, hpl_negOne_one_zero_at_one,
    hpl_zero_negOne_one_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_zero_at_one, hpl_zero_negOne_zero_one_at_one, hpl_zero_negOne_one_zero_at_one,
    hpl_zero_one_negOne_one_at_one, hpl_zero_one_one_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s128k2` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s128k2S0 (x : ℝ) : ℝ :=
    (-x ^ 4 - 165 / 2 * x ^ 3) / x ^ 2 +
    (x ^ 4 + 42 * x ^ 2 + 43 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (x ^ 4 / 2 + 21 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (x ^ 3 / 2 + 39 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-x ^ 4 - 22 * x ^ 3 - 21 * x ^ 2) / x ^ 2 * hpl [negOne, zero] x +
    (x ^ 4 - 4 * x + 15 * x ^ 2 + 20 * x ^ 3) / x ^ 2 * hpl [negOne, one] x +
    (-x ^ 4 - 22 * x ^ 3 + 4 * x ^ 2) / x ^ 2 * hpl [zero, negOne] x +
    (4) * hpl [zero, one] x +
    (-x ^ 3 - 21 * x ^ 2 - 4 * x) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (4) * hpl [zero, negOne, zero] x +
    (-20 * x ^ 3 - 4 * x - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, one] x +
    (4) * hpl [zero, zero, negOne] x +
    (-20 * x ^ 3 - 4 * x - 2 * x ^ 4) / x ^ 2 * hpl [zero, one, negOne] x +
    (-4 * x + 2 * x ^ 3 + 22 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (-4 * x + 2 * x ^ 3 + 22 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (20) * hpl [zero, zero, negOne, one] x +
    (20) * hpl [zero, zero, one, negOne] x +
    (20) * hpl [zero, one, negOne, zero] x +
    (20) * hpl [zero, one, zero, negOne] x +
    (-4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne, one] x)

theorem continuousOn_i8Psi4s128k2S0 : ContinuousOn i8Psi4s128k2S0 (Ioc 0 1) := by
  unfold i8Psi4s128k2S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -x ^ 4 -
    165 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 42 * x ^ 2 + 43 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 21 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 + 39 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 22 * x ^ 3 - 21 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 4 * x + 15 * x ^ 2 + 20 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 22 * x ^ 3 + 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 21 * x ^ 2 - 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -20 * x ^ 3 - 4 * x - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -20 * x ^ 3 - 4 * x - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -4 * x + 2 * x ^ 3 + 22 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x + 2 * x ^ 3 + 22 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne, one])))

/-- Chunk 1 of `i8Psi4s128k2` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s128k2S1 (x : ℝ) : ℝ :=
    (-4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, one, negOne] x) +
    (-4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one, negOne, zero] x) +
    (-4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one, zero, negOne] x)

theorem continuousOn_i8Psi4s128k2S1 : ContinuousOn i8Psi4s128k2S1 (Ioc 0 1) := by
  unfold i8Psi4s128k2S1
  exact ((((i13_cont_coef (p := fun x => -4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one, negOne])).add
      ((i13_cont_coef (p := fun x => -4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero, negOne])))

theorem i8Psi4s128k2_eq_S (x : ℝ) : i8Psi4s128k2 x = i8Psi4s128k2S0 x + i8Psi4s128k2S1 x := by
  unfold i8Psi4s128k2 i8Psi4s128k2S0 i8Psi4s128k2S1 i8Psi4s128k2N0 i8Psi4s128k2N1 i8Psi4s128k2N2
    i8Psi4s128k2N3 i8Psi4s128k2N4 i8Psi4s128k2W
  ring

theorem continuousOn_i8Psi4s128k2 : ContinuousOn i8Psi4s128k2 (Ioc 0 1) := by
  rw [show i8Psi4s128k2 = fun x => i8Psi4s128k2S0 x +
    i8Psi4s128k2S1 x from funext i8Psi4s128k2_eq_S]
  exact (continuousOn_i8Psi4s128k2S0.add continuousOn_i8Psi4s128k2S1)

theorem i8Psi4s128k2_one : i8Psi4s128k2 1 = -167 / 2 - 16 * Real.log 2 ^ 2 + 40 * Li 4 (1 / 2) +
    86 * Real.log 2 - 77 / 4 * zeta3 + 5 / 3 * Real.log 2 ^ 4 + 11 / 72 * π ^ 4 +
    65 / 12 * π ^ 2 - 35 * Real.log 2 * zeta3 - 5 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s128k2_eq_S]
  unfold i8Psi4s128k2S0 i8Psi4s128k2S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_negOne_one_at_one,
    hpl_zero_negOne_at_one, hpl_zero_one_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_negOne_one_at_one, hpl_zero_zero_negOne_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_zero_negOne_one_at_one, hpl_zero_zero_one_negOne_at_one,
    hpl_zero_one_negOne_zero_at_one, hpl_zero_one_zero_negOne_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s128 : ContinuousOn i8Psi4s128 (Ioc 0 1) := by
  rw [show i8Psi4s128 = fun x => i8Psi4s128k0 x + i8Psi4s128k1 x + i8Psi4s128k2 x from rfl]
  exact ((continuousOn_i8Psi4s128k0.add continuousOn_i8Psi4s128k1).add continuousOn_i8Psi4s128k2)

theorem i8Psi4s128_one : i8Psi4s128 1 = -435 / 2 - 32 * Real.log 2 ^ 2 + 86 * zeta3 +
    112 * Li 4 (1 / 2) + 124 * Real.log 2 - 179 / 360 * π ^ 4 + 14 / 3 * Real.log 2 ^ 4 +
    61 / 4 * π ^ 2 - 70 * Real.log 2 * zeta3 - 12 * Real.log 2 * π ^ 2 +
    10 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  unfold i8Psi4s128
  rw [i8Psi4s128k0_one, i8Psi4s128k1_one, i8Psi4s128k2_one]
  ring

/-- Chunk 0 of `i8Psi4s129` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s129S0 (x : ℝ) : ℝ :=
    (32 * x - 17 / 8 * x ^ 4 - 15 / 2 * x ^ 3 - π ^ 2 * x / 3 - π ^ 2 * x ^ 3 / 3 -
      π ^ 2 * x ^ 4 / 24) / x ^ 2 +
    (32 * x + 15 / 2 * x ^ 3 + 17 / 4 * x ^ 4 - π ^ 2 * x / 3 + π ^ 2 * x ^ 3 / 3 +
      π ^ 2 * x ^ 4 / 12) / x ^ 2 * hpl [zero] x +
    (-4 * x - 4 * x ^ 3 - 15 / 2 * x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [negOne, zero] x +
    (-8 * x ^ 4 - 4 * x ^ 3 + 4 * x ^ 2 + 32 * x - π ^ 2 * x / 3 - π ^ 2 * x ^ 3 / 3 -
      π ^ 2 * x ^ 4 / 6) / x ^ 2 * hpl [zero, zero] x +
    (-8 * x - 2 * x ^ 2 + 2 * x ^ 4 + 8 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero] x +
    (x ^ 4 - 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero] x +
    (6 * x ^ 3 + 6 * x ^ 4 + 16 * x ^ 2 + 24 * x +
      π ^ 2 * x ^ 2 / 3) / x ^ 2 * hpl [zero, zero, zero] x +
    (-18 * x ^ 2 - 12 * x - 12 * x ^ 3 - 6 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero, zero] x +
    (-8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero, zero] x +
    (-4 * x - 4 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne, zero] x +
    (6 * x ^ 4 + 12 * x + 12 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero, zero] x +
    (12) * hpl [zero, negOne, zero, zero, zero] x +
    (8) * hpl [zero, zero, negOne, zero, zero] x +
    (4) * hpl [zero, zero, zero, negOne, zero] x +
    (-12) * hpl [zero, zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s129S0 : ContinuousOn i8Psi4s129S0 (Ioc 0 1) := by
  unfold i8Psi4s129S0
  exact (((((((((((((((i13_cont_coef (p := fun x => 32 * x - 17 / 8 * x ^ 4 - 15 / 2 * x ^ 3 -
    π ^ 2 * x / 3 - π ^ 2 * x ^ 3 / 3 - π ^ 2 * x ^ 4 / 24) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 32 * x + 15 / 2 * x ^ 3 + 17 / 4 * x ^ 4 - π ^ 2 * x / 3 +
        π ^ 2 * x ^ 3 / 3 + π ^ 2 * x ^ 4 / 12) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -4 * x - 4 * x ^ 3 - 15 / 2 * x ^ 2 -
        x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 4 - 4 * x ^ 3 + 4 * x ^ 2 + 32 * x - π ^ 2 * x / 3 -
        π ^ 2 * x ^ 3 / 3 - π ^ 2 * x ^ 4 / 6) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x - 2 * x ^ 2 + 2 * x ^ 4 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 6 * x ^ 3 + 6 * x ^ 4 + 16 * x ^ 2 + 24 * x +
        π ^ 2 * x ^ 2 / 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -18 * x ^ 2 - 12 * x - 12 * x ^ 3 -
        6 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x - 4 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 6 * x ^ 4 + 12 * x + 12 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, zero])))

theorem i8Psi4s129_eq_S (x : ℝ) : i8Psi4s129 x = i8Psi4s129S0 x := by
  unfold i8Psi4s129 i8Psi4s129S0 i8Psi4s129N0 i8Psi4s129N1 i8Psi4s129N2 i8Psi4s129N3 i8Psi4s129N4
    i8Psi4s129W
  ring

theorem continuousOn_i8Psi4s129 : ContinuousOn i8Psi4s129 (Ioc 0 1) := by
  rw [show i8Psi4s129 = fun x => i8Psi4s129S0 x from funext i8Psi4s129_eq_S]
  exact continuousOn_i8Psi4s129S0

theorem i8Psi4s129_one : i8Psi4s129 1 = 179 / 8 - 15 * zeta5 - 3 / 2 * zeta3 + 5 / 8 * π ^ 2 +
    7 / 40 * π ^ 4 := by
  have h5 : hpl [zero, zero, zero, zero, zero] 1 = 0 := by
    rw [hpl_of_allZero (by decide)]
    simp
  rw [i8Psi4s129_eq_S]
  unfold i8Psi4s129S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_zero_zero_at_one, hpl_negOne_zero_zero_zero_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_zero_at_one, hpl_zero_zero_zero_negOne_zero_at_one, h5]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s130` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s130S0 (x : ℝ) : ℝ :=
    (-20 * x ^ 3 + 4 * x ^ 4 + π ^ 2 * x ^ 4 / 6 + 11 / 6 * π ^ 2 * x ^ 3) / x ^ 2 +
    (-16 * x ^ 2 - 4 * x ^ 4 + 8 * x ^ 3 - π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 6 +
      2 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (-4 * x ^ 3 + 12 * x ^ 2 + 16 * x - 5 / 6 * π ^ 2 * x ^ 2 - 2 / 3 * π ^ 2 * x -
      π ^ 2 * x ^ 3 / 6) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-16 + 2 / 3 * π ^ 2) * hpl [zero, zero] x +
    (-8 * x ^ 4 + 16 * x + 16 * x ^ 3 - 2 / 3 * π ^ 2 * x - 2 / 3 * π ^ 2 * x ^ 3 -
      π ^ 2 * x ^ 4 / 3) / x ^ 2 * hpl [zero, one] x +
    (-8 * x ^ 2 + 8 * x ^ 3 + 16 * x + π ^ 2 * x ^ 2 - 2 / 3 * π ^ 2 * x +
      π ^ 2 * x ^ 3 / 3) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (16 + 2 / 3 * π ^ 2) * hpl [zero, zero, one] x +
    (16 + 2 / 3 * π ^ 2) * hpl [zero, one, zero] x

theorem continuousOn_i8Psi4s130S0 : ContinuousOn i8Psi4s130S0 (Ioc 0 1) := by
  unfold i8Psi4s130S0
  exact ((((((((i13_cont_coef (p := fun x => -20 * x ^ 3 + 4 * x ^ 4 + π ^ 2 * x ^ 4 / 6 +
    11 / 6 * π ^ 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -16 * x ^ 2 - 4 * x ^ 4 + 8 * x ^ 3 - π ^ 2 * x ^ 3 -
        π ^ 2 * x ^ 4 / 6 + 2 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 3 + 12 * x ^ 2 + 16 * x - 5 / 6 * π ^ 2 * x ^ 2 -
        2 / 3 * π ^ 2 * x - π ^ 2 * x ^ 3 / 6) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 4 + 16 * x + 16 * x ^ 3 - 2 / 3 * π ^ 2 * x -
        2 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 2 + 8 * x ^ 3 + 16 * x + π ^ 2 * x ^ 2 -
        2 / 3 * π ^ 2 * x + π ^ 2 * x ^ 3 / 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero])))

theorem i8Psi4s130_eq_S (x : ℝ) : i8Psi4s130 x = i8Psi4s130S0 x := by
  unfold i8Psi4s130 i8Psi4s130S0 i8Psi4s130N0 i8Psi4s130N1 i8Psi4s130N2 i8Psi4s130N3 i8Psi4s130N4
    i8Psi4s130W
  ring

theorem continuousOn_i8Psi4s130 : ContinuousOn i8Psi4s130 (Ioc 0 1) := by
  rw [show i8Psi4s130 = fun x => i8Psi4s130S0 x from funext i8Psi4s130_eq_S]
  exact continuousOn_i8Psi4s130S0

theorem i8Psi4s130_one : i8Psi4s130 1 = -16 - 16 * zeta3 + 6 * π ^ 2 - 5 / 18 * π ^ 4 -
    2 / 3 * π ^ 2 * zeta3 := by
  rw [i8Psi4s130_eq_S]
  unfold i8Psi4s130S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_one_at_one,
    hpl_zero_one_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s131k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s131k0S0 (x : ℝ) : ℝ :=
    (7 / 4 * x ^ 4 + 75 / 2 * x ^ 3) / x ^ 2 +
    (-22 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (-31 / 2 * x ^ 2 - 3 / 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (2 * x ^ 4 + 12 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-14 * x ^ 3 - 3 * x ^ 4) / x ^ 2 * hpl [zero, one] x +
    (2 * x ^ 3 + 10 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-8 * x - 2 * x ^ 2 + 2 * x ^ 4 + 8 * x ^ 3) / x ^ 2 * hpl [negOne, zero, one] x +
    (4 * x ^ 4 + 8 * x ^ 2 + 8 * x ^ 3) / x ^ 2 * hpl [zero, zero, one] x +
    (4 * x ^ 4 + 8 * x ^ 3) / x ^ 2 * hpl [zero, one, zero] x +
    (-12 * x ^ 2 - 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 8 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero, one] x +
    (-24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 8 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one, zero] x +
    (-24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 8 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero, zero] x +
    (-8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero, one] x +
    (16) * hpl [zero, zero, zero, one] x +
    (16) * hpl [zero, zero, one, zero] x +
    (16) * hpl [zero, one, zero, zero] x +
    (16) * hpl [zero, negOne, zero, zero, one] x +
    (16) * hpl [zero, negOne, zero, one, zero] x +
    (16) * hpl [zero, negOne, one, zero, zero] x

theorem continuousOn_i8Psi4s131k0S0 : ContinuousOn i8Psi4s131k0S0 (Ioc 0 1) := by
  unfold i8Psi4s131k0S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => 7 / 4 * x ^ 4 +
    75 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -22 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -31 / 2 * x ^ 2 - 3 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 12 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -14 * x ^ 3 - 3 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 3 + 10 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x - 2 * x ^ 2 + 2 * x ^ 4 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x ^ 2 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, one]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one, zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero, zero])))

/-- Chunk 1 of `i8Psi4s131k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s131k0S1 (x : ℝ) : ℝ :=
    (8) * hpl [zero, zero, negOne, zero, one] x

theorem continuousOn_i8Psi4s131k0S1 : ContinuousOn i8Psi4s131k0S1 (Ioc 0 1) := by
  unfold i8Psi4s131k0S1
  exact (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, one]))

theorem i8Psi4s131k0_eq_S (x : ℝ) : i8Psi4s131k0 x = i8Psi4s131k0S0 x + i8Psi4s131k0S1 x := by
  unfold i8Psi4s131k0 i8Psi4s131k0S0 i8Psi4s131k0S1 i8Psi4s131k0N0 i8Psi4s131k0N1 i8Psi4s131k0N2
    i8Psi4s131k0N3 i8Psi4s131k0N4 i8Psi4s131k0W
  ring

theorem continuousOn_i8Psi4s131k0 : ContinuousOn i8Psi4s131k0 (Ioc 0 1) := by
  rw [show i8Psi4s131k0 = fun x => i8Psi4s131k0S0 x +
    i8Psi4s131k0S1 x from funext i8Psi4s131k0_eq_S]
  exact (continuousOn_i8Psi4s131k0S0.add continuousOn_i8Psi4s131k0S1)

theorem i8Psi4s131k0_one : i8Psi4s131k0 1 = 157 / 4 - 128 * Li 4 (1 / 2) - 4 * zeta3 +
    103 * zeta5 - 17 / 6 * π ^ 2 - 16 / 3 * Real.log 2 ^ 4 + 59 / 120 * π ^ 4 -
    Real.log 2 * π ^ 4 - 3 * π ^ 2 * zeta3 + 16 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s131k0_eq_S]
  unfold i8Psi4s131k0S0 i8Psi4s131k0S1
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_negOne_zero_one_at_one,
    hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one, hpl_negOne_zero_zero_one_at_one,
    hpl_negOne_zero_one_zero_at_one, hpl_negOne_one_zero_zero_at_one,
    hpl_zero_negOne_zero_one_at_one, hpl_zero_zero_zero_one_at_one, hpl_zero_zero_one_zero_at_one,
    hpl_zero_one_zero_zero_at_one, hpl_zero_negOne_zero_zero_one_at_one,
    hpl_zero_negOne_zero_one_zero_at_one, hpl_zero_negOne_one_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_one_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s131k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s131k1S0 (x : ℝ) : ℝ :=
    (47 * x ^ 3 + 5 / 4 * x ^ 4) / x ^ 2 +
    (-47 * x ^ 3 - 5 / 2 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (2 * x ^ 4 + 20 * x ^ 2 + 22 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (2 * x ^ 4 + 20 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (x ^ 3 + 7 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-24 * x ^ 3 - 20 * x ^ 2 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-8 * x - 2 * x ^ 2 + 2 * x ^ 4 + 8 * x ^ 3) / x ^ 2 * hpl [negOne, one, zero] x +
    (-12 * x ^ 3 - 2 * x ^ 4 + 8 * x ^ 2) / x ^ 2 * hpl [zero, negOne, zero] x +
    (8) * hpl [zero, one, zero] x +
    (-10 * x ^ 2 - 8 * x - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (16) * hpl [zero, negOne, zero, zero] x +
    (-8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, negOne, one, zero] x +
    (8) * hpl [zero, zero, negOne, zero] x +
    (-8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, one, negOne, zero] x +
    (-16 * x + 8 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero, zero] x) +
    (-8 * x + 4 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne, zero] x) +
    (8) * hpl [zero, zero, negOne, one, zero] x +
    (8) * hpl [zero, zero, one, negOne, zero] x +
    (16) * hpl [zero, one, negOne, zero, zero] x +
    (8) * hpl [zero, one, zero, negOne, zero] x

theorem continuousOn_i8Psi4s131k1S0 : ContinuousOn i8Psi4s131k1S0 (Ioc 0 1) := by
  unfold i8Psi4s131k1S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => 47 * x ^ 3 +
    5 / 4 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -47 * x ^ 3 - 5 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 20 * x ^ 2 + 22 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 20 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + 7 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 3 - 20 * x ^ 2 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x - 2 * x ^ 2 + 2 * x ^ 4 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 2 * x ^ 4 + 8 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -10 * x ^ 2 - 8 * x - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -16 * x + 8 * x ^ 3 + 24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x + 4 * x ^ 3 + 12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne, zero])))

theorem i8Psi4s131k1_eq_S (x : ℝ) : i8Psi4s131k1 x = i8Psi4s131k1S0 x := by
  unfold i8Psi4s131k1 i8Psi4s131k1S0 i8Psi4s131k1N0 i8Psi4s131k1N1 i8Psi4s131k1N2 i8Psi4s131k1N3
    i8Psi4s131k1N4 i8Psi4s131k1W
  ring

theorem continuousOn_i8Psi4s131k1 : ContinuousOn i8Psi4s131k1 (Ioc 0 1) := by
  rw [show i8Psi4s131k1 = fun x => i8Psi4s131k1S0 x from funext i8Psi4s131k1_eq_S]
  exact continuousOn_i8Psi4s131k1S0

theorem i8Psi4s131k1_one : i8Psi4s131k1 1 = 193 / 4 - 43 * zeta3 - 155 / 2 * zeta5 -
    11 / 3 * π ^ 2 + 23 / 45 * π ^ 4 + Real.log 2 * π ^ 4 + 7 / 6 * π ^ 2 * zeta3 := by
  rw [i8Psi4s131k1_eq_S]
  unfold i8Psi4s131k1S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one,
    hpl_negOne_one_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_one_zero_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_negOne_one_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_one_negOne_zero_at_one,
    hpl_zero_zero_negOne_one_zero_at_one, hpl_zero_zero_one_negOne_zero_at_one,
    hpl_zero_one_negOne_zero_zero_at_one, hpl_zero_one_zero_negOne_zero_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s131 : ContinuousOn i8Psi4s131 (Ioc 0 1) := by
  rw [show i8Psi4s131 = fun x => i8Psi4s131k0 x + i8Psi4s131k1 x from rfl]
  exact (continuousOn_i8Psi4s131k0.add continuousOn_i8Psi4s131k1)

theorem i8Psi4s131_one : i8Psi4s131 1 = 175 / 2 - 128 * Li 4 (1 / 2) - 47 * zeta3 -
    16 / 3 * Real.log 2 ^ 4 - 13 / 2 * π ^ 2 + 51 / 2 * zeta5 + 361 / 360 * π ^ 4 -
    11 / 6 * π ^ 2 * zeta3 + 16 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  unfold i8Psi4s131
  rw [i8Psi4s131k0_one, i8Psi4s131k1_one]
  ring

/-- Chunk 0 of `i8Psi4s132` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s132S0 (x : ℝ) : ℝ :=
    (-237 / 4 * x ^ 3 - 3 / 2 * x ^ 4) / x ^ 2 +
    (-12 * x ^ 2 + 9 / 4 * x ^ 4 + 93 / 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (12 * x + 3 / 4 * x ^ 3 + 51 / 4 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-33 * x ^ 3 - 12 * x ^ 2 - 3 * x ^ 4) / x ^ 2 * hpl [zero, zero] x +
    (12 * x + 12 * x ^ 3 + 3 / 2 * x ^ 4) / x ^ 2 * hpl [zero, one] x +
    (12 * x - 27 / 2 * x ^ 2 - 3 / 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-12 * x ^ 2 + 3 * x ^ 4 + 18 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero] x +
    (-12 * x ^ 3 - 3 * x ^ 4 + 12 * x) / x ^ 2 * hpl [zero, zero, one] x +
    (-12 * x ^ 3 - 3 * x ^ 4 + 12 * x) / x ^ 2 * hpl [zero, one, zero] x +
    (3 * x ^ 3 + 12 * x + 15 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-12) * hpl [zero, zero, zero, zero] x +
    (6 * x ^ 4 + 12 * x + 12 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero, one] x +
    (6 * x ^ 4 + 12 * x + 12 * x ^ 3) / x ^ 2 * hpl [zero, zero, one, zero] x +
    (6 * x ^ 4 + 12 * x + 12 * x ^ 3) / x ^ 2 * hpl [zero, one, zero, zero] x +
    (-18 * x ^ 2 - 6 * x ^ 3 + 12 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero, zero] x) +
    (-12) * hpl [zero, zero, zero, zero, one] x +
    (-12) * hpl [zero, zero, zero, one, zero] x +
    (-12) * hpl [zero, zero, one, zero, zero] x +
    (-12) * hpl [zero, one, zero, zero, zero] x

theorem continuousOn_i8Psi4s132S0 : ContinuousOn i8Psi4s132S0 (Ioc 0 1) := by
  unfold i8Psi4s132S0
  exact (((((((((((((((((((i13_cont_coef (p := fun x => -237 / 4 * x ^ 3 -
    3 / 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 + 9 / 4 * x ^ 4 +
        93 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 12 * x + 3 / 4 * x ^ 3 + 51 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -33 * x ^ 3 - 12 * x ^ 2 - 3 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 12 * x + 12 * x ^ 3 + 3 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => 12 * x - 27 / 2 * x ^ 2 - 3 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 + 3 * x ^ 4 + 18 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 3 * x ^ 4 + 12 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 3 * x ^ 4 + 12 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => 3 * x ^ 3 + 12 * x + 15 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 6 * x ^ 4 + 12 * x + 12 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      ((i13_cont_coef (p := fun x => 6 * x ^ 4 + 12 * x + 12 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      ((i13_cont_coef (p := fun x => 6 * x ^ 4 + 12 * x + 12 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -18 * x ^ 2 - 6 * x ^ 3 + 12 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero, zero])))

theorem i8Psi4s132_eq_S (x : ℝ) : i8Psi4s132 x = i8Psi4s132S0 x := by
  unfold i8Psi4s132 i8Psi4s132S0 i8Psi4s132N0 i8Psi4s132N1 i8Psi4s132N2 i8Psi4s132N3 i8Psi4s132N4
    i8Psi4s132W
  ring

theorem continuousOn_i8Psi4s132 : ContinuousOn i8Psi4s132 (Ioc 0 1) := by
  rw [show i8Psi4s132 = fun x => i8Psi4s132S0 x from funext i8Psi4s132_eq_S]
  exact continuousOn_i8Psi4s132S0

theorem i8Psi4s132_one : i8Psi4s132 1 = -243 / 4 + 3 * zeta3 + 12 * zeta5 + π ^ 4 / 3 +
    17 / 4 * π ^ 2 := by
  rw [i8Psi4s132_eq_S]
  unfold i8Psi4s132S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one, hpl_zero_zero_zero_zero_at_one,
    hpl_zero_zero_zero_one_at_one, hpl_zero_zero_one_zero_at_one, hpl_zero_one_zero_zero_at_one,
    hpl_zero_zero_zero_zero_one_at_one, hpl_zero_zero_zero_one_zero_at_one,
    hpl_zero_zero_one_zero_zero_at_one, hpl_zero_one_zero_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s133` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s133S0 (x : ℝ) : ℝ :=
    (3 * x ^ 4 + 62 * x ^ 3) / x ^ 2 +
    (-44 * x ^ 3 - 16 * x ^ 2 - 4 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (-18 * x ^ 2 - 2 * x ^ 3 + 16 * x) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-16 * x ^ 2 + 4 * x ^ 4 + 24 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-16 * x ^ 3 - 4 * x ^ 4 + 16 * x) / x ^ 2 * hpl [zero, one] x +
    (4 * x ^ 3 + 16 * x + 20 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-16) * hpl [zero, zero, zero] x +
    (8 * x ^ 4 + 16 * x + 16 * x ^ 3) / x ^ 2 * hpl [zero, zero, one] x +
    (8 * x ^ 4 + 16 * x + 16 * x ^ 3) / x ^ 2 * hpl [zero, one, zero] x +
    (-24 * x ^ 2 - 8 * x ^ 3 + 16 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-16) * hpl [zero, zero, zero, one] x +
    (-16) * hpl [zero, zero, one, zero] x +
    (-16) * hpl [zero, one, zero, zero] x

theorem continuousOn_i8Psi4s133S0 : ContinuousOn i8Psi4s133S0 (Ioc 0 1) := by
  unfold i8Psi4s133S0
  exact (((((((((((((i13_cont_coef (p := fun x => 3 * x ^ 4 + 62 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -44 * x ^ 3 - 16 * x ^ 2 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -18 * x ^ 2 - 2 * x ^ 3 + 16 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -16 * x ^ 2 + 4 * x ^ 4 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -16 * x ^ 3 - 4 * x ^ 4 + 16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 3 + 16 * x + 20 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 8 * x ^ 4 + 16 * x + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => 8 * x ^ 4 + 16 * x + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 8 * x ^ 3 + 16 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero])))

theorem i8Psi4s133_eq_S (x : ℝ) : i8Psi4s133 x = i8Psi4s133S0 x := by
  unfold i8Psi4s133 i8Psi4s133S0 i8Psi4s133N0 i8Psi4s133N1 i8Psi4s133N2 i8Psi4s133N3 i8Psi4s133N4
    i8Psi4s133W
  ring

theorem continuousOn_i8Psi4s133 : ContinuousOn i8Psi4s133 (Ioc 0 1) := by
  rw [show i8Psi4s133 = fun x => i8Psi4s133S0 x from funext i8Psi4s133_eq_S]
  exact continuousOn_i8Psi4s133S0

theorem i8Psi4s133_one : i8Psi4s133 1 = 65 - 40 * zeta3 - 8 / 45 * π ^ 4 - 2 / 3 * π ^ 2 := by
  rw [i8Psi4s133_eq_S]
  unfold i8Psi4s133S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one, hpl_zero_zero_zero_one_at_one,
    hpl_zero_zero_one_zero_at_one, hpl_zero_one_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s134` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s134S0 (x : ℝ) : ℝ :=
    (-4 * x ^ 4 + 8 * x ^ 3 - 7 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 6) / x ^ 2 +
    (-8 * x ^ 2 + 8 * x ^ 3 + π ^ 2 * x ^ 3 / 3 + 7 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * ((1 -
      x) * hpl [one] x) +
    (-32 + 4 / 3 * π ^ 2) * hpl [zero, one] x +
    (-16 * x ^ 2 + 16 * x ^ 3 + 32 * x + 2 * π ^ 2 * x ^ 2 - 4 / 3 * π ^ 2 * x +
      2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (32 + 4 / 3 * π ^ 2) * hpl [zero, one, one] x

theorem continuousOn_i8Psi4s134S0 : ContinuousOn i8Psi4s134S0 (Ioc 0 1) := by
  unfold i8Psi4s134S0
  exact (((((i13_cont_coef (p := fun x => -4 * x ^ 4 + 8 * x ^ 3 - 7 / 3 * π ^ 2 * x ^ 3 -
    π ^ 2 * x ^ 4 / 6) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 2 + 8 * x ^ 3 + π ^ 2 * x ^ 3 / 3 +
        7 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -16 * x ^ 2 + 16 * x ^ 3 + 32 * x + 2 * π ^ 2 * x ^ 2 -
        4 / 3 * π ^ 2 * x + 2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one])))

theorem i8Psi4s134_eq_S (x : ℝ) : i8Psi4s134 x = i8Psi4s134S0 x := by
  unfold i8Psi4s134 i8Psi4s134S0 i8Psi4s134N0 i8Psi4s134N1 i8Psi4s134N2 i8Psi4s134N3 i8Psi4s134N4
    i8Psi4s134W
  ring

theorem continuousOn_i8Psi4s134 : ContinuousOn i8Psi4s134 (Ioc 0 1) := by
  rw [show i8Psi4s134 = fun x => i8Psi4s134S0 x from funext i8Psi4s134_eq_S]
  exact continuousOn_i8Psi4s134S0

theorem i8Psi4s134_one : i8Psi4s134 1 = 4 + 32 * zeta3 - 47 / 6 * π ^ 2 + 2 / 9 * π ^ 4 +
    4 / 3 * π ^ 2 * zeta3 := by
  rw [i8Psi4s134_eq_S]
  unfold i8Psi4s134S0
  rw [hpl_zero_one_at_one, hpl_zero_one_one_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s135k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s135k0S0 (x : ℝ) : ℝ :=
    (-59 * x ^ 3 - 2 * x ^ 4) / x ^ 2 +
    (x ^ 4 + 14 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (3 * x ^ 3 + 45 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (4 * x ^ 4 + 32 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-14 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (2 * x ^ 3 + 10 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-24 * x ^ 3 - 20 * x ^ 2 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one] x +
    (4 * x ^ 4 + 8 * x ^ 3) / x ^ 2 * hpl [zero, one, one] x +
    (-12 * x ^ 2 - 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, one] x) +
    (-12 * x ^ 2 - 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one, zero] x) +
    (-24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 8 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one, one] x +
    (-24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 8 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero, one] x +
    (-24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 8 * x ^ 4) / x ^ 2 * hpl [negOne, one, one, zero] x +
    (16) * hpl [zero, negOne, zero, one] x +
    (16) * hpl [zero, zero, one, one] x +
    (16) * hpl [zero, one, zero, one] x +
    (16) * hpl [zero, one, one, zero] x +
    (-16 * x + 8 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero, one] x) +
    (16) * hpl [zero, negOne, zero, one, one] x +
    (16) * hpl [zero, negOne, one, zero, one] x

theorem continuousOn_i8Psi4s135k0S0 : ContinuousOn i8Psi4s135k0S0 (Ioc 0 1) := by
  unfold i8Psi4s135k0S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -59 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 14 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 3 * x ^ 3 + 45 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 32 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -14 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 3 + 10 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 3 - 20 * x ^ 2 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one, one]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero]))).add
      ((i13_cont_coef (p := fun x => -16 * x + 8 * x ^ 3 + 24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero, one])))

/-- Chunk 1 of `i8Psi4s135k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s135k0S1 (x : ℝ) : ℝ :=
    (16) * hpl [zero, negOne, one, one, zero] x +
    (16) * hpl [zero, one, negOne, zero, one] x

theorem continuousOn_i8Psi4s135k0S1 : ContinuousOn i8Psi4s135k0S1 (Ioc 0 1) := by
  unfold i8Psi4s135k0S1
  exact ((continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, one, zero])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero, one])))

theorem i8Psi4s135k0_eq_S (x : ℝ) : i8Psi4s135k0 x = i8Psi4s135k0S0 x + i8Psi4s135k0S1 x := by
  unfold i8Psi4s135k0 i8Psi4s135k0S0 i8Psi4s135k0S1 i8Psi4s135k0N0 i8Psi4s135k0N1 i8Psi4s135k0N2
    i8Psi4s135k0N3 i8Psi4s135k0N4 i8Psi4s135k0W
  ring

theorem continuousOn_i8Psi4s135k0 : ContinuousOn i8Psi4s135k0 (Ioc 0 1) := by
  rw [show i8Psi4s135k0 = fun x => i8Psi4s135k0S0 x +
    i8Psi4s135k0S1 x from funext i8Psi4s135k0_eq_S]
  exact (continuousOn_i8Psi4s135k0S0.add continuousOn_i8Psi4s135k0S1)

theorem i8Psi4s135k0_one : i8Psi4s135k0 1 = -61 - 64 * Li 5 (1 / 2) + 6 * π ^ 2 +
    8 * Real.log 2 ^ 4 + 42 * zeta3 + 192 * Li 4 (1 / 2) - 89 / 90 * π ^ 4 +
    8 / 15 * Real.log 2 ^ 5 + 123 / 4 * zeta5 - 8 * Real.log 2 * π ^ 2 -
    8 / 9 * π ^ 2 * Real.log 2 ^ 3 + 7 / 90 * Real.log 2 * π ^ 4 := by
  rw [i8Psi4s135k0_eq_S]
  unfold i8Psi4s135k0S0 i8Psi4s135k0S1
  rw [hpl_zero_at_one, hpl_zero_one_at_one, hpl_negOne_zero_one_at_one, hpl_zero_one_one_at_one,
    hpl_negOne_zero_one_one_at_one, hpl_negOne_one_zero_one_at_one, hpl_negOne_one_one_zero_at_one,
    hpl_zero_negOne_zero_one_at_one, hpl_zero_zero_one_one_at_one, hpl_zero_one_zero_one_at_one,
    hpl_zero_one_one_zero_at_one, hpl_zero_negOne_zero_one_one_at_one,
    hpl_zero_negOne_one_zero_one_at_one, hpl_zero_negOne_one_one_zero_at_one,
    hpl_zero_one_negOne_zero_one_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s135k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s135k1S0 (x : ℝ) : ℝ :=
    (-x ^ 4 - 48 * x ^ 3) / x ^ 2 +
    (2 * x ^ 4 + 48 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-28 * x ^ 3 - 26 * x ^ 2 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-22 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-24 * x ^ 3 - 20 * x ^ 2 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero] x +
    (4 * x ^ 3 + 28 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (16) * hpl [zero, negOne, one, zero] x +
    (16) * hpl [zero, one, negOne, zero] x +
    (-16 * x + 8 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, one, zero] x) +
    (-16 * x + 8 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one, negOne, zero] x) +
    (16) * hpl [zero, one, negOne, one, zero] x +
    (16) * hpl [zero, one, one, negOne, zero] x

theorem continuousOn_i8Psi4s135k1S0 : ContinuousOn i8Psi4s135k1S0 (Ioc 0 1) := by
  unfold i8Psi4s135k1S0
  exact ((((((((((((i13_cont_coef (p := fun x => -x ^ 4 - 48 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 48 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -28 * x ^ 3 - 26 * x ^ 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -22 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 3 - 20 * x ^ 2 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 3 + 28 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -16 * x + 8 * x ^ 3 + 24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, one, zero]))).add
      ((i13_cont_coef (p := fun x => -16 * x + 8 * x ^ 3 + 24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, negOne, zero])))

theorem i8Psi4s135k1_eq_S (x : ℝ) : i8Psi4s135k1 x = i8Psi4s135k1S0 x := by
  unfold i8Psi4s135k1 i8Psi4s135k1S0 i8Psi4s135k1N0 i8Psi4s135k1N1 i8Psi4s135k1N2 i8Psi4s135k1N3
    i8Psi4s135k1N4 i8Psi4s135k1W
  ring

theorem continuousOn_i8Psi4s135k1 : ContinuousOn i8Psi4s135k1 (Ioc 0 1) := by
  rw [show i8Psi4s135k1 = fun x => i8Psi4s135k1S0 x from funext i8Psi4s135k1_eq_S]
  exact continuousOn_i8Psi4s135k1S0

theorem i8Psi4s135k1_one : i8Psi4s135k1 1 = -49 + 48 * zeta3 + 64 * Li 5 (1 / 2) -
    205 / 4 * zeta5 - 8 / 15 * Real.log 2 ^ 5 - 2 / 9 * π ^ 4 + 14 / 3 * π ^ 2 +
    π ^ 2 * zeta3 / 2 - 4 * Real.log 2 * π ^ 2 - 7 / 90 * Real.log 2 * π ^ 4 +
    8 / 9 * π ^ 2 * Real.log 2 ^ 3 := by
  rw [i8Psi4s135k1_eq_S]
  unfold i8Psi4s135k1S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_negOne_one_zero_at_one,
    hpl_zero_negOne_one_zero_at_one, hpl_zero_one_negOne_zero_at_one,
    hpl_zero_one_negOne_one_zero_at_one, hpl_zero_one_one_negOne_zero_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s135 : ContinuousOn i8Psi4s135 (Ioc 0 1) := by
  rw [show i8Psi4s135 = fun x => i8Psi4s135k0 x + i8Psi4s135k1 x from rfl]
  exact (continuousOn_i8Psi4s135k0.add continuousOn_i8Psi4s135k1)

theorem i8Psi4s135_one : i8Psi4s135 1 = -110 + 8 * Real.log 2 ^ 4 + 90 * zeta3 +
    192 * Li 4 (1 / 2) - 109 / 90 * π ^ 4 - 41 / 2 * zeta5 + 32 / 3 * π ^ 2 + π ^ 2 * zeta3 / 2 -
    12 * Real.log 2 * π ^ 2 := by
  unfold i8Psi4s135
  rw [i8Psi4s135k0_one, i8Psi4s135k1_one]
  ring

/-- Chunk 0 of `i8Psi4s136k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s136k0S0 (x : ℝ) : ℝ :=
    (x ^ 4 + 87 / 2 * x ^ 3) / x ^ 2 +
    (-11 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero] x +
    (-65 / 2 * x ^ 2 - 3 / 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-22 * x ^ 3 - 8 * x ^ 2 - 2 * x ^ 4) / x ^ 2 * hpl [zero, one] x +
    (x ^ 3 + 11 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-x ^ 3 - 9 * x ^ 2 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-8 * x ^ 2 + 2 * x ^ 4 + 12 * x ^ 3) / x ^ 2 * hpl [zero, zero, one] x +
    (-8) * hpl [zero, one, zero] x +
    (-8 * x ^ 3 - 2 * x ^ 4 + 8 * x) / x ^ 2 * hpl [zero, one, one] x +
    (2 * x ^ 3 + 8 * x + 10 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, one] x) +
    (2 * x ^ 3 + 8 * x + 10 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one, zero] x) +
    (-8) * hpl [zero, zero, zero, one] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, zero, one, one] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, one, zero, one] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, one, one, zero] x +
    (-12 * x ^ 2 - 4 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero, one] x) +
    (-8) * hpl [zero, zero, zero, one, one] x +
    (-8) * hpl [zero, zero, one, zero, one] x +
    (-8) * hpl [zero, zero, one, one, zero] x +
    (-8) * hpl [zero, one, zero, zero, one] x

theorem continuousOn_i8Psi4s136k0S0 : ContinuousOn i8Psi4s136k0S0 (Ioc 0 1) := by
  unfold i8Psi4s136k0S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 + 87 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -11 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -65 / 2 * x ^ 2 - 3 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -22 * x ^ 3 - 8 * x ^ 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + 11 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 9 * x ^ 2 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 2 + 2 * x ^ 4 + 12 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 3 - 2 * x ^ 4 + 8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 3 + 8 * x + 10 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 3 + 8 * x + 10 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 4 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero, one])))

theorem i8Psi4s136k0_eq_S (x : ℝ) : i8Psi4s136k0 x = i8Psi4s136k0S0 x := by
  unfold i8Psi4s136k0 i8Psi4s136k0S0 i8Psi4s136k0N0 i8Psi4s136k0N1 i8Psi4s136k0N2 i8Psi4s136k0N3
    i8Psi4s136k0N4 i8Psi4s136k0W
  ring

theorem continuousOn_i8Psi4s136k0 : ContinuousOn i8Psi4s136k0 (Ioc 0 1) := by
  rw [show i8Psi4s136k0 = fun x => i8Psi4s136k0S0 x from funext i8Psi4s136k0_eq_S]
  exact continuousOn_i8Psi4s136k0S0

theorem i8Psi4s136k0_one : i8Psi4s136k0 1 = 89 / 2 - 4 * zeta5 + 20 * zeta3 - 16 / 3 * π ^ 2 -
    13 / 90 * π ^ 4 := by
  rw [i8Psi4s136k0_eq_S]
  unfold i8Psi4s136k0S0
  rw [hpl_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one,
    hpl_zero_one_one_at_one, hpl_zero_zero_zero_one_at_one, hpl_zero_zero_one_one_at_one,
    hpl_zero_one_zero_one_at_one, hpl_zero_one_one_zero_at_one, hpl_zero_zero_zero_one_one_at_one,
    hpl_zero_zero_one_zero_one_at_one, hpl_zero_zero_one_one_zero_at_one,
    hpl_zero_one_zero_zero_one_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s136k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s136k1S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 + 27 * x ^ 3) / x ^ 2 +
    (-x ^ 4 - 27 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (x ^ 4 + 14 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (x ^ 3 + 13 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (2 * x ^ 4 + 12 * x ^ 3) / x ^ 2 * hpl [zero, one, zero] x +
    (-14 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-8) * hpl [zero, zero, one, zero] x +
    (-8) * hpl [zero, one, zero, zero] x +
    (-12 * x ^ 2 - 4 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, one, zero] x) +
    (-12 * x ^ 2 - 4 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, one, zero, zero] x) +
    (-8) * hpl [zero, one, zero, one, zero] x +
    (-8) * hpl [zero, one, one, zero, zero] x

theorem continuousOn_i8Psi4s136k1S0 : ContinuousOn i8Psi4s136k1S0 (Ioc 0 1) := by
  unfold i8Psi4s136k1S0
  exact ((((((((((((i13_cont_coef (p := fun x => x ^ 4 / 2 + 27 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 27 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 14 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + 13 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 12 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -14 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 4 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 4 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero, zero])))

theorem i8Psi4s136k1_eq_S (x : ℝ) : i8Psi4s136k1 x = i8Psi4s136k1S0 x := by
  unfold i8Psi4s136k1 i8Psi4s136k1S0 i8Psi4s136k1N0 i8Psi4s136k1N1 i8Psi4s136k1N2 i8Psi4s136k1N3
    i8Psi4s136k1N4 i8Psi4s136k1W
  ring

theorem continuousOn_i8Psi4s136k1 : ContinuousOn i8Psi4s136k1 (Ioc 0 1) := by
  rw [show i8Psi4s136k1 = fun x => i8Psi4s136k1S0 x from funext i8Psi4s136k1_eq_S]
  exact continuousOn_i8Psi4s136k1S0

theorem i8Psi4s136k1_one : i8Psi4s136k1 1 = 55 / 2 - 28 * zeta3 - 12 * zeta5 +
    4 / 3 * π ^ 2 * zeta3 := by
  rw [i8Psi4s136k1_eq_S]
  unfold i8Psi4s136k1S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_zero_at_one,
    hpl_zero_zero_one_zero_at_one, hpl_zero_one_zero_zero_at_one, hpl_zero_one_zero_one_zero_at_one,
    hpl_zero_one_one_zero_zero_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s136 : ContinuousOn i8Psi4s136 (Ioc 0 1) := by
  rw [show i8Psi4s136 = fun x => i8Psi4s136k0 x + i8Psi4s136k1 x from rfl]
  exact (continuousOn_i8Psi4s136k0.add continuousOn_i8Psi4s136k1)

theorem i8Psi4s136_one : i8Psi4s136 1 = 72 - 16 * zeta5 - 8 * zeta3 - 16 / 3 * π ^ 2 -
    13 / 90 * π ^ 4 + 4 / 3 * π ^ 2 * zeta3 := by
  unfold i8Psi4s136
  rw [i8Psi4s136k0_one, i8Psi4s136k1_one]
  ring

/-- Chunk 0 of `i8Psi4s137` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s137S0 (x : ℝ) : ℝ :=
    (-76 * x ^ 3 - 3 * x ^ 4) / x ^ 2 +
    (2 * x ^ 4 + 28 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (4 * x ^ 3 + 48 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-16 * x ^ 2 + 4 * x ^ 4 + 24 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-28 * x ^ 2 - 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (4 * x ^ 3 + 16 * x + 20 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-16) * hpl [zero, zero, one] x +
    (-16) * hpl [zero, one, zero] x +
    (8 * x ^ 4 + 16 * x + 16 * x ^ 3) / x ^ 2 * hpl [zero, one, one] x +
    (-24 * x ^ 2 - 8 * x ^ 3 + 16 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, one] x) +
    (-24 * x ^ 2 - 8 * x ^ 3 + 16 * x) / x ^ 2 * ((1 - x) * hpl [one, one, zero] x) +
    (-16) * hpl [zero, zero, one, one] x +
    (-16) * hpl [zero, one, zero, one] x +
    (-16) * hpl [zero, one, one, zero] x

theorem continuousOn_i8Psi4s137S0 : ContinuousOn i8Psi4s137S0 (Ioc 0 1) := by
  unfold i8Psi4s137S0
  exact ((((((((((((((i13_cont_coef (p := fun x => -76 * x ^ 3 - 3 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 28 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 3 + 48 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -16 * x ^ 2 + 4 * x ^ 4 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -28 * x ^ 2 - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 3 + 16 * x + 20 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => 8 * x ^ 4 + 16 * x + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 8 * x ^ 3 + 16 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 8 * x ^ 3 + 16 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero])))

theorem i8Psi4s137_eq_S (x : ℝ) : i8Psi4s137 x = i8Psi4s137S0 x := by
  unfold i8Psi4s137 i8Psi4s137S0 i8Psi4s137N0 i8Psi4s137N1 i8Psi4s137N2 i8Psi4s137N3 i8Psi4s137N4
    i8Psi4s137W
  ring

theorem continuousOn_i8Psi4s137 : ContinuousOn i8Psi4s137 (Ioc 0 1) := by
  rw [show i8Psi4s137 = fun x => i8Psi4s137S0 x from funext i8Psi4s137_eq_S]
  exact continuousOn_i8Psi4s137S0

theorem i8Psi4s137_one : i8Psi4s137 1 = -79 + 2 * π ^ 2 + 56 * zeta3 + 2 / 45 * π ^ 4 := by
  rw [i8Psi4s137_eq_S]
  unfold i8Psi4s137S0
  rw [hpl_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one,
    hpl_zero_one_one_at_one, hpl_zero_zero_one_one_at_one, hpl_zero_one_zero_one_at_one,
    hpl_zero_one_one_zero_at_one]
  norm_num
  ring

end QED.ThreeLoopD
