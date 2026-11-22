/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4V3

/-!
# Set (d), master `I₈`: continuity and values at `1` of the sub-pieces 75 to 83 of `Ψ₄`

Each sub-piece `Ψ₄⁽ⁿ⁾` is continuous on `(0, 1]` (the words beginning with `1` carry a factor
`1 - ξ`), and its value at `ξ = 1` follows from the values of the harmonic polylogarithms at `1`.

## Main results

* `QED.ThreeLoopD.continuousOn_i8Psi4s75`, `QED.ThreeLoopD.i8Psi4s75_one` and their
  companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- Chunk 0 of `i8Psi4s75k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s75k0S0 (x : ℝ) : ℝ :=
    (13 / 8 * x ^ 4 + 41 / 4 * x ^ 3) / x ^ 2 +
    (-10 * x ^ 2 - 6 * x - 6 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [negOne] x +
    (9) * hpl [zero] x +
    (-3 * x - 25 / 4 * x ^ 2 - 5 / 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-2 - 2 * x ^ 4 + 4 * x ^ 2) / x ^ 2 * hpl [negOne, one] x +
    (-4 * x + 2 * x ^ 2 + 2 * x ^ 4 + 4 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (-x - 7 * x ^ 3 - 2 * x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [zero, one] x +
    (-2 - 2 * x + 2 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (-1 + x ^ 4 - 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [negOne, zero, one] x +
    (-4 + 4 * x ^ 4) / x ^ 2 * hpl [zero, negOne, one] x +
    (4) * hpl [zero, zero, negOne] x +
    (7) * hpl [zero, zero, one] x +
    (-4 + 4 * x ^ 4) / x ^ 2 * hpl [zero, one, negOne] x +
    (-4 - 4 * x - 4 * x ^ 2 - 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (-2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero, one] x +
    (-16) * hpl [zero, zero, negOne, one] x +
    (-16) * hpl [zero, zero, one, negOne] x +
    (-16) * hpl [zero, one, zero, negOne] x

theorem continuousOn_i8Psi4s75k0S0 : ContinuousOn i8Psi4s75k0S0 (Ioc 0 1) := by
  unfold i8Psi4s75k0S0
  exact ((((((((((((((((((i13_cont_coef (p := fun x => 13 / 8 * x ^ 4 +
    41 / 4 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -10 * x ^ 2 - 6 * x - 6 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -3 * x - 25 / 4 * x ^ 2 - 5 / 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -2 - 2 * x ^ 4 + 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -4 * x + 2 * x ^ 2 + 2 * x ^ 4 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -x - 7 * x ^ 3 - 2 * x ^ 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -2 - 2 * x + 2 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4 - 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -4 + 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -4 + 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -4 - 4 * x - 4 * x ^ 2 - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne])))

theorem i8Psi4s75k0_eq_S (x : ℝ) : i8Psi4s75k0 x = i8Psi4s75k0S0 x := by
  unfold i8Psi4s75k0 i8Psi4s75k0S0 i8Psi4s75k0N0 i8Psi4s75k0N1 i8Psi4s75k0N2 i8Psi4s75k0N3
    i8Psi4s75k0N4 i8Psi4s75k0W
  ring

theorem continuousOn_i8Psi4s75k0 : ContinuousOn i8Psi4s75k0 (Ioc 0 1) := by
  rw [show i8Psi4s75k0 = fun x => i8Psi4s75k0S0 x from funext i8Psi4s75k0_eq_S]
  exact continuousOn_i8Psi4s75k0S0

theorem i8Psi4s75k0_one : i8Psi4s75k0 1 = 95 / 8 - 24 * Real.log 2 + 10 * zeta3 +
    32 * Li 4 (1 / 2) - 191 / 360 * π ^ 4 - 17 / 12 * π ^ 2 + 4 / 3 * Real.log 2 ^ 4 +
    28 * Real.log 2 * zeta3 - 4 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s75k0_eq_S]
  unfold i8Psi4s75k0S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one,
    hpl_zero_one_at_one, hpl_negOne_zero_one_at_one, hpl_zero_negOne_one_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_negOne_zero_one_at_one, hpl_zero_zero_negOne_one_at_one,
    hpl_zero_zero_one_negOne_at_one, hpl_zero_one_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s75k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s75k1S0 (x : ℝ) : ℝ :=
    (48 * x ^ 3 + 3 / 4 * x ^ 4) / x ^ 2 +
    (-x - 17 * x ^ 3 - 35 / 2 * x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [negOne] x +
    (-16 * x ^ 3 + 2 * x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [zero] x +
    (-x - 31 / 2 * x ^ 2 - x ^ 3 / 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x ^ 4 / 2 - x + 9 * x ^ 3 + 15 / 2 * x ^ 2) / x ^ 2 * hpl [negOne, zero] x +
    (-1 - x ^ 4 - 30 * x ^ 2 - 16 * x - 16 * x ^ 3) / x ^ 2 * hpl [negOne, one] x +
    (17) * hpl [zero, negOne] x +
    (2) * hpl [zero, zero] x +
    (15) * hpl [zero, one] x +
    (-1 + x ^ 3 - 17 * x + 17 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (x ^ 3 / 2 - x + 15 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-1 + x ^ 4 - 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [negOne, one, zero] x +
    (9) * hpl [zero, negOne, zero] x +
    (-2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [zero, negOne, one] x +
    (-2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [zero, one, negOne] x +
    (7) * hpl [zero, one, zero] x +
    (-1 - x ^ 3 - 9 * x - 9 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (-2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, one, zero] x +
    (-4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne, one] x +
    (-4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, zero, one, negOne] x

theorem continuousOn_i8Psi4s75k1S0 : ContinuousOn i8Psi4s75k1S0 (Ioc 0 1) := by
  unfold i8Psi4s75k1S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => 48 * x ^ 3 +
    3 / 4 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -x - 17 * x ^ 3 - 35 / 2 * x ^ 2 -
        x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -16 * x ^ 3 + 2 * x ^ 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x - 31 / 2 * x ^ 2 - x ^ 3 / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - x + 9 * x ^ 3 + 15 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 4 - 30 * x ^ 2 - 16 * x -
        16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 3 - 17 * x + 17 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 - x + 15 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4 - 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 3 - 9 * x - 9 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one]))).add
      ((i13_cont_coef (p := fun x => -4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne])))

/-- Chunk 1 of `i8Psi4s75k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s75k1S1 (x : ℝ) : ℝ :=
    (-2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, one, negOne, zero] x

theorem continuousOn_i8Psi4s75k1S1 : ContinuousOn i8Psi4s75k1S1 (Ioc 0 1) := by
  unfold i8Psi4s75k1S1
  exact ((i13_cont_coef (p := fun x => -2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))

theorem i8Psi4s75k1_eq_S (x : ℝ) : i8Psi4s75k1 x = i8Psi4s75k1S0 x + i8Psi4s75k1S1 x := by
  unfold i8Psi4s75k1 i8Psi4s75k1S0 i8Psi4s75k1S1 i8Psi4s75k1N0 i8Psi4s75k1N1 i8Psi4s75k1N2
    i8Psi4s75k1N3 i8Psi4s75k1N4 i8Psi4s75k1W
  ring

theorem continuousOn_i8Psi4s75k1 : ContinuousOn i8Psi4s75k1 (Ioc 0 1) := by
  rw [show i8Psi4s75k1 = fun x => i8Psi4s75k1S0 x + i8Psi4s75k1S1 x from funext i8Psi4s75k1_eq_S]
  exact (continuousOn_i8Psi4s75k1S0.add continuousOn_i8Psi4s75k1S1)

theorem i8Psi4s75k1_one : i8Psi4s75k1 1 = 195 / 4 - 80 * Li 4 (1 / 2) - 36 * Real.log 2 +
    32 * Real.log 2 ^ 2 - 55 / 2 * zeta3 - 11 / 4 * π ^ 2 - 10 / 3 * Real.log 2 ^ 4 +
    37 / 36 * π ^ 4 - 70 * Real.log 2 * zeta3 + 10 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s75k1_eq_S]
  unfold i8Psi4s75k1S0 i8Psi4s75k1S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_negOne_one_at_one,
    hpl_zero_negOne_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_negOne_one_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_negOne_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_zero_at_one, hpl_zero_negOne_one_zero_at_one, hpl_zero_zero_negOne_one_at_one,
    hpl_zero_zero_one_negOne_at_one, hpl_zero_one_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s75k2` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s75k2S0 (x : ℝ) : ℝ :=
    (5 / 8 * x ^ 4 + 93 / 2 * x ^ 3) / x ^ 2 +
    (-x ^ 4 - 43 * x ^ 2 - 38 * x ^ 3 - 6 * x) / x ^ 2 * hpl [negOne] x +
    (6 * x ^ 2 - 19 / 2 * x ^ 3 - x ^ 4 / 4) / x ^ 2 * hpl [zero] x +
    (x ^ 4 / 2 - 2 * x + 10 * x ^ 3 + 15 / 2 * x ^ 2) / x ^ 2 * hpl [negOne, zero] x +
    (-6 * x + 2 * x ^ 4 + 38 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (2) * hpl [zero, zero] x +
    (-x ^ 4 - 10 * x ^ 3 - 2 * x) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-20 * x ^ 3 - 4 * x - 2 * x ^ 4 + 18 * x ^ 2) / x ^ 2 * hpl [zero, zero, negOne] x +
    (-2 - 18 * x - 18 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (10) * hpl [zero, zero, negOne, zero] x +
    (20) * hpl [zero, zero, zero, negOne] x +
    (-4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, one, zero, negOne] x +
    (-2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne, zero] x) +
    (-4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, zero, negOne] x)

theorem continuousOn_i8Psi4s75k2S0 : ContinuousOn i8Psi4s75k2S0 (Ioc 0 1) := by
  unfold i8Psi4s75k2S0
  exact ((((((((((((((i13_cont_coef (p := fun x => 5 / 8 * x ^ 4 +
    93 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 43 * x ^ 2 - 38 * x ^ 3 - 6 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 6 * x ^ 2 - 19 / 2 * x ^ 3 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - 2 * x + 10 * x ^ 3 +
        15 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -6 * x + 2 * x ^ 4 + 38 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 10 * x ^ 3 - 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -20 * x ^ 3 - 4 * x - 2 * x ^ 4 +
        18 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 - 18 * x - 18 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero, negOne])))

theorem i8Psi4s75k2_eq_S (x : ℝ) : i8Psi4s75k2 x = i8Psi4s75k2S0 x := by
  unfold i8Psi4s75k2 i8Psi4s75k2S0 i8Psi4s75k2N0 i8Psi4s75k2N1 i8Psi4s75k2N2 i8Psi4s75k2N3
    i8Psi4s75k2N4 i8Psi4s75k2W
  ring

theorem continuousOn_i8Psi4s75k2 : ContinuousOn i8Psi4s75k2 (Ioc 0 1) := by
  rw [show i8Psi4s75k2 = fun x => i8Psi4s75k2S0 x from funext i8Psi4s75k2_eq_S]
  exact continuousOn_i8Psi4s75k2S0

theorem i8Psi4s75k2_one : i8Psi4s75k2 1 = 377 / 8 - 88 * Real.log 2 + 160 * Li 4 (1 / 2) -
    149 / 72 * π ^ 4 + 3 / 2 * π ^ 2 + 20 / 3 * Real.log 2 ^ 4 + 27 / 2 * zeta3 +
    140 * Real.log 2 * zeta3 - 20 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s75k2_eq_S]
  unfold i8Psi4s75k2S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_at_one,
    hpl_zero_one_zero_negOne_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s75 : ContinuousOn i8Psi4s75 (Ioc 0 1) := by
  rw [show i8Psi4s75 = fun x => i8Psi4s75k0 x + i8Psi4s75k1 x + i8Psi4s75k2 x from rfl]
  exact ((continuousOn_i8Psi4s75k0.add continuousOn_i8Psi4s75k1).add continuousOn_i8Psi4s75k2)

theorem i8Psi4s75_one : i8Psi4s75 1 = 431 / 4 - 148 * Real.log 2 - 4 * zeta3 +
    32 * Real.log 2 ^ 2 + 112 * Li 4 (1 / 2) - 283 / 180 * π ^ 4 - 8 / 3 * π ^ 2 +
    14 / 3 * Real.log 2 ^ 4 + 98 * Real.log 2 * zeta3 - 14 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  unfold i8Psi4s75
  rw [i8Psi4s75k0_one, i8Psi4s75k1_one, i8Psi4s75k2_one]
  ring

/-- Chunk 0 of `i8Psi4s76` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s76S0 (x : ℝ) : ℝ :=
    (x ^ 3 + 22 * x + 27 / 8 * x ^ 4 - π ^ 2 * x / 3 + π ^ 2 * x ^ 3 / 3 +
      π ^ 2 * x ^ 4 / 12) / x ^ 2 +
    (-x ^ 3 + 22 * x - 27 / 4 * x ^ 4 - π ^ 2 * x / 3 - π ^ 2 * x ^ 3 / 3 -
      π ^ 2 * x ^ 4 / 6) / x ^ 2 * hpl [zero] x +
    (x ^ 4 - x ^ 2 - 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (6 * x ^ 3 + 12 * x ^ 2 + 14 * x + 9 / 2 * x ^ 4 +
      π ^ 2 * x ^ 2 / 3) / x ^ 2 * hpl [zero, zero] x +
    (-12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-4 * x - 4 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero] x +
    (3 * x ^ 4 + 6 * x + 6 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero] x +
    (8) * hpl [zero, negOne, zero, zero] x +
    (4) * hpl [zero, zero, negOne, zero] x +
    (-6) * hpl [zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s76S0 : ContinuousOn i8Psi4s76S0 (Ioc 0 1) := by
  unfold i8Psi4s76S0
  exact ((((((((((i13_cont_coef (p := fun x => x ^ 3 + 22 * x + 27 / 8 * x ^ 4 - π ^ 2 * x / 3 +
    π ^ 2 * x ^ 3 / 3 + π ^ 2 * x ^ 4 / 12) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -x ^ 3 + 22 * x - 27 / 4 * x ^ 4 - π ^ 2 * x / 3 -
        π ^ 2 * x ^ 3 / 3 - π ^ 2 * x ^ 4 / 6) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - x ^ 2 - 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 6 * x ^ 3 + 12 * x ^ 2 + 14 * x + 9 / 2 * x ^ 4 +
        π ^ 2 * x ^ 2 / 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x - 4 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 3 * x ^ 4 + 6 * x + 6 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero])))

theorem i8Psi4s76_eq_S (x : ℝ) : i8Psi4s76 x = i8Psi4s76S0 x := by
  unfold i8Psi4s76 i8Psi4s76S0 i8Psi4s76N0 i8Psi4s76N1 i8Psi4s76N2 i8Psi4s76N3 i8Psi4s76N4
    i8Psi4s76W
  ring

theorem continuousOn_i8Psi4s76 : ContinuousOn i8Psi4s76 (Ioc 0 1) := by
  rw [show i8Psi4s76 = fun x => i8Psi4s76S0 x from funext i8Psi4s76_eq_S]
  exact continuousOn_i8Psi4s76S0

theorem i8Psi4s76_one : i8Psi4s76 1 = 211 / 8 - 9 * zeta3 + π ^ 2 / 12 + 7 / 60 * π ^ 4 := by
  rw [i8Psi4s76_eq_S]
  unfold i8Psi4s76S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s77` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s77S0 (x : ℝ) : ℝ :=
    (-149 / 8 * x + 17 / 4 * x ^ 4 + 483 / 8 * x ^ 3 + π ^ 2 * x / 4 + π ^ 2 * x ^ 4 / 12 +
      13 / 12 * π ^ 2 * x ^ 3) / x ^ 2 +
    (-27 / 8 - 23 * x - 23 * x ^ 3 - 157 / 4 * x ^ 2 - 27 / 8 * x ^ 4 + π ^ 2 / 12 -
      2 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 12 + 2 / 3 * π ^ 2 * x) / x ^ 2 * hpl [negOne] x +
    (-163 / 4 * x ^ 3 - 61 / 4 * x - 41 / 8 * x ^ 4 + 157 / 8 * x ^ 2 - 7 / 12 * π ^ 2 * x ^ 2 -
      π ^ 2 * x ^ 3 / 2 - π ^ 2 * x ^ 4 / 12 + π ^ 2 * x / 6) / x ^ 2 * hpl [zero] x +
    (-27 / 4 - 20 * x + 15 * x ^ 2 + 36 * x ^ 3 + π ^ 2 / 6 + 31 / 4 * x ^ 4 + π ^ 2 * x ^ 2 +
      π ^ 2 * x ^ 4 / 6 + 2 / 3 * π ^ 2 * x +
      2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (-27 / 4 - 23 * x + 23 * x ^ 3 + π ^ 2 / 6 + 27 / 4 * x ^ 4 + π ^ 2 * x ^ 4 / 6 +
      2 / 3 * π ^ 2 * x + 2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (-17 / 2 * x + 5 / 2 * x ^ 4 + 25 / 2 * x ^ 3 + 53 / 4 * x ^ 2 -
      π ^ 2 * x ^ 2 / 2) / x ^ 2 * hpl [zero, zero] x +
    (2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (1 - x ^ 4 - 8 * x ^ 3 + 8 * x) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (-11 / 2 - 36 * x ^ 2 - 28 * x ^ 3 - 20 * x -
      13 / 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-11 / 2 - 30 * x ^ 2 - 22 * x - 22 * x ^ 3 -
      11 / 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-11 / 2 - 24 * x - 23 * x ^ 2 - 16 * x ^ 3 -
      9 / 2 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne] x +
    (-3 * x + 9 * x ^ 3 + 3 / 2 * x ^ 4 + 29 / 2 * x ^ 2) / x ^ 2 * hpl [zero, zero, zero] x +
    (8 + 8 * x ^ 4 + 32 * x + 32 * x ^ 3 +
      48 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero, zero] x +
    (6 + 6 * x ^ 4 + 24 * x + 24 * x ^ 3 +
      36 * x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne, zero] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
      24 * x ^ 2) / x ^ 2 * hpl [negOne, zero, zero, negOne] x +
    (-3 - 18 * x ^ 2 - 12 * x - 12 * x ^ 3 - 3 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero, zero] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3) / x ^ 2 * hpl [zero, negOne, negOne, zero] x +
    (2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero, negOne] x +
    (-3 - 24 * x ^ 2 - 12 * x - 12 * x ^ 3 - 3 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero, zero] x +
    (-3 - 18 * x ^ 2 - 12 * x - 12 * x ^ 3 - 3 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne, zero] x

theorem continuousOn_i8Psi4s77S0 : ContinuousOn i8Psi4s77S0 (Ioc 0 1) := by
  unfold i8Psi4s77S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -149 / 8 * x + 17 / 4 * x ^ 4 +
    483 / 8 * x ^ 3 + π ^ 2 * x / 4 + π ^ 2 * x ^ 4 / 12 +
    13 / 12 * π ^ 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -27 / 8 - 23 * x - 23 * x ^ 3 - 157 / 4 * x ^ 2 -
        27 / 8 * x ^ 4 + π ^ 2 / 12 - 2 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 12 +
        2 / 3 * π ^ 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -163 / 4 * x ^ 3 - 61 / 4 * x - 41 / 8 * x ^ 4 +
        157 / 8 * x ^ 2 - 7 / 12 * π ^ 2 * x ^ 2 - π ^ 2 * x ^ 3 / 2 - π ^ 2 * x ^ 4 / 12 +
        π ^ 2 * x / 6) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -27 / 4 - 20 * x + 15 * x ^ 2 + 36 * x ^ 3 + π ^ 2 / 6 +
        31 / 4 * x ^ 4 + π ^ 2 * x ^ 2 + π ^ 2 * x ^ 4 / 6 + 2 / 3 * π ^ 2 * x +
        2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -27 / 4 - 23 * x + 23 * x ^ 3 + π ^ 2 / 6 + 27 / 4 * x ^ 4 +
        π ^ 2 * x ^ 4 / 6 + 2 / 3 * π ^ 2 * x + 2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -17 / 2 * x + 5 / 2 * x ^ 4 + 25 / 2 * x ^ 3 +
        53 / 4 * x ^ 2 - π ^ 2 * x ^ 2 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4 - 8 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -11 / 2 - 36 * x ^ 2 - 28 * x ^ 3 - 20 * x -
        13 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -11 / 2 - 30 * x ^ 2 - 22 * x - 22 * x ^ 3 -
        11 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -11 / 2 - 24 * x - 23 * x ^ 2 - 16 * x ^ 3 -
        9 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -3 * x + 9 * x ^ 3 + 3 / 2 * x ^ 4 +
        29 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 8 + 8 * x ^ 4 + 32 * x + 32 * x ^ 3 +
        48 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 6 + 6 * x ^ 4 + 24 * x + 24 * x ^ 3 +
        36 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -3 - 18 * x ^ 2 - 12 * x - 12 * x ^ 3 -
        3 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -3 - 24 * x ^ 2 - 12 * x - 12 * x ^ 3 -
        3 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -3 - 18 * x ^ 2 - 12 * x - 12 * x ^ 3 -
        3 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero])))

/-- Chunk 1 of `i8Psi4s77` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s77S1 (x : ℝ) : ℝ :=
    (-3 - 12 * x - 12 * x ^ 2 - 12 * x ^ 3 - 3 * x ^ 4) / x ^ 2 * hpl [zero, zero, zero, negOne] x +
    (9) * hpl [zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s77S1 : ContinuousOn i8Psi4s77S1 (Ioc 0 1) := by
  unfold i8Psi4s77S1
  exact (((i13_cont_coef (p := fun x => -3 - 12 * x - 12 * x ^ 2 - 12 * x ^ 3 -
    3 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero])))

theorem i8Psi4s77_eq_S (x : ℝ) : i8Psi4s77 x = i8Psi4s77S0 x + i8Psi4s77S1 x := by
  unfold i8Psi4s77 i8Psi4s77S0 i8Psi4s77S1 i8Psi4s77N0 i8Psi4s77N1 i8Psi4s77N2 i8Psi4s77N3
    i8Psi4s77N4 i8Psi4s77W i8Psi4s77N1c0 i8Psi4s77N1c1 i8Psi4s77N3c0 i8Psi4s77N3c1 i8Psi4s77N4c0
    i8Psi4s77N4c1
  ring

theorem continuousOn_i8Psi4s77 : ContinuousOn i8Psi4s77 (Ioc 0 1) := by
  rw [show i8Psi4s77 = fun x => i8Psi4s77S0 x + i8Psi4s77S1 x from funext i8Psi4s77_eq_S]
  exact (continuousOn_i8Psi4s77S0.add continuousOn_i8Psi4s77S1)

theorem i8Psi4s77_one : i8Psi4s77 1 = 46 - 92 * Real.log 2 + 2 * Real.log 2 ^ 4 +
    48 * Li 4 (1 / 2) - 79 / 120 * π ^ 4 - 5 / 4 * π ^ 2 + 3 / 4 * zeta3 -
    2 * π ^ 2 * Real.log 2 ^ 2 + 42 * Real.log 2 * zeta3 := by
  rw [i8Psi4s77_eq_S]
  unfold i8Psi4s77S0 i8Psi4s77S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_negOne_zero_at_one, hpl_negOne_zero_negOne_at_one,
    hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_zero_zero_at_one, hpl_negOne_negOne_zero_zero_at_one,
    hpl_negOne_zero_negOne_zero_at_one, hpl_negOne_zero_zero_negOne_at_one,
    hpl_negOne_zero_zero_zero_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_zero_negOne_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_at_one,
    hpl_zero_zero_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s78` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s78S0 (x : ℝ) : ℝ :=
    (-39 / 2 * x ^ 3 - 27 / 4 * x ^ 4 - π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 6) / x ^ 2 +
    (-28 * x ^ 2 + 3 * x ^ 4 + 17 * x ^ 3 + 2 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (28 * x + 5 / 2 * x ^ 2 + 21 / 2 * x ^ 3 + π ^ 2 * x ^ 2 - 2 / 3 * π ^ 2 * x +
      π ^ 2 * x ^ 3 / 3) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-12 * x ^ 3 - 10 * x ^ 2 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (x ^ 4 - 12 * x ^ 2 + 6 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (5 * x ^ 4 + 8 * x ^ 3 + 12 * x + 16 * x ^ 2 +
      2 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, one] x +
    (-13 * x ^ 2 - 5 * x ^ 3 + 12 * x) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one] x +
    (-12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero] x +
    (8) * hpl [zero, negOne, zero] x +
    (-4) * hpl [zero, zero, zero] x +
    (2 * x ^ 4 + 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [zero, zero, one] x +
    (2 * x ^ 4 + 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [zero, one, zero] x +
    (-8 * x + 4 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (-6 * x ^ 2 - 2 * x ^ 3 + 4 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (8) * hpl [zero, negOne, zero, one] x +
    (8) * hpl [zero, negOne, one, zero] x +
    (-4) * hpl [zero, zero, zero, one] x +
    (-4) * hpl [zero, zero, one, zero] x +
    (8) * hpl [zero, one, negOne, zero] x

theorem continuousOn_i8Psi4s78S0 : ContinuousOn i8Psi4s78S0 (Ioc 0 1) := by
  unfold i8Psi4s78S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -39 / 2 * x ^ 3 - 27 / 4 * x ^ 4 -
    π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 6) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -28 * x ^ 2 + 3 * x ^ 4 + 17 * x ^ 3 +
        2 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 28 * x + 5 / 2 * x ^ 2 + 21 / 2 * x ^ 3 + π ^ 2 * x ^ 2 -
        2 / 3 * π ^ 2 * x + π ^ 2 * x ^ 3 / 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 10 * x ^ 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 12 * x ^ 2 + 6 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 5 * x ^ 4 + 8 * x ^ 3 + 12 * x + 16 * x ^ 2 +
        2 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -13 * x ^ 2 - 5 * x ^ 3 + 12 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x + 4 * x ^ 3 + 12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -6 * x ^ 2 - 2 * x ^ 3 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero])))

/-- Chunk 1 of `i8Psi4s78` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s78S1 (x : ℝ) : ℝ :=
    (-4) * hpl [zero, one, zero, zero] x

theorem continuousOn_i8Psi4s78S1 : ContinuousOn i8Psi4s78S1 (Ioc 0 1) := by
  unfold i8Psi4s78S1
  exact (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero]))

theorem i8Psi4s78_eq_S (x : ℝ) : i8Psi4s78 x = i8Psi4s78S0 x + i8Psi4s78S1 x := by
  unfold i8Psi4s78 i8Psi4s78S0 i8Psi4s78S1 i8Psi4s78N0 i8Psi4s78N1 i8Psi4s78N2 i8Psi4s78N3
    i8Psi4s78N4 i8Psi4s78W
  ring

theorem continuousOn_i8Psi4s78 : ContinuousOn i8Psi4s78 (Ioc 0 1) := by
  rw [show i8Psi4s78 = fun x => i8Psi4s78S0 x + i8Psi4s78S1 x from funext i8Psi4s78_eq_S]
  exact (continuousOn_i8Psi4s78S0.add continuousOn_i8Psi4s78S1)

theorem i8Psi4s78_one : i8Psi4s78 1 = -105 / 4 + 30 * zeta3 - π ^ 4 / 36 + 23 / 3 * π ^ 2 -
    8 * Real.log 2 * π ^ 2 := by
  rw [i8Psi4s78_eq_S]
  unfold i8Psi4s78S0 i8Psi4s78S1
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one,
    hpl_negOne_zero_one_at_one, hpl_negOne_one_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one,
    hpl_zero_negOne_zero_one_at_one, hpl_zero_negOne_one_zero_at_one, hpl_zero_zero_zero_one_at_one,
    hpl_zero_zero_one_zero_at_one, hpl_zero_one_negOne_zero_at_one, hpl_zero_one_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s79` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s79S0 (x : ℝ) : ℝ :=
    (-4 * x ^ 4 - 8 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 6) / x ^ 2 +
    (-8 * x - 4 * x ^ 2 + 4 * x ^ 4 + 8 * x ^ 3 + π ^ 2 * x / 3 + π ^ 2 * x ^ 4 / 6 +
      5 / 3 * π ^ 2 * x ^ 3 + 11 / 6 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (16 - 2 / 3 * π ^ 2) * hpl [zero] x +
    (-8 * x - 4 * x ^ 2 + 4 * x ^ 3 + π ^ 2 * x / 3 + π ^ 2 * x ^ 3 / 6 +
      7 / 6 * π ^ 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-8 + 8 * x ^ 4 + π ^ 2 / 3 + 2 * π ^ 2 * x ^ 2 + π ^ 2 * x ^ 4 / 3 + 4 / 3 * π ^ 2 * x +
      4 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [negOne, one] x +
    (8 - 5 / 3 * π ^ 2) * hpl [zero, negOne] x +
    (-8 - π ^ 2) * hpl [zero, one] x +
    (-8 - 8 * x - 8 * x ^ 2 - 8 * x ^ 3 + π ^ 2 / 3 - 5 / 3 * π ^ 2 * x ^ 2 - π ^ 2 * x ^ 3 / 3 +
      5 / 3 * π ^ 2 * x) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (-32) * hpl [zero, negOne, one] x +
    (-32) * hpl [zero, one, negOne] x

theorem continuousOn_i8Psi4s79S0 : ContinuousOn i8Psi4s79S0 (Ioc 0 1) := by
  unfold i8Psi4s79S0
  exact ((((((((((i13_cont_coef (p := fun x => -4 * x ^ 4 - 8 / 3 * π ^ 2 * x ^ 3 -
    π ^ 2 * x ^ 4 / 6) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -8 * x - 4 * x ^ 2 + 4 * x ^ 4 + 8 * x ^ 3 + π ^ 2 * x / 3 +
        π ^ 2 * x ^ 4 / 6 + 5 / 3 * π ^ 2 * x ^ 3 + 11 / 6 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -8 * x - 4 * x ^ 2 + 4 * x ^ 3 + π ^ 2 * x / 3 +
        π ^ 2 * x ^ 3 / 6 + 7 / 6 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -8 + 8 * x ^ 4 + π ^ 2 / 3 + 2 * π ^ 2 * x ^ 2 +
        π ^ 2 * x ^ 4 / 3 + 4 / 3 * π ^ 2 * x + 4 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -8 - 8 * x - 8 * x ^ 2 - 8 * x ^ 3 + π ^ 2 / 3 -
        5 / 3 * π ^ 2 * x ^ 2 - π ^ 2 * x ^ 3 / 3 + 5 / 3 * π ^ 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne])))

theorem i8Psi4s79_eq_S (x : ℝ) : i8Psi4s79 x = i8Psi4s79S0 x := by
  unfold i8Psi4s79 i8Psi4s79S0 i8Psi4s79N0 i8Psi4s79N1 i8Psi4s79N2 i8Psi4s79N3 i8Psi4s79N4
    i8Psi4s79W
  ring

theorem continuousOn_i8Psi4s79 : ContinuousOn i8Psi4s79 (Ioc 0 1) := by
  rw [show i8Psi4s79 = fun x => i8Psi4s79S0 x from funext i8Psi4s79_eq_S]
  exact continuousOn_i8Psi4s79S0

theorem i8Psi4s79_one : i8Psi4s79 1 = -4 - 20 * zeta3 - 7 / 2 * π ^ 2 + 5 / 36 * π ^ 4 +
    4 * Real.log 2 * π ^ 2 - 8 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s79_eq_S]
  unfold i8Psi4s79S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one,
    hpl_zero_one_at_one, hpl_zero_negOne_one_at_one, hpl_zero_one_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s80k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s80k0S0 (x : ℝ) : ℝ :=
    (-67 * x ^ 3 - 3 / 2 * x ^ 4) / x ^ 2 +
    (x ^ 4 / 2 + 13 * x ^ 3 + 25 / 2 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (x ^ 4 + 22 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (3 / 2 * x ^ 3 + 65 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x ^ 4 + 4 * x + 12 * x ^ 3 + 15 * x ^ 2) / x ^ 2 * hpl [negOne, one] x +
    (-4) * hpl [zero, negOne] x +
    (-4 * x ^ 2 + 2 * x ^ 4 + 20 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-x ^ 3 - 13 * x ^ 2 + 4 * x) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (-22 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-24 * x ^ 3 - 12 * x ^ 2 - 4 * x ^ 4 + 8 * x) / x ^ 2 * hpl [negOne, zero, one] x +
    (-24 * x ^ 3 - 12 * x ^ 2 - 4 * x ^ 4 + 8 * x) / x ^ 2 * hpl [negOne, one, zero] x +
    (-12 * x ^ 3 - 2 * x ^ 4 + 4 * x) / x ^ 2 * hpl [zero, negOne, one] x +
    (-8) * hpl [zero, zero, one] x +
    (-12 * x ^ 3 - 2 * x ^ 4 + 4 * x) / x ^ 2 * hpl [zero, one, negOne] x +
    (-8) * hpl [zero, one, zero] x +
    (8 + 8 * x ^ 4 + 32 * x + 32 * x ^ 3 + 48 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero, one] x +
    (8 + 8 * x ^ 4 + 32 * x + 32 * x ^ 3 + 48 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, one, zero] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne, one] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * hpl [negOne, zero, one, negOne] x +
    (-24) * hpl [zero, negOne, zero, one] x

theorem continuousOn_i8Psi4s80k0S0 : ContinuousOn i8Psi4s80k0S0 (Ioc 0 1) := by
  unfold i8Psi4s80k0S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -67 * x ^ 3 -
    3 / 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 13 * x ^ 3 + 25 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 22 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 3 / 2 * x ^ 3 + 65 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 4 * x + 12 * x ^ 3 + 15 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 2 + 2 * x ^ 4 + 20 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 13 * x ^ 2 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -22 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 3 - 12 * x ^ 2 - 4 * x ^ 4 +
        8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 3 - 12 * x ^ 2 - 4 * x ^ 4 +
        8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 2 * x ^ 4 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 2 * x ^ 4 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => 8 + 8 * x ^ 4 + 32 * x + 32 * x ^ 3 +
        48 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, one]))).add
      ((i13_cont_coef (p := fun x => 8 + 8 * x ^ 4 + 32 * x + 32 * x ^ 3 +
        48 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, one, zero]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, one]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one])))

/-- Chunk 1 of `i8Psi4s80k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s80k0S1 (x : ℝ) : ℝ :=
    (-24) * hpl [zero, negOne, one, zero] x +
    (-12) * hpl [zero, zero, negOne, one] x +
    (-12) * hpl [zero, zero, one, negOne] x

theorem continuousOn_i8Psi4s80k0S1 : ContinuousOn i8Psi4s80k0S1 (Ioc 0 1) := by
  unfold i8Psi4s80k0S1
  exact (((continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne])))

theorem i8Psi4s80k0_eq_S (x : ℝ) : i8Psi4s80k0 x = i8Psi4s80k0S0 x + i8Psi4s80k0S1 x := by
  unfold i8Psi4s80k0 i8Psi4s80k0S0 i8Psi4s80k0S1 i8Psi4s80k0N0 i8Psi4s80k0N1 i8Psi4s80k0N2
    i8Psi4s80k0N3 i8Psi4s80k0N4 i8Psi4s80k0W
  ring

theorem continuousOn_i8Psi4s80k0 : ContinuousOn i8Psi4s80k0 (Ioc 0 1) := by
  rw [show i8Psi4s80k0 = fun x => i8Psi4s80k0S0 x + i8Psi4s80k0S1 x from funext i8Psi4s80k0_eq_S]
  exact (continuousOn_i8Psi4s80k0S0.add continuousOn_i8Psi4s80k0S1)

theorem i8Psi4s80k0_one : i8Psi4s80k0 1 = -137 / 2 - 16 * Real.log 2 ^ 2 + 26 * Real.log 2 +
    328 * Li 4 (1 / 2) - 227 / 72 * π ^ 4 + 16 / 3 * π ^ 2 + 41 / 3 * Real.log 2 ^ 4 +
    215 / 4 * zeta3 - 8 * Real.log 2 * π ^ 2 + 147 * Real.log 2 * zeta3 +
    7 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s80k0_eq_S]
  unfold i8Psi4s80k0S0 i8Psi4s80k0S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one,
    hpl_zero_one_at_one, hpl_negOne_zero_one_at_one, hpl_negOne_one_zero_at_one,
    hpl_zero_negOne_one_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_zero_at_one, hpl_negOne_negOne_zero_one_at_one, hpl_negOne_negOne_one_zero_at_one,
    hpl_negOne_zero_negOne_one_at_one, hpl_negOne_zero_one_negOne_at_one,
    hpl_zero_negOne_zero_one_at_one, hpl_zero_negOne_one_zero_at_one,
    hpl_zero_zero_negOne_one_at_one, hpl_zero_zero_one_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s80k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s80k1S0 (x : ℝ) : ℝ :=
    (-91 * x ^ 3 - 3 / 2 * x ^ 4) / x ^ 2 +
    (x ^ 4 + 31 * x ^ 2 + 32 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (2 * x ^ 4 + 60 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-64 * x ^ 3 - 60 * x ^ 2 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-32 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne] x +
    (4 * x ^ 4 + 8 * x + 40 * x ^ 3 + 44 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (2 * x ^ 4 + 4 * x + 20 * x ^ 3 + 22 * x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (-16) * hpl [zero, negOne, zero] x +
    (-8) * hpl [zero, zero, negOne] x +
    (4 * x ^ 3 + 8 * x + 28 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (2 * x ^ 3 + 4 * x + 14 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (8 + 8 * x ^ 4 + 32 * x + 32 * x ^ 3 + 48 * x ^ 2) / x ^ 2 * hpl [negOne, one, negOne, zero] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * hpl [negOne, one, zero, negOne] x +
    (-40) * hpl [zero, negOne, negOne, zero] x +
    (-20) * hpl [zero, negOne, zero, negOne] x +
    (-24) * hpl [zero, one, negOne, zero] x +
    (-12) * hpl [zero, one, zero, negOne] x +
    (8 - 40 * x ^ 2 - 8 * x ^ 3 + 40 * x) / x ^ 2 * ((1 - x) * hpl [one, negOne, negOne, zero] x) +
    (4 - 20 * x ^ 2 - 4 * x ^ 3 + 20 * x) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero, negOne] x)

theorem continuousOn_i8Psi4s80k1S0 : ContinuousOn i8Psi4s80k1S0 (Ioc 0 1) := by
  unfold i8Psi4s80k1S0
  exact (((((((((((((((((((i13_cont_coef (p := fun x => -91 * x ^ 3 -
    3 / 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 31 * x ^ 2 + 32 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 60 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -64 * x ^ 3 - 60 * x ^ 2 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -32 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 40 * x ^ 3 + 44 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 4 * x + 20 * x ^ 3 + 22 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 3 + 8 * x + 28 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 3 + 4 * x + 14 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 8 + 8 * x ^ 4 + 32 * x + 32 * x ^ 3 +
        48 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 8 - 40 * x ^ 2 - 8 * x ^ 3 + 40 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 4 - 20 * x ^ 2 - 4 * x ^ 3 + 20 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero, negOne])))

theorem i8Psi4s80k1_eq_S (x : ℝ) : i8Psi4s80k1 x = i8Psi4s80k1S0 x := by
  unfold i8Psi4s80k1 i8Psi4s80k1S0 i8Psi4s80k1N0 i8Psi4s80k1N1 i8Psi4s80k1N2 i8Psi4s80k1N3
    i8Psi4s80k1N4 i8Psi4s80k1W
  ring

theorem continuousOn_i8Psi4s80k1 : ContinuousOn i8Psi4s80k1 (Ioc 0 1) := by
  rw [show i8Psi4s80k1 = fun x => i8Psi4s80k1S0 x from funext i8Psi4s80k1_eq_S]
  exact continuousOn_i8Psi4s80k1S0

theorem i8Psi4s80k1_one : i8Psi4s80k1 1 = -185 / 2 - 224 * Li 4 (1 / 2) + 18 * zeta3 +
    64 * Real.log 2 - 28 / 3 * Real.log 2 ^ 4 + 47 / 6 * π ^ 2 + 149 / 60 * π ^ 4 -
    224 * Real.log 2 * zeta3 - 4 * Real.log 2 * π ^ 2 + 12 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s80k1_eq_S]
  unfold i8Psi4s80k1S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_negOne_negOne_zero_at_one, hpl_negOne_zero_negOne_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_negOne_one_negOne_zero_at_one,
    hpl_negOne_one_zero_negOne_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_zero_negOne_at_one, hpl_zero_one_negOne_zero_at_one,
    hpl_zero_one_zero_negOne_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s80 : ContinuousOn i8Psi4s80 (Ioc 0 1) := by
  rw [show i8Psi4s80 = fun x => i8Psi4s80k0 x + i8Psi4s80k1 x from rfl]
  exact (continuousOn_i8Psi4s80k0.add continuousOn_i8Psi4s80k1)

theorem i8Psi4s80_one : i8Psi4s80 1 = -161 - 16 * Real.log 2 ^ 2 + 90 * Real.log 2 +
    104 * Li 4 (1 / 2) - 241 / 360 * π ^ 4 + 13 / 3 * Real.log 2 ^ 4 + 79 / 6 * π ^ 2 +
    287 / 4 * zeta3 - 77 * Real.log 2 * zeta3 - 12 * Real.log 2 * π ^ 2 +
    43 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  unfold i8Psi4s80
  rw [i8Psi4s80k0_one, i8Psi4s80k1_one]
  ring

/-- Chunk 0 of `i8Psi4s81k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s81k0S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 + 27 * x ^ 3) / x ^ 2 +
    (3 * x ^ 2 - 27 / 2 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero] x +
    (-3 * x - 27 / 2 * x ^ 2 - x ^ 3 / 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x ^ 4 / 2 + 2 * x ^ 2 + 7 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-x ^ 4 - 13 * x ^ 3 - 3 * x) / x ^ 2 * hpl [zero, one] x +
    (x ^ 3 / 2 - 2 * x + 13 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-1 + x ^ 4 - 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [negOne, zero, one] x +
    (2) * hpl [zero, zero, zero] x +
    (x ^ 4 - 2 * x + 6 * x ^ 3 + 7 * x ^ 2) / x ^ 2 * hpl [zero, zero, one] x +
    (x ^ 4 - 2 * x + 6 * x ^ 3) / x ^ 2 * hpl [zero, one, zero] x +
    (-x ^ 3 - 7 * x ^ 2 - 2 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero, one] x +
    (-2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one, zero] x +
    (-2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero, zero] x +
    (-2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero, one] x +
    (6) * hpl [zero, zero, zero, one] x +
    (6) * hpl [zero, zero, one, zero] x +
    (6) * hpl [zero, one, zero, zero] x

theorem continuousOn_i8Psi4s81k0S0 : ContinuousOn i8Psi4s81k0S0 (Ioc 0 1) := by
  unfold i8Psi4s81k0S0
  exact ((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 / 2 + 27 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 3 * x ^ 2 - 27 / 2 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -3 * x - 27 / 2 * x ^ 2 - x ^ 3 / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 2 * x ^ 2 + 7 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 13 * x ^ 3 - 3 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 - 2 * x + 13 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4 - 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 2 * x + 6 * x ^ 3 + 7 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 2 * x + 6 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 7 * x ^ 2 - 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, one]))).add
      ((i13_cont_coef (p := fun x => -2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero])))

theorem i8Psi4s81k0_eq_S (x : ℝ) : i8Psi4s81k0 x = i8Psi4s81k0S0 x := by
  unfold i8Psi4s81k0 i8Psi4s81k0S0 i8Psi4s81k0N0 i8Psi4s81k0N1 i8Psi4s81k0N2 i8Psi4s81k0N3
    i8Psi4s81k0N4 i8Psi4s81k0W
  ring

theorem continuousOn_i8Psi4s81k0 : ContinuousOn i8Psi4s81k0 (Ioc 0 1) := by
  rw [show i8Psi4s81k0 = fun x => i8Psi4s81k0S0 x from funext i8Psi4s81k0_eq_S]
  exact continuousOn_i8Psi4s81k0S0

theorem i8Psi4s81k0_one : i8Psi4s81k0 1 = 55 / 2 - 64 * Li 4 (1 / 2) + 2 * zeta3 -
    17 / 6 * π ^ 2 - 8 / 3 * Real.log 2 ^ 4 + 73 / 360 * π ^ 4 +
    8 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s81k0_eq_S]
  unfold i8Psi4s81k0S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_negOne_zero_one_at_one,
    hpl_zero_zero_zero_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one,
    hpl_negOne_zero_zero_one_at_one, hpl_negOne_zero_one_zero_at_one,
    hpl_negOne_one_zero_zero_at_one, hpl_zero_negOne_zero_one_at_one, hpl_zero_zero_zero_one_at_one,
    hpl_zero_zero_one_zero_at_one, hpl_zero_one_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s81k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s81k1S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 + 32 * x ^ 3) / x ^ 2 +
    (-35 / 4 * x ^ 2 - 17 / 2 * x ^ 3 - x / 2 - x ^ 4 / 4) / x ^ 2 * hpl [negOne] x +
    (x ^ 2 - 16 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero] x +
    (-31 / 4 * x ^ 2 - x / 2 - x ^ 3 / 4) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x ^ 4 / 2 - x + 9 * x ^ 3 + 15 / 2 * x ^ 2) / x ^ 2 * hpl [negOne, zero] x +
    (-1 / 2 - 15 * x ^ 2 - 8 * x - 8 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [negOne, one] x +
    (17 / 2) * hpl [zero, negOne] x +
    (2) * hpl [zero, zero] x +
    (15 / 2) * hpl [zero, one] x +
    (-1 / 2 + x ^ 3 / 2 - 17 / 2 * x + 17 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (x ^ 3 / 2 - x + 15 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-1 + x ^ 4 - 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [negOne, one, zero] x +
    (9) * hpl [zero, negOne, zero] x +
    (-1 + x ^ 4 - 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, negOne, one] x +
    (-1 + x ^ 4 - 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, one, negOne] x +
    (7) * hpl [zero, one, zero] x +
    (-1 - x ^ 3 - 9 * x - 9 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (-2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, one, zero] x +
    (-2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne, one] x +
    (-2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, zero, one, negOne] x

theorem continuousOn_i8Psi4s81k1S0 : ContinuousOn i8Psi4s81k1S0 (Ioc 0 1) := by
  unfold i8Psi4s81k1S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 / 2 + 32 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -35 / 4 * x ^ 2 - 17 / 2 * x ^ 3 - x / 2 -
        x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 2 - 16 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -31 / 4 * x ^ 2 - x / 2 - x ^ 3 / 4) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - x + 9 * x ^ 3 + 15 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 - 15 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 3 / 2 - 17 / 2 * x +
        17 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 - x + 15 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4 - 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4 - 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4 - 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 3 - 9 * x - 9 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one]))).add
      ((i13_cont_coef (p := fun x => -2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne])))

/-- Chunk 1 of `i8Psi4s81k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s81k1S1 (x : ℝ) : ℝ :=
    (-2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, one, negOne, zero] x

theorem continuousOn_i8Psi4s81k1S1 : ContinuousOn i8Psi4s81k1S1 (Ioc 0 1) := by
  unfold i8Psi4s81k1S1
  exact ((i13_cont_coef (p := fun x => -2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))

theorem i8Psi4s81k1_eq_S (x : ℝ) : i8Psi4s81k1 x = i8Psi4s81k1S0 x + i8Psi4s81k1S1 x := by
  unfold i8Psi4s81k1 i8Psi4s81k1S0 i8Psi4s81k1S1 i8Psi4s81k1N0 i8Psi4s81k1N1 i8Psi4s81k1N2
    i8Psi4s81k1N3 i8Psi4s81k1N4 i8Psi4s81k1W
  ring

theorem continuousOn_i8Psi4s81k1 : ContinuousOn i8Psi4s81k1 (Ioc 0 1) := by
  rw [show i8Psi4s81k1 = fun x => i8Psi4s81k1S0 x + i8Psi4s81k1S1 x from funext i8Psi4s81k1_eq_S]
  exact (continuousOn_i8Psi4s81k1S0.add continuousOn_i8Psi4s81k1S1)

theorem i8Psi4s81k1_one : i8Psi4s81k1 1 = 65 / 2 - 40 * Li 4 (1 / 2) - 18 * Real.log 2 +
    16 * Real.log 2 ^ 2 - 55 / 2 * zeta3 - 49 / 24 * π ^ 2 - 5 / 3 * Real.log 2 ^ 4 +
    47 / 72 * π ^ 4 - 35 * Real.log 2 * zeta3 + 5 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s81k1_eq_S]
  unfold i8Psi4s81k1S0 i8Psi4s81k1S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_negOne_one_at_one,
    hpl_zero_negOne_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_negOne_one_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_negOne_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_zero_at_one, hpl_zero_negOne_one_zero_at_one, hpl_zero_zero_negOne_one_at_one,
    hpl_zero_zero_one_negOne_at_one, hpl_zero_one_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s81k2` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s81k2S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 + 37 * x ^ 3) / x ^ 2 +
    (-19 * x ^ 3 - 3 * x - 43 / 2 * x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [negOne] x +
    (3 * x ^ 2 - 37 / 2 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero] x +
    (x ^ 4 / 2 - 2 * x + 10 * x ^ 3 + 15 / 2 * x ^ 2) / x ^ 2 * hpl [negOne, zero] x +
    (x ^ 4 - 3 * x + 19 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (x ^ 4 / 2 + 2 * x ^ 2 + 9 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-x ^ 4 - 11 * x ^ 2 - 10 * x ^ 3 - 2 * x) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-x ^ 4 - 10 * x ^ 3 - 2 * x) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-x ^ 4 - 10 * x ^ 3 - 2 * x + 9 * x ^ 2) / x ^ 2 * hpl [zero, zero, negOne] x +
    (2) * hpl [zero, zero, zero] x +
    (-1 - x ^ 3 - 9 * x - 9 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (10) * hpl [zero, negOne, zero, zero] x +
    (10) * hpl [zero, zero, negOne, zero] x +
    (10) * hpl [zero, zero, zero, negOne] x +
    (-2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, one, zero, negOne] x +
    (-2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero, zero] x) +
    (-2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne, zero] x) +
    (-2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, zero, negOne] x)

theorem continuousOn_i8Psi4s81k2S0 : ContinuousOn i8Psi4s81k2S0 (Ioc 0 1) := by
  unfold i8Psi4s81k2S0
  exact ((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 / 2 + 37 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -19 * x ^ 3 - 3 * x - 43 / 2 * x ^ 2 -
        x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 3 * x ^ 2 - 37 / 2 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - 2 * x + 10 * x ^ 3 +
        15 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 3 * x + 19 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 2 * x ^ 2 + 9 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 11 * x ^ 2 - 10 * x ^ 3 - 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 10 * x ^ 3 - 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 10 * x ^ 3 - 2 * x + 9 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 3 - 9 * x - 9 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero, negOne])))

theorem i8Psi4s81k2_eq_S (x : ℝ) : i8Psi4s81k2 x = i8Psi4s81k2S0 x := by
  unfold i8Psi4s81k2 i8Psi4s81k2S0 i8Psi4s81k2N0 i8Psi4s81k2N1 i8Psi4s81k2N2 i8Psi4s81k2N3
    i8Psi4s81k2N4 i8Psi4s81k2W
  ring

theorem continuousOn_i8Psi4s81k2 : ContinuousOn i8Psi4s81k2 (Ioc 0 1) := by
  rw [show i8Psi4s81k2 = fun x => i8Psi4s81k2S0 x from funext i8Psi4s81k2_eq_S]
  exact continuousOn_i8Psi4s81k2S0

theorem i8Psi4s81k2_one : i8Psi4s81k2 1 = 75 / 2 - 44 * Real.log 2 + 80 * Li 4 (1 / 2) -
    8 / 9 * π ^ 4 - 3 / 2 * zeta3 + π ^ 2 / 12 + 10 / 3 * Real.log 2 ^ 4 +
    70 * Real.log 2 * zeta3 - 10 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s81k2_eq_S]
  unfold i8Psi4s81k2S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_at_one,
    hpl_zero_one_zero_negOne_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s81 : ContinuousOn i8Psi4s81 (Ioc 0 1) := by
  rw [show i8Psi4s81 = fun x => i8Psi4s81k0 x + i8Psi4s81k1 x + i8Psi4s81k2 x from rfl]
  exact ((continuousOn_i8Psi4s81k0.add continuousOn_i8Psi4s81k1).add continuousOn_i8Psi4s81k2)

theorem i8Psi4s81_one : i8Psi4s81 1 = 195 / 2 - Real.log 2 ^ 4 - 62 * Real.log 2 - 27 * zeta3 -
    24 * Li 4 (1 / 2) + 16 * Real.log 2 ^ 2 - 115 / 24 * π ^ 2 - π ^ 4 / 30 +
    π ^ 2 * Real.log 2 ^ 2 + 35 * Real.log 2 * zeta3 := by
  unfold i8Psi4s81
  rw [i8Psi4s81k0_one, i8Psi4s81k1_one, i8Psi4s81k2_one]
  ring

/-- Chunk 0 of `i8Psi4s82` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s82S0 (x : ℝ) : ℝ :=
    (-96 * x ^ 3 - 3 * x ^ 4) / x ^ 2 +
    (-6 * x + 2 * x ^ 4 + 30 * x ^ 2 + 38 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (2 * x ^ 4 + 12 * x ^ 2 + 32 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-6 * x + 2 * x ^ 3 + 28 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-22 * x ^ 2 - 20 * x ^ 3 - 4 * x - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [negOne, one] x +
    (-20 * x ^ 3 - 4 * x - 2 * x ^ 4 + 18 * x ^ 2) / x ^ 2 * hpl [zero, negOne] x +
    (8) * hpl [zero, zero] x +
    (-4 * x + 2 * x ^ 4 + 12 * x ^ 3 + 14 * x ^ 2) / x ^ 2 * hpl [zero, one] x +
    (-2 - 18 * x - 18 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (-14 * x ^ 2 - 4 * x - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one] x +
    (-4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero] x +
    (20) * hpl [zero, negOne, zero] x +
    (-4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, negOne, one] x +
    (20) * hpl [zero, zero, negOne] x +
    (12) * hpl [zero, zero, one] x +
    (-4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, one, negOne] x +
    (12) * hpl [zero, one, zero] x +
    (-4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x)

theorem continuousOn_i8Psi4s82S0 : ContinuousOn i8Psi4s82S0 (Ioc 0 1) := by
  unfold i8Psi4s82S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -96 * x ^ 3 - 3 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -6 * x + 2 * x ^ 4 + 30 * x ^ 2 +
        38 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 12 * x ^ 2 + 32 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -6 * x + 2 * x ^ 3 + 28 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -22 * x ^ 2 - 20 * x ^ 3 - 4 * x -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -20 * x ^ 3 - 4 * x - 2 * x ^ 4 +
        18 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x + 2 * x ^ 4 + 12 * x ^ 3 +
        14 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -2 - 18 * x - 18 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -14 * x ^ 2 - 4 * x - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero])))

/-- Chunk 1 of `i8Psi4s82` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s82S1 (x : ℝ) : ℝ :=
    (-4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x)

theorem continuousOn_i8Psi4s82S1 : ContinuousOn i8Psi4s82S1 (Ioc 0 1) := by
  unfold i8Psi4s82S1
  exact ((i13_cont_coef (p := fun x => -4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))

theorem i8Psi4s82_eq_S (x : ℝ) : i8Psi4s82 x = i8Psi4s82S0 x + i8Psi4s82S1 x := by
  unfold i8Psi4s82 i8Psi4s82S0 i8Psi4s82S1 i8Psi4s82N0 i8Psi4s82N1 i8Psi4s82N2 i8Psi4s82N3
    i8Psi4s82N4 i8Psi4s82W
  ring

theorem continuousOn_i8Psi4s82 : ContinuousOn i8Psi4s82 (Ioc 0 1) := by
  rw [show i8Psi4s82 = fun x => i8Psi4s82S0 x + i8Psi4s82S1 x from funext i8Psi4s82_eq_S]
  exact (continuousOn_i8Psi4s82S0.add continuousOn_i8Psi4s82S1)

theorem i8Psi4s82_one : i8Psi4s82 1 = -99 + 52 * zeta3 + 64 * Real.log 2 + 22 / 3 * π ^ 2 -
    16 * Real.log 2 * π ^ 2 := by
  rw [i8Psi4s82_eq_S]
  unfold i8Psi4s82S0 i8Psi4s82S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_negOne_one_at_one,
    hpl_zero_negOne_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_negOne_zero_one_at_one,
    hpl_negOne_one_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_negOne_one_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s83` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s83S0 (x : ℝ) : ℝ :=
    (18 * x + 22 * x ^ 3 + 19 / 8 * x ^ 4) / x ^ 2 +
    (-22 * x ^ 3 + 18 * x - 19 / 4 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (4 * x ^ 2 + 14 * x + 26 * x ^ 3 + 11 / 2 * x ^ 4) / x ^ 2 * hpl [zero, zero] x +
    (-18 * x ^ 3 - 8 * x ^ 2 - 3 * x ^ 4 + 6 * x) / x ^ 2 * hpl [zero, zero, zero] x +
    (-18) * hpl [zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s83S0 : ContinuousOn i8Psi4s83S0 (Ioc 0 1) := by
  unfold i8Psi4s83S0
  exact (((((i13_cont_coef (p := fun x => 18 * x + 22 * x ^ 3 + 19 / 8 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -22 * x ^ 3 + 18 * x - 19 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 2 + 14 * x + 26 * x ^ 3 +
        11 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -18 * x ^ 3 - 8 * x ^ 2 - 3 * x ^ 4 + 6 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero])))

theorem i8Psi4s83_eq_S (x : ℝ) : i8Psi4s83 x = i8Psi4s83S0 x := by
  unfold i8Psi4s83 i8Psi4s83S0 i8Psi4s83N0 i8Psi4s83N1 i8Psi4s83N2 i8Psi4s83N3 i8Psi4s83N4
    i8Psi4s83W
  ring

theorem continuousOn_i8Psi4s83 : ContinuousOn i8Psi4s83 (Ioc 0 1) := by
  rw [show i8Psi4s83 = fun x => i8Psi4s83S0 x from funext i8Psi4s83_eq_S]
  exact continuousOn_i8Psi4s83S0

theorem i8Psi4s83_one : i8Psi4s83 1 = 339 / 8 := by
  rw [i8Psi4s83_eq_S]
  unfold i8Psi4s83S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_zero_zero_at_one]
  norm_num

end QED.ThreeLoopD
