/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4V4

/-!
# Set (d), master `I₈`: continuity and values at `1` of the sub-pieces 84 to 97 of `Ψ₄`

Each sub-piece `Ψ₄⁽ⁿ⁾` is continuous on `(0, 1]` (the words beginning with `1` carry a factor
`1 - ξ`), and its value at `ξ = 1` follows from the values of the harmonic polylogarithms at `1`.

## Main results

* `QED.ThreeLoopD.continuousOn_i8Psi4s84`, `QED.ThreeLoopD.i8Psi4s84_one` and their
  companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- Chunk 0 of `i8Psi4s84` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s84S0 (x : ℝ) : ℝ :=
    (-125 / 8 * x + 13 / 4 * x ^ 4 + 1027 / 8 * x ^ 3) / x ^ 2 +
    (-19 / 8 - 40 * x - 40 * x ^ 3 - 301 / 4 * x ^ 2 - 19 / 8 * x ^ 4) / x ^ 2 * hpl [negOne] x +
    (-363 / 4 * x ^ 3 - 53 / 4 * x - 33 / 8 * x ^ 4 + 301 / 8 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (-19 / 4 - 40 * x + 40 * x ^ 3 + 19 / 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-19 / 4 - 40 * x + 40 * x ^ 3 + 19 / 4 * x ^ 4) / x ^ 2 * hpl [zero, negOne] x +
    (-17 / 2 * x + 7 / 2 * x ^ 4 + 111 / 2 * x ^ 3 + 141 / 4 * x ^ 2) / x ^ 2 * hpl [zero, zero] x +
    (-11 / 2 - 69 * x ^ 2 - 40 * x - 40 * x ^ 3 -
      11 / 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-11 / 2 - 40 * x - 40 * x ^ 3 - 8 * x ^ 2 -
      11 / 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-11 / 2 - 40 * x - 40 * x ^ 3 - 8 * x ^ 2 -
      11 / 2 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne] x +
    (-21 * x ^ 3 - 3 * x - 3 / 2 * x ^ 4 + 69 / 2 * x ^ 2) / x ^ 2 * hpl [zero, zero, zero] x +
    (-3 - 24 * x + 3 * x ^ 4 + 24 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero, zero] x +
    (-3 - 24 * x + 3 * x ^ 4 + 24 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero, zero] x +
    (-3 - 24 * x + 3 * x ^ 4 + 24 * x ^ 3) / x ^ 2 * hpl [zero, zero, negOne, zero] x +
    (-3 - 24 * x + 3 * x ^ 4 + 24 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero, negOne] x +
    (21) * hpl [zero, zero, zero, zero] x +
    (36) * hpl [zero, negOne, zero, zero, zero] x +
    (36) * hpl [zero, zero, negOne, zero, zero] x +
    (36) * hpl [zero, zero, zero, negOne, zero] x +
    (36) * hpl [zero, zero, zero, zero, negOne] x

theorem continuousOn_i8Psi4s84S0 : ContinuousOn i8Psi4s84S0 (Ioc 0 1) := by
  unfold i8Psi4s84S0
  exact (((((((((((((((((((i13_cont_coef (p := fun x => -125 / 8 * x + 13 / 4 * x ^ 4 +
    1027 / 8 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -19 / 8 - 40 * x - 40 * x ^ 3 - 301 / 4 * x ^ 2 -
        19 / 8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -363 / 4 * x ^ 3 - 53 / 4 * x - 33 / 8 * x ^ 4 +
        301 / 8 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -19 / 4 - 40 * x + 40 * x ^ 3 +
        19 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -19 / 4 - 40 * x + 40 * x ^ 3 +
        19 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -17 / 2 * x + 7 / 2 * x ^ 4 + 111 / 2 * x ^ 3 +
        141 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -11 / 2 - 69 * x ^ 2 - 40 * x - 40 * x ^ 3 -
        11 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -11 / 2 - 40 * x - 40 * x ^ 3 - 8 * x ^ 2 -
        11 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -11 / 2 - 40 * x - 40 * x ^ 3 - 8 * x ^ 2 -
        11 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -21 * x ^ 3 - 3 * x - 3 / 2 * x ^ 4 +
        69 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -3 - 24 * x + 3 * x ^ 4 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -3 - 24 * x + 3 * x ^ 4 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -3 - 24 * x + 3 * x ^ 4 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -3 - 24 * x + 3 * x ^ 4 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, negOne])))

theorem i8Psi4s84_eq_S (x : ℝ) : i8Psi4s84 x = i8Psi4s84S0 x := by
  unfold i8Psi4s84 i8Psi4s84S0 i8Psi4s84N0 i8Psi4s84N1 i8Psi4s84N2 i8Psi4s84N3 i8Psi4s84N4
    i8Psi4s84W
  ring

theorem continuousOn_i8Psi4s84 : ContinuousOn i8Psi4s84 (Ioc 0 1) := by
  rw [show i8Psi4s84 = fun x => i8Psi4s84S0 x from funext i8Psi4s84_eq_S]
  exact continuousOn_i8Psi4s84S0

theorem i8Psi4s84_one : i8Psi4s84 1 = 116 - 160 * Real.log 2 - 183 / 4 * zeta3 -
    135 / 4 * zeta5 := by
  rw [i8Psi4s84_eq_S]
  unfold i8Psi4s84S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one, hpl_negOne_zero_zero_zero_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_negOne_at_one, hpl_zero_zero_zero_zero_at_one,
    hpl_zero_negOne_zero_zero_zero_at_one, hpl_zero_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s85` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s85S0 (x : ℝ) : ℝ :=
    (-115 / 2 * x ^ 3 - 19 / 4 * x ^ 4) / x ^ 2 +
    (-20 * x ^ 2 + 3 * x ^ 4 + 39 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (20 * x + 13 / 2 * x ^ 3 + 37 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-x ^ 4 - 14 * x ^ 3 - 12 * x ^ 2) / x ^ 2 * hpl [zero, zero] x +
    (5 * x ^ 4 + 8 * x ^ 2 + 12 * x + 20 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-25 * x ^ 2 - 5 * x ^ 3 + 12 * x) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-4) * hpl [zero, zero, zero] x +
    (-12 * x ^ 3 - 8 * x ^ 2 - 2 * x ^ 4 + 4 * x) / x ^ 2 * hpl [zero, zero, one] x +
    (-12 * x ^ 3 - 8 * x ^ 2 - 2 * x ^ 4 + 4 * x) / x ^ 2 * hpl [zero, one, zero] x +
    (2 * x ^ 3 + 4 * x + 14 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-12) * hpl [zero, zero, zero, one] x +
    (-12) * hpl [zero, zero, one, zero] x +
    (-12) * hpl [zero, one, zero, zero] x

theorem continuousOn_i8Psi4s85S0 : ContinuousOn i8Psi4s85S0 (Ioc 0 1) := by
  unfold i8Psi4s85S0
  exact (((((((((((((i13_cont_coef (p := fun x => -115 / 2 * x ^ 3 -
    19 / 4 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -20 * x ^ 2 + 3 * x ^ 4 + 39 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 20 * x + 13 / 2 * x ^ 3 + 37 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 14 * x ^ 3 - 12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 5 * x ^ 4 + 8 * x ^ 2 + 12 * x + 20 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -25 * x ^ 2 - 5 * x ^ 3 + 12 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 8 * x ^ 2 - 2 * x ^ 4 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 8 * x ^ 2 - 2 * x ^ 4 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 3 + 4 * x + 14 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero])))

theorem i8Psi4s85_eq_S (x : ℝ) : i8Psi4s85 x = i8Psi4s85S0 x := by
  unfold i8Psi4s85 i8Psi4s85S0 i8Psi4s85N0 i8Psi4s85N1 i8Psi4s85N2 i8Psi4s85N3 i8Psi4s85N4
    i8Psi4s85W
  ring

theorem continuousOn_i8Psi4s85 : ContinuousOn i8Psi4s85 (Ioc 0 1) := by
  rw [show i8Psi4s85 = fun x => i8Psi4s85S0 x from funext i8Psi4s85_eq_S]
  exact continuousOn_i8Psi4s85S0

theorem i8Psi4s85_one : i8Psi4s85 1 = -249 / 4 + 18 * zeta3 - 2 / 15 * π ^ 4 + 15 / 2 * π ^ 2 := by
  rw [i8Psi4s85_eq_S]
  unfold i8Psi4s85S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one, hpl_zero_zero_zero_one_at_one,
    hpl_zero_zero_one_zero_at_one, hpl_zero_one_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s86` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s86S0 (x : ℝ) : ℝ :=
    (-48 * x ^ 3 - 7 / 2 * x ^ 4) / x ^ 2 +
    (-7 * x + 3 * x ^ 4 + 13 * x ^ 2 + 23 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (x ^ 4 + 14 * x ^ 2 + 16 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-7 * x + 3 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-x ^ 4 - 11 * x ^ 2 - 10 * x ^ 3 - 2 * x) / x ^ 2 * hpl [negOne, zero] x +
    (-5 - 8 * x + 5 * x ^ 4 + 8 * x ^ 3) / x ^ 2 * hpl [negOne, one] x +
    (-x ^ 4 - 10 * x ^ 3 - 2 * x + 13 * x ^ 2) / x ^ 2 * hpl [zero, negOne] x +
    (4) * hpl [zero, zero] x +
    (x ^ 4 - 2 * x + 3 * x ^ 2 + 6 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-5 - 13 * x - 13 * x ^ 2 - 5 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (-x ^ 3 - 7 * x ^ 2 - 2 * x) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one] x +
    (-2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero] x +
    (10) * hpl [zero, negOne, zero] x +
    (-2 - 16 * x ^ 2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, one] x +
    (10) * hpl [zero, zero, negOne] x +
    (6) * hpl [zero, zero, one] x +
    (-2 - 16 * x ^ 2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, one, negOne] x +
    (6) * hpl [zero, one, zero] x +
    (-2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x)

theorem continuousOn_i8Psi4s86S0 : ContinuousOn i8Psi4s86S0 (Ioc 0 1) := by
  unfold i8Psi4s86S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -48 * x ^ 3 -
    7 / 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -7 * x + 3 * x ^ 4 + 13 * x ^ 2 +
        23 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 14 * x ^ 2 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -7 * x + 3 * x ^ 3 + 12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 11 * x ^ 2 - 10 * x ^ 3 - 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -5 - 8 * x + 5 * x ^ 4 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 10 * x ^ 3 - 2 * x + 13 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 2 * x + 3 * x ^ 2 + 6 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -5 - 13 * x - 13 * x ^ 2 - 5 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 7 * x ^ 2 - 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero])))

/-- Chunk 1 of `i8Psi4s86` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s86S1 (x : ℝ) : ℝ :=
    (-2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x)

theorem continuousOn_i8Psi4s86S1 : ContinuousOn i8Psi4s86S1 (Ioc 0 1) := by
  unfold i8Psi4s86S1
  exact ((i13_cont_coef (p := fun x => -2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))

theorem i8Psi4s86_eq_S (x : ℝ) : i8Psi4s86 x = i8Psi4s86S0 x + i8Psi4s86S1 x := by
  unfold i8Psi4s86 i8Psi4s86S0 i8Psi4s86S1 i8Psi4s86N0 i8Psi4s86N1 i8Psi4s86N2 i8Psi4s86N3
    i8Psi4s86N4 i8Psi4s86W
  ring

theorem continuousOn_i8Psi4s86 : ContinuousOn i8Psi4s86 (Ioc 0 1) := by
  rw [show i8Psi4s86 = fun x => i8Psi4s86S0 x + i8Psi4s86S1 x from funext i8Psi4s86_eq_S]
  exact (continuousOn_i8Psi4s86S0.add continuousOn_i8Psi4s86S1)

theorem i8Psi4s86_one : i8Psi4s86 1 = -103 / 2 + 16 * zeta3 + 32 * Real.log 2 + 10 / 3 * π ^ 2 -
    8 * Real.log 2 * π ^ 2 := by
  rw [i8Psi4s86_eq_S]
  unfold i8Psi4s86S0 i8Psi4s86S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_negOne_one_at_one,
    hpl_zero_negOne_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_negOne_zero_one_at_one,
    hpl_negOne_one_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_negOne_one_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s87k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s87k0S0 (x : ℝ) : ℝ :=
    (-x ^ 4 - 59 / 2 * x ^ 3) / x ^ 2 +
    (x ^ 4 / 2 - x + 9 * x ^ 3 + 15 / 2 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (x ^ 4 / 2 + 4 * x ^ 2 + 7 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (x ^ 3 - 3 * x + 14 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-1 + x ^ 4 - 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [negOne, one] x +
    (9) * hpl [zero, negOne] x +
    (2) * hpl [zero, zero] x +
    (x ^ 4 - 2 * x + 6 * x ^ 3 + 7 * x ^ 2) / x ^ 2 * hpl [zero, one] x +
    (-1 - x ^ 3 - 9 * x - 9 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (-x ^ 3 - 7 * x ^ 2 - 2 * x) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one] x +
    (-2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero] x +
    (-2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, one] x +
    (6) * hpl [zero, zero, one] x +
    (-2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, one, negOne] x +
    (6) * hpl [zero, one, zero] x

theorem continuousOn_i8Psi4s87k0S0 : ContinuousOn i8Psi4s87k0S0 (Ioc 0 1) := by
  unfold i8Psi4s87k0S0
  exact ((((((((((((((((i13_cont_coef (p := fun x => -x ^ 4 - 59 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - x + 9 * x ^ 3 + 15 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 4 * x ^ 2 + 7 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - 3 * x + 14 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4 - 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 2 * x + 6 * x ^ 3 + 7 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 3 - 9 * x - 9 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 7 * x ^ 2 - 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero])))

theorem i8Psi4s87k0_eq_S (x : ℝ) : i8Psi4s87k0 x = i8Psi4s87k0S0 x := by
  unfold i8Psi4s87k0 i8Psi4s87k0S0 i8Psi4s87k0N0 i8Psi4s87k0N1 i8Psi4s87k0N2 i8Psi4s87k0N3
    i8Psi4s87k0N4 i8Psi4s87k0W
  ring

theorem continuousOn_i8Psi4s87k0 : ContinuousOn i8Psi4s87k0 (Ioc 0 1) := by
  rw [show i8Psi4s87k0 = fun x => i8Psi4s87k0S0 x from funext i8Psi4s87k0_eq_S]
  exact continuousOn_i8Psi4s87k0S0

theorem i8Psi4s87k0_one : i8Psi4s87k0 1 = -61 / 2 + 16 * Real.log 2 + 11 / 4 * π ^ 2 +
    67 / 2 * zeta3 - 8 * Real.log 2 * π ^ 2 := by
  rw [i8Psi4s87k0_eq_S]
  unfold i8Psi4s87k0S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_negOne_zero_one_at_one,
    hpl_negOne_one_zero_at_one, hpl_zero_negOne_one_at_one, hpl_zero_zero_one_at_one,
    hpl_zero_one_negOne_at_one, hpl_zero_one_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s87k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s87k1S0 (x : ℝ) : ℝ :=
    (-189 / 4 * x ^ 3 - 3 / 4 * x ^ 4) / x ^ 2 +
    (x ^ 4 / 2 - 2 * x + 10 * x ^ 3 + 15 / 2 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (4 * x ^ 2 + 3 / 4 * x ^ 4 + 47 / 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-2 * x + x ^ 3 / 4 + 57 / 4 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-x ^ 4 - 11 * x ^ 2 - 10 * x ^ 3 - 2 * x) / x ^ 2 * hpl [negOne, zero] x +
    (-x ^ 4 - 10 * x ^ 3 - 2 * x) / x ^ 2 * hpl [zero, negOne] x +
    (4) * hpl [zero, zero] x +
    (x ^ 4 / 2 - 2 * x + 14 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-2 * x - 29 / 2 * x ^ 2 - x ^ 3 / 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (10) * hpl [zero, negOne, zero] x +
    (10) * hpl [zero, zero, negOne] x +
    (-x ^ 4 - 14 * x ^ 3 - 2 * x) / x ^ 2 * hpl [zero, zero, one] x +
    (-x ^ 4 - 14 * x ^ 3 - 2 * x) / x ^ 2 * hpl [zero, one, zero] x +
    (-2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (-2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (-2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero, one] x +
    (-2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [negOne, zero, one, zero] x +
    (14) * hpl [zero, zero, zero, one] x +
    (14) * hpl [zero, zero, one, zero] x +
    (24) * hpl [zero, negOne, zero, zero, one] x

theorem continuousOn_i8Psi4s87k1S0 : ContinuousOn i8Psi4s87k1S0 (Ioc 0 1) := by
  unfold i8Psi4s87k1S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -189 / 4 * x ^ 3 -
    3 / 4 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - 2 * x + 10 * x ^ 3 +
        15 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 2 + 3 / 4 * x ^ 4 + 47 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -2 * x + x ^ 3 / 4 + 57 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 11 * x ^ 2 - 10 * x ^ 3 - 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 10 * x ^ 3 - 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - 2 * x + 14 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -2 * x - 29 / 2 * x ^ 2 - x ^ 3 / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 14 * x ^ 3 - 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 14 * x ^ 3 - 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, one]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero, one])))

/-- Chunk 1 of `i8Psi4s87k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s87k1S1 (x : ℝ) : ℝ :=
    (24) * hpl [zero, negOne, zero, one, zero] x

theorem continuousOn_i8Psi4s87k1S1 : ContinuousOn i8Psi4s87k1S1 (Ioc 0 1) := by
  unfold i8Psi4s87k1S1
  exact (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one, zero]))

theorem i8Psi4s87k1_eq_S (x : ℝ) : i8Psi4s87k1 x = i8Psi4s87k1S0 x + i8Psi4s87k1S1 x := by
  unfold i8Psi4s87k1 i8Psi4s87k1S0 i8Psi4s87k1S1 i8Psi4s87k1N0 i8Psi4s87k1N1 i8Psi4s87k1N2
    i8Psi4s87k1N3 i8Psi4s87k1N4 i8Psi4s87k1W
  ring

theorem continuousOn_i8Psi4s87k1 : ContinuousOn i8Psi4s87k1 (Ioc 0 1) := by
  rw [show i8Psi4s87k1 = fun x => i8Psi4s87k1S0 x + i8Psi4s87k1S1 x from funext i8Psi4s87k1_eq_S]
  exact (continuousOn_i8Psi4s87k1S0.add continuousOn_i8Psi4s87k1S1)

theorem i8Psi4s87k1_one : i8Psi4s87k1 1 = -48 + 3 * π ^ 2 + 16 * Real.log 2 - 14 / 45 * π ^ 4 +
    19 / 2 * zeta3 + 153 / 2 * zeta5 - 15 / 2 * π ^ 2 * zeta3 := by
  rw [i8Psi4s87k1_eq_S]
  unfold i8Psi4s87k1S0 i8Psi4s87k1S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one,
    hpl_negOne_zero_zero_one_at_one, hpl_negOne_zero_one_zero_at_one, hpl_zero_zero_zero_one_at_one,
    hpl_zero_zero_one_zero_at_one, hpl_zero_negOne_zero_zero_one_at_one,
    hpl_zero_negOne_zero_one_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s87k2` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s87k2S0 (x : ℝ) : ℝ :=
    (-123 / 2 * x ^ 3 - x ^ 4 / 2) / x ^ 2 +
    (x ^ 4 / 2 + 3 / 2 * x ^ 2 + 61 / 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (x ^ 3 / 2 + 31 * x ^ 2 - 3 / 2 * x) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-1 / 2 + x ^ 4 / 2 - 16 * x + 16 * x ^ 3) / x ^ 2 * hpl [negOne, one] x +
    (x ^ 2 - 15 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero, zero] x +
    (x ^ 4 / 2 - x + 15 * x ^ 3 + 31 / 2 * x ^ 2) / x ^ 2 * hpl [zero, one] x +
    (-x - 31 / 2 * x ^ 2 - x ^ 3 / 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-1 - x ^ 4 - 30 * x ^ 2 - 16 * x - 16 * x ^ 3) / x ^ 2 * hpl [negOne, zero, one] x +
    (-1 - x ^ 4 - 30 * x ^ 2 - 16 * x - 16 * x ^ 3) / x ^ 2 * hpl [negOne, one, zero] x +
    (-1 - x ^ 4 - 16 * x - 16 * x ^ 3) / x ^ 2 * hpl [zero, negOne, one] x +
    (2) * hpl [zero, zero, zero] x +
    (15) * hpl [zero, zero, one] x +
    (15) * hpl [zero, one, zero] x +
    (x ^ 3 - 2 * x + 15 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [negOne, one, zero, zero] x +
    (-2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero, one] x +
    (-2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [zero, negOne, one, zero] x +
    (-2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [zero, zero, negOne, one] x +
    (14) * hpl [zero, one, zero, zero] x +
    (24) * hpl [zero, negOne, one, zero, zero] x

theorem continuousOn_i8Psi4s87k2S0 : ContinuousOn i8Psi4s87k2S0 (Ioc 0 1) := by
  unfold i8Psi4s87k2S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -123 / 2 * x ^ 3 -
    x ^ 4 / 2) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 3 / 2 * x ^ 2 + 61 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 + 31 * x ^ 2 - 3 / 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 4 / 2 - 16 * x + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 - 15 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - x + 15 * x ^ 3 + 31 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -x - 31 / 2 * x ^ 2 - x ^ 3 / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 4 - 30 * x ^ 2 - 16 * x -
        16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 4 - 30 * x ^ 2 - 16 * x -
        16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 4 - 16 * x - 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - 2 * x + 15 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero, zero])))

/-- Chunk 1 of `i8Psi4s87k2` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s87k2S1 (x : ℝ) : ℝ :=
    (24) * hpl [zero, zero, negOne, zero, one] x +
    (24) * hpl [zero, zero, negOne, one, zero] x +
    (24) * hpl [zero, zero, zero, negOne, one] x

theorem continuousOn_i8Psi4s87k2S1 : ContinuousOn i8Psi4s87k2S1 (Ioc 0 1) := by
  unfold i8Psi4s87k2S1
  exact (((continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, one])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne, one])))

theorem i8Psi4s87k2_eq_S (x : ℝ) : i8Psi4s87k2 x = i8Psi4s87k2S0 x + i8Psi4s87k2S1 x := by
  unfold i8Psi4s87k2 i8Psi4s87k2S0 i8Psi4s87k2S1 i8Psi4s87k2N0 i8Psi4s87k2N1 i8Psi4s87k2N2
    i8Psi4s87k2N3 i8Psi4s87k2N4 i8Psi4s87k2W
  ring

theorem continuousOn_i8Psi4s87k2 : ContinuousOn i8Psi4s87k2 (Ioc 0 1) := by
  rw [show i8Psi4s87k2 = fun x => i8Psi4s87k2S0 x + i8Psi4s87k2S1 x from funext i8Psi4s87k2_eq_S]
  exact (continuousOn_i8Psi4s87k2S0.add continuousOn_i8Psi4s87k2S1)

theorem i8Psi4s87k2_one : i8Psi4s87k2 1 = -62 + 5 * π ^ 2 - 33 / 4 * zeta5 + 7 / 15 * π ^ 4 +
    135 / 4 * zeta3 - 15 / 2 * Real.log 2 * π ^ 2 - Real.log 2 * π ^ 4 / 2 +
    9 / 2 * π ^ 2 * zeta3 := by
  rw [i8Psi4s87k2_eq_S]
  unfold i8Psi4s87k2S0 i8Psi4s87k2S1
  rw [hpl_zero_at_one, hpl_negOne_one_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one,
    hpl_negOne_zero_one_at_one, hpl_negOne_one_zero_at_one, hpl_zero_negOne_one_at_one,
    hpl_zero_zero_zero_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one,
    hpl_negOne_one_zero_zero_at_one, hpl_zero_negOne_zero_one_at_one,
    hpl_zero_negOne_one_zero_at_one, hpl_zero_zero_negOne_one_at_one, hpl_zero_one_zero_zero_at_one,
    hpl_zero_negOne_one_zero_zero_at_one, hpl_zero_zero_negOne_zero_one_at_one,
    hpl_zero_zero_negOne_one_zero_at_one, hpl_zero_zero_zero_negOne_one_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s87k3` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s87k3S0 (x : ℝ) : ℝ :=
    (-133 / 2 * x ^ 3 - x ^ 4 / 2) / x ^ 2 +
    (x ^ 4 / 2 - 3 / 2 * x + 63 / 2 * x ^ 2 + 67 / 2 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (x ^ 4 / 2 + 3 / 2 * x ^ 2 + 67 / 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-x - 17 * x ^ 3 - 35 / 2 * x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [negOne, zero] x +
    (-x - 17 * x ^ 3 - x ^ 4 / 2 + 33 / 2 * x ^ 2) / x ^ 2 * hpl [zero, negOne] x +
    (x ^ 2 - 17 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero, zero] x +
    (-1 / 2 - 33 / 2 * x - 33 / 2 * x ^ 2 - x ^ 3 / 2) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (x ^ 4 - 2 * x + 15 * x ^ 2 + 18 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero] x +
    (17) * hpl [zero, negOne, zero] x +
    (17) * hpl [zero, zero, negOne] x +
    (2) * hpl [zero, zero, zero] x +
    (-1 - x ^ 4 - 16 * x - 16 * x ^ 3) / x ^ 2 * hpl [zero, one, negOne] x +
    (-1 + x ^ 3 - 17 * x + 17 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (-1 + x ^ 3 - 17 * x + 17 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (18) * hpl [zero, negOne, zero, zero] x +
    (-2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [zero, zero, one, negOne] x +
    (-2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [zero, one, negOne, zero] x +
    (-2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [zero, one, zero, negOne] x +
    (-2 - 18 * x - 18 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero, zero] x) +
    (24) * hpl [zero, zero, zero, one, negOne] x

theorem continuousOn_i8Psi4s87k3S0 : ContinuousOn i8Psi4s87k3S0 (Ioc 0 1) := by
  unfold i8Psi4s87k3S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -133 / 2 * x ^ 3 -
    x ^ 4 / 2) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - 3 / 2 * x + 63 / 2 * x ^ 2 +
        67 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 3 / 2 * x ^ 2 + 67 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x - 17 * x ^ 3 - 35 / 2 * x ^ 2 -
        x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -x - 17 * x ^ 3 - x ^ 4 / 2 +
        33 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 - 17 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 - 33 / 2 * x - 33 / 2 * x ^ 2 -
        x ^ 3 / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 2 * x + 15 * x ^ 2 + 18 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 4 - 16 * x - 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 3 - 17 * x + 17 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 3 - 17 * x + 17 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 - 18 * x - 18 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one, negOne])))

/-- Chunk 1 of `i8Psi4s87k3` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s87k3S1 (x : ℝ) : ℝ :=
    (24) * hpl [zero, zero, one, negOne, zero] x +
    (24) * hpl [zero, zero, one, zero, negOne] x +
    (24) * hpl [zero, one, negOne, zero, zero] x

theorem continuousOn_i8Psi4s87k3S1 : ContinuousOn i8Psi4s87k3S1 (Ioc 0 1) := by
  unfold i8Psi4s87k3S1
  exact (((continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne, zero])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero, zero])))

theorem i8Psi4s87k3_eq_S (x : ℝ) : i8Psi4s87k3 x = i8Psi4s87k3S0 x + i8Psi4s87k3S1 x := by
  unfold i8Psi4s87k3 i8Psi4s87k3S0 i8Psi4s87k3S1 i8Psi4s87k3N0 i8Psi4s87k3N1 i8Psi4s87k3N2
    i8Psi4s87k3N3 i8Psi4s87k3N4 i8Psi4s87k3W
  ring

theorem continuousOn_i8Psi4s87k3 : ContinuousOn i8Psi4s87k3 (Ioc 0 1) := by
  rw [show i8Psi4s87k3 = fun x => i8Psi4s87k3S0 x + i8Psi4s87k3S1 x from funext i8Psi4s87k3_eq_S]
  exact (continuousOn_i8Psi4s87k3S0.add continuousOn_i8Psi4s87k3S1)

theorem i8Psi4s87k3_one : i8Psi4s87k3 1 = -67 + 64 * Real.log 2 - 33 / 4 * zeta5 +
    17 / 6 * π ^ 2 + 21 / 40 * π ^ 4 + 181 / 4 * zeta3 + Real.log 2 * π ^ 4 / 2 -
    17 / 2 * Real.log 2 * π ^ 2 := by
  rw [i8Psi4s87k3_eq_S]
  unfold i8Psi4s87k3S0 i8Psi4s87k3S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_zero_one_negOne_at_one,
    hpl_zero_one_negOne_zero_at_one, hpl_zero_one_zero_negOne_at_one,
    hpl_zero_zero_zero_one_negOne_at_one, hpl_zero_zero_one_negOne_zero_at_one,
    hpl_zero_zero_one_zero_negOne_at_one, hpl_zero_one_negOne_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s87k4` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s87k4S0 (x : ℝ) : ℝ :=
    (-141 / 4 * x ^ 3 - x ^ 4 / 4) / x ^ 2 +
    (-2 * x + 18 * x ^ 3 + x ^ 4 / 4 + 63 / 4 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (2 * x ^ 2 + x ^ 4 / 4 + 35 / 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-18 * x ^ 3 - 2 * x - 39 / 2 * x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [negOne, zero] x +
    (-18 * x ^ 3 - 2 * x - x ^ 4 / 2) / x ^ 2 * hpl [zero, negOne] x +
    (2) * hpl [zero, zero] x +
    (x ^ 4 - 2 * x + 18 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero] x +
    (x ^ 4 - 2 * x + 18 * x ^ 3) / x ^ 2 * hpl [zero, zero, negOne] x +
    (18) * hpl [zero, zero, negOne, zero] x +
    (18) * hpl [zero, zero, zero, negOne] x +
    (-2 - 18 * x - 18 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne, zero] x) +
    (-2 - 18 * x - 18 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, zero, negOne] x) +
    (24) * hpl [zero, one, zero, negOne, zero] x +
    (24) * hpl [zero, one, zero, zero, negOne] x

theorem continuousOn_i8Psi4s87k4S0 : ContinuousOn i8Psi4s87k4S0 (Ioc 0 1) := by
  unfold i8Psi4s87k4S0
  exact ((((((((((((((i13_cont_coef (p := fun x => -141 / 4 * x ^ 3 - x ^ 4 / 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -2 * x + 18 * x ^ 3 + x ^ 4 / 4 +
        63 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 2 + x ^ 4 / 4 + 35 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -18 * x ^ 3 - 2 * x - 39 / 2 * x ^ 2 -
        x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -18 * x ^ 3 - 2 * x - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 2 * x + 18 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 2 * x + 18 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 - 18 * x - 18 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 18 * x - 18 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero, negOne])))

theorem i8Psi4s87k4_eq_S (x : ℝ) : i8Psi4s87k4 x = i8Psi4s87k4S0 x := by
  unfold i8Psi4s87k4 i8Psi4s87k4S0 i8Psi4s87k4N0 i8Psi4s87k4N1 i8Psi4s87k4N2 i8Psi4s87k4N3
    i8Psi4s87k4N4 i8Psi4s87k4W
  ring

theorem continuousOn_i8Psi4s87k4 : ContinuousOn i8Psi4s87k4 (Ioc 0 1) := by
  rw [show i8Psi4s87k4 = fun x => i8Psi4s87k4S0 x from funext i8Psi4s87k4_eq_S]
  exact continuousOn_i8Psi4s87k4S0

theorem i8Psi4s87k4_one : i8Psi4s87k4 1 = -71 / 2 + 32 * Real.log 2 - 159 / 4 * zeta5 -
    51 / 4 * zeta3 - 7 / 20 * π ^ 4 + 13 / 8 * π ^ 2 + 3 / 2 * π ^ 2 * zeta3 := by
  rw [i8Psi4s87k4_eq_S]
  unfold i8Psi4s87k4S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_at_one,
    hpl_zero_one_zero_negOne_zero_at_one, hpl_zero_one_zero_zero_negOne_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s87 : ContinuousOn i8Psi4s87 (Ioc 0 1) := by
  rw [show i8Psi4s87 = fun x => i8Psi4s87k0 x + i8Psi4s87k1 x + i8Psi4s87k2 x +
    i8Psi4s87k3 x + i8Psi4s87k4 x from rfl]
  exact ((((continuousOn_i8Psi4s87k0.add continuousOn_i8Psi4s87k1).add continuousOn_i8Psi4s87k2).add
    continuousOn_i8Psi4s87k3).add continuousOn_i8Psi4s87k4)

theorem i8Psi4s87_one : i8Psi4s87 1 = -243 + 128 * Real.log 2 + 81 / 4 * zeta5 +
    119 / 360 * π ^ 4 + 365 / 24 * π ^ 2 + 437 / 4 * zeta3 - 24 * Real.log 2 * π ^ 2 -
    3 / 2 * π ^ 2 * zeta3 := by
  unfold i8Psi4s87
  rw [i8Psi4s87k0_one, i8Psi4s87k1_one, i8Psi4s87k2_one, i8Psi4s87k3_one, i8Psi4s87k4_one]
  ring

/-- Chunk 0 of `i8Psi4s88` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s88S0 (x : ℝ) : ℝ :=
    (-16 * x ^ 3 + 4 * x ^ 4 + 16 * x + zeta3 * x ^ 4 - 4 * x * zeta3 + 4 * zeta3 * x ^ 3 -
      2 / 3 * π ^ 2 * x + π ^ 2 * x ^ 4 / 6 + 2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 +
    (-8 * x ^ 4 + 16 * x + 16 * x ^ 3 - 4 * x * zeta3 - 4 * zeta3 * x ^ 3 - 2 * zeta3 * x ^ 4 -
      2 / 3 * π ^ 2 * x - 2 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 3) / x ^ 2 * hpl [zero] x +
    (16 + 4 * zeta3 + 2 / 3 * π ^ 2) * hpl [zero, zero] x

theorem continuousOn_i8Psi4s88S0 : ContinuousOn i8Psi4s88S0 (Ioc 0 1) := by
  unfold i8Psi4s88S0
  exact (((i13_cont_coef (p := fun x => -16 * x ^ 3 + 4 * x ^ 4 + 16 * x + zeta3 * x ^ 4 -
    4 * x * zeta3 + 4 * zeta3 * x ^ 3 - 2 / 3 * π ^ 2 * x + π ^ 2 * x ^ 4 / 6 +
    2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 4 + 16 * x + 16 * x ^ 3 - 4 * x * zeta3 -
        4 * zeta3 * x ^ 3 - 2 * zeta3 * x ^ 4 - 2 / 3 * π ^ 2 * x - 2 / 3 * π ^ 2 * x ^ 3 -
        π ^ 2 * x ^ 4 / 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero])))

theorem i8Psi4s88_eq_S (x : ℝ) : i8Psi4s88 x = i8Psi4s88S0 x := by
  unfold i8Psi4s88 i8Psi4s88S0 i8Psi4s88N0 i8Psi4s88N1 i8Psi4s88N2 i8Psi4s88N3 i8Psi4s88N4
    i8Psi4s88W
  ring

theorem continuousOn_i8Psi4s88 : ContinuousOn i8Psi4s88 (Ioc 0 1) := by
  rw [show i8Psi4s88 = fun x => i8Psi4s88S0 x from funext i8Psi4s88_eq_S]
  exact continuousOn_i8Psi4s88S0

theorem i8Psi4s88_one : i8Psi4s88 1 = 4 + zeta3 + π ^ 2 / 6 := by
  rw [i8Psi4s88_eq_S]
  unfold i8Psi4s88S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s89` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s89S0 (x : ℝ) : ℝ :=
    (2 * x ^ 4 + 16 * x + 16 * x ^ 3 - 2 / 3 * π ^ 2 * x - 2 / 3 * π ^ 2 * x ^ 3 -
      π ^ 2 * x ^ 4 / 12) / x ^ 2 +
    (-16 * x ^ 3 - 4 * x ^ 4 + 16 * x - 2 / 3 * π ^ 2 * x + π ^ 2 * x ^ 4 / 6 +
      2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (8 * x ^ 4 + 16 * x + 16 * x ^ 3 - 2 / 3 * π ^ 2 * x - 2 / 3 * π ^ 2 * x ^ 3 -
      π ^ 2 * x ^ 4 / 3) / x ^ 2 * hpl [zero, zero] x +
    (-16 + 2 / 3 * π ^ 2) * hpl [zero, zero, zero] x

theorem continuousOn_i8Psi4s89S0 : ContinuousOn i8Psi4s89S0 (Ioc 0 1) := by
  unfold i8Psi4s89S0
  exact ((((i13_cont_coef (p := fun x => 2 * x ^ 4 + 16 * x + 16 * x ^ 3 - 2 / 3 * π ^ 2 * x -
    2 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 12) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -16 * x ^ 3 - 4 * x ^ 4 + 16 * x - 2 / 3 * π ^ 2 * x +
        π ^ 2 * x ^ 4 / 6 + 2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 8 * x ^ 4 + 16 * x + 16 * x ^ 3 - 2 / 3 * π ^ 2 * x -
        2 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero])))

theorem i8Psi4s89_eq_S (x : ℝ) : i8Psi4s89 x = i8Psi4s89S0 x := by
  unfold i8Psi4s89 i8Psi4s89S0 i8Psi4s89N0 i8Psi4s89N1 i8Psi4s89N2 i8Psi4s89N3 i8Psi4s89N4
    i8Psi4s89W
  ring

theorem continuousOn_i8Psi4s89 : ContinuousOn i8Psi4s89 (Ioc 0 1) := by
  rw [show i8Psi4s89 = fun x => i8Psi4s89S0 x from funext i8Psi4s89_eq_S]
  exact continuousOn_i8Psi4s89S0

theorem i8Psi4s89_one : i8Psi4s89 1 = 34 - 17 / 12 * π ^ 2 := by
  rw [i8Psi4s89_eq_S]
  unfold i8Psi4s89S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s90` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s90S0 (x : ℝ) : ℝ :=
    (π ^ 2 * x ^ 4 / 6 + 5 / 6 * π ^ 2 * x ^ 3) / x ^ 2 +
    (-2 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 6 + π ^ 2 * x ^ 2 / 6 +
      2 / 3 * π ^ 2 * x) / x ^ 2 * hpl [negOne] x +
    (-2 / 3 * π ^ 2 * x ^ 2 - π ^ 2 * x ^ 3 / 3 - π ^ 2 * x ^ 4 / 6) / x ^ 2 * hpl [zero] x +
    (π ^ 2 * x ^ 2 + π ^ 2 * x ^ 4 / 3 + 2 / 3 * π ^ 2 * x +
      2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (π ^ 2 * x ^ 4 / 3 + 2 / 3 * π ^ 2 * x + 2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (-2 / 3 * π ^ 2) * hpl [zero, zero] x +
    (-2 / 3 * π ^ 2) * hpl [zero, negOne, zero] x +
    (-2 / 3 * π ^ 2) * hpl [zero, zero, negOne] x

theorem continuousOn_i8Psi4s90S0 : ContinuousOn i8Psi4s90S0 (Ioc 0 1) := by
  unfold i8Psi4s90S0
  exact ((((((((i13_cont_coef (p := fun x => π ^ 2 * x ^ 4 / 6 +
    5 / 6 * π ^ 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -2 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 6 +
        π ^ 2 * x ^ 2 / 6 + 2 / 3 * π ^ 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -2 / 3 * π ^ 2 * x ^ 2 - π ^ 2 * x ^ 3 / 3 -
        π ^ 2 * x ^ 4 / 6) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => π ^ 2 * x ^ 2 + π ^ 2 * x ^ 4 / 3 + 2 / 3 * π ^ 2 * x +
        2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => π ^ 2 * x ^ 4 / 3 + 2 / 3 * π ^ 2 * x +
        2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne])))

theorem i8Psi4s90_eq_S (x : ℝ) : i8Psi4s90 x = i8Psi4s90S0 x := by
  unfold i8Psi4s90 i8Psi4s90S0 i8Psi4s90N0 i8Psi4s90N1 i8Psi4s90N2 i8Psi4s90N3 i8Psi4s90N4
    i8Psi4s90W
  ring

theorem continuousOn_i8Psi4s90 : ContinuousOn i8Psi4s90 (Ioc 0 1) := by
  rw [show i8Psi4s90 = fun x => i8Psi4s90S0 x from funext i8Psi4s90_eq_S]
  exact continuousOn_i8Psi4s90S0

theorem i8Psi4s90_one : i8Psi4s90 1 = π ^ 2 - π ^ 4 / 12 + π ^ 2 * zeta3 / 2 := by
  rw [i8Psi4s90_eq_S]
  unfold i8Psi4s90S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s91` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s91S0 (x : ℝ) : ℝ :=
    (-13 * x ^ 3 - x ^ 4 / 2) / x ^ 2 +
    (x ^ 4 + 13 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-x ^ 4 - 15 * x ^ 2 - 8 * x - 8 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (-x ^ 4 - 6 * x ^ 3 + 8 * x ^ 2) / x ^ 2 * hpl [zero, zero] x +
    (-8 * x - 2 * x ^ 2 + 2 * x ^ 4 + 8 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-8 * x + 2 * x ^ 4 + 8 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero] x +
    (8) * hpl [zero, zero, zero] x +
    (-8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero, zero] x +
    (-8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne, zero] x +
    (8) * hpl [zero, zero, negOne, zero, zero] x +
    (8) * hpl [zero, zero, zero, negOne, zero] x

theorem continuousOn_i8Psi4s91S0 : ContinuousOn i8Psi4s91S0 (Ioc 0 1) := by
  unfold i8Psi4s91S0
  exact (((((((((((i13_cont_coef (p := fun x => -13 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 13 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 15 * x ^ 2 - 8 * x - 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 6 * x ^ 3 + 8 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x - 2 * x ^ 2 + 2 * x ^ 4 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x + 2 * x ^ 4 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne, zero])))

theorem i8Psi4s91_eq_S (x : ℝ) : i8Psi4s91 x = i8Psi4s91S0 x := by
  unfold i8Psi4s91 i8Psi4s91S0 i8Psi4s91N0 i8Psi4s91N1 i8Psi4s91N2 i8Psi4s91N3 i8Psi4s91N4
    i8Psi4s91W
  ring

theorem continuousOn_i8Psi4s91 : ContinuousOn i8Psi4s91 (Ioc 0 1) := by
  rw [show i8Psi4s91 = fun x => i8Psi4s91S0 x from funext i8Psi4s91_eq_S]
  exact continuousOn_i8Psi4s91S0

theorem i8Psi4s91_one : i8Psi4s91 1 = -27 / 2 - 3 * zeta3 + 15 * zeta5 + 8 / 3 * π ^ 2 := by
  rw [i8Psi4s91_eq_S]
  unfold i8Psi4s91S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_zero_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s92` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s92S0 (x : ℝ) : ℝ :=
    (x ^ 4 + 12 * x ^ 3) / x ^ 2 +
    (-12 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (2 * x ^ 4 + 8 * x ^ 2 + 10 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (2 * x ^ 4 + 4 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-8 * x ^ 3 - 2 * x ^ 4 + 2 * x ^ 2 + 8 * x) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (-8 * x ^ 3 - 4 * x ^ 2 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-8 * x ^ 2 - 4 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero] x +
    (8 * x ^ 4 + 16 * x + 16 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero, zero] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne, zero] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, negOne, negOne, zero] x +
    (-16) * hpl [zero, negOne, zero, zero] x +
    (-8) * hpl [zero, zero, negOne, zero] x +
    (-16) * hpl [zero, negOne, negOne, zero, zero] x +
    (-8) * hpl [zero, negOne, zero, negOne, zero] x +
    (-8) * hpl [zero, zero, negOne, negOne, zero] x

theorem continuousOn_i8Psi4s92S0 : ContinuousOn i8Psi4s92S0 (Ioc 0 1) := by
  unfold i8Psi4s92S0
  exact (((((((((((((((i13_cont_coef (p := fun x => x ^ 4 + 12 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 8 * x ^ 2 + 10 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 3 - 2 * x ^ 4 + 2 * x ^ 2 + 8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 3 - 4 * x ^ 2 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 2 - 4 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 8 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 3 + 12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne, zero])))

theorem i8Psi4s92_eq_S (x : ℝ) : i8Psi4s92 x = i8Psi4s92S0 x := by
  unfold i8Psi4s92 i8Psi4s92S0 i8Psi4s92N0 i8Psi4s92N1 i8Psi4s92N2 i8Psi4s92N3 i8Psi4s92N4
    i8Psi4s92W
  ring

theorem continuousOn_i8Psi4s92 : ContinuousOn i8Psi4s92 (Ioc 0 1) := by
  rw [show i8Psi4s92 = fun x => i8Psi4s92S0 x from funext i8Psi4s92_eq_S]
  exact continuousOn_i8Psi4s92S0

theorem i8Psi4s92_one : i8Psi4s92 1 = 13 + 9 * zeta3 - 23 / 120 * π ^ 4 - 5 / 3 * π ^ 2 +
    23 / 2 * zeta5 - 7 / 6 * π ^ 2 * zeta3 := by
  rw [i8Psi4s92_eq_S]
  unfold i8Psi4s92S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_negOne_negOne_zero_zero_at_one,
    hpl_negOne_zero_negOne_zero_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_negOne_negOne_zero_zero_at_one, hpl_zero_negOne_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s93` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s93S0 (x : ℝ) : ℝ :=
    (8 * x + 8 * x ^ 3 + x ^ 4 / 4) / x ^ 2 +
    (-8 * x ^ 3 + 8 * x - x ^ 4 / 2) / x ^ 2 * hpl [zero] x +
    (x ^ 4 + 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-8 * x ^ 3 - 2 * x ^ 4 + 8 * x) / x ^ 2 * hpl [zero, zero, zero] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero, zero] x +
    (-8) * hpl [zero, zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s93S0 : ContinuousOn i8Psi4s93S0 (Ioc 0 1) := by
  unfold i8Psi4s93S0
  exact ((((((i13_cont_coef (p := fun x => 8 * x + 8 * x ^ 3 + x ^ 4 / 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 3 + 8 * x - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 3 - 2 * x ^ 4 + 8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, zero])))

theorem i8Psi4s93_eq_S (x : ℝ) : i8Psi4s93 x = i8Psi4s93S0 x := by
  unfold i8Psi4s93 i8Psi4s93S0 i8Psi4s93N0 i8Psi4s93N1 i8Psi4s93N2 i8Psi4s93N3 i8Psi4s93N4
    i8Psi4s93W
  ring

theorem continuousOn_i8Psi4s93 : ContinuousOn i8Psi4s93 (Ioc 0 1) := by
  rw [show i8Psi4s93 = fun x => i8Psi4s93S0 x from funext i8Psi4s93_eq_S]
  exact continuousOn_i8Psi4s93S0

theorem i8Psi4s93_one : i8Psi4s93 1 = 65 / 4 := by
  have h5 : hpl [zero, zero, zero, zero, zero] 1 = 0 := by
    rw [hpl_of_allZero (by decide)]
    simp
  rw [i8Psi4s93_eq_S]
  unfold i8Psi4s93S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_zero_zero_at_one, h5]
  norm_num

/-- Chunk 0 of `i8Psi4s94` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s94S0 (x : ℝ) : ℝ :=
    (-9 * x ^ 3 - x ^ 4 / 2) / x ^ 2 +
    (x ^ 4 + 9 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-9 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, zero] x +
    (x ^ 4 - x ^ 2 - 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero] x +
    (3 * x ^ 4 + 4 * x ^ 2 + 6 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero] x +
    (-18 * x ^ 2 - 12 * x - 12 * x ^ 3 - 6 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero, zero] x +
    (-4 * x - 4 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero, zero] x +
    (12) * hpl [zero, zero, zero, zero] x +
    (12) * hpl [zero, negOne, zero, zero, zero] x +
    (4) * hpl [zero, zero, negOne, zero, zero] x

theorem continuousOn_i8Psi4s94S0 : ContinuousOn i8Psi4s94S0 (Ioc 0 1) := by
  unfold i8Psi4s94S0
  exact ((((((((((i13_cont_coef (p := fun x => -9 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 9 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -9 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - x ^ 2 - 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 3 * x ^ 4 + 4 * x ^ 2 + 6 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -18 * x ^ 2 - 12 * x - 12 * x ^ 3 -
        6 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x - 4 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, zero])))

theorem i8Psi4s94_eq_S (x : ℝ) : i8Psi4s94 x = i8Psi4s94S0 x := by
  unfold i8Psi4s94 i8Psi4s94S0 i8Psi4s94N0 i8Psi4s94N1 i8Psi4s94N2 i8Psi4s94N3 i8Psi4s94N4
    i8Psi4s94W
  ring

theorem continuousOn_i8Psi4s94 : ContinuousOn i8Psi4s94 (Ioc 0 1) := by
  rw [show i8Psi4s94 = fun x => i8Psi4s94S0 x from funext i8Psi4s94_eq_S]
  exact continuousOn_i8Psi4s94S0

theorem i8Psi4s94_one : i8Psi4s94 1 = -19 / 2 - 45 / 2 * zeta5 + 7 / 40 * π ^ 4 := by
  rw [i8Psi4s94_eq_S]
  unfold i8Psi4s94S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_negOne_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s95` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s95S0 (x : ℝ) : ℝ :=
    (14 * x ^ 3 + 3 / 2 * x ^ 4) / x ^ 2 +
    (-14 * x ^ 3 - 3 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (-8 * x - 2 * x ^ 2 + 2 * x ^ 4 + 8 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (4 * x ^ 4 + 8 * x ^ 2 + 8 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 8 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero] x +
    (16) * hpl [zero, zero, zero] x +
    (16) * hpl [zero, negOne, zero, zero] x +
    (8) * hpl [zero, zero, negOne, zero] x

theorem continuousOn_i8Psi4s95S0 : ContinuousOn i8Psi4s95S0 (Ioc 0 1) := by
  unfold i8Psi4s95S0
  exact (((((((((i13_cont_coef (p := fun x => 14 * x ^ 3 + 3 / 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -14 * x ^ 3 - 3 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -8 * x - 2 * x ^ 2 + 2 * x ^ 4 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x ^ 2 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero])))

theorem i8Psi4s95_eq_S (x : ℝ) : i8Psi4s95 x = i8Psi4s95S0 x := by
  unfold i8Psi4s95 i8Psi4s95S0 i8Psi4s95N0 i8Psi4s95N1 i8Psi4s95N2 i8Psi4s95N3 i8Psi4s95N4
    i8Psi4s95W
  ring

theorem continuousOn_i8Psi4s95 : ContinuousOn i8Psi4s95 (Ioc 0 1) := by
  rw [show i8Psi4s95 = fun x => i8Psi4s95S0 x from funext i8Psi4s95_eq_S]
  exact continuousOn_i8Psi4s95S0

theorem i8Psi4s95_one : i8Psi4s95 1 = 31 / 2 - 18 * zeta3 + 7 / 30 * π ^ 4 := by
  rw [i8Psi4s95_eq_S]
  unfold i8Psi4s95S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s96` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s96S0 (x : ℝ) : ℝ :=
    (-12 * x ^ 3 + 12 * x - 3 / 4 * x ^ 4) / x ^ 2 +
    (12 * x + 12 * x ^ 3 + 3 / 2 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (-12 * x ^ 3 - 3 * x ^ 4 + 12 * x) / x ^ 2 * hpl [zero, zero] x +
    (6 * x ^ 4 + 12 * x + 12 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero] x +
    (-12) * hpl [zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s96S0 : ContinuousOn i8Psi4s96S0 (Ioc 0 1) := by
  unfold i8Psi4s96S0
  exact (((((i13_cont_coef (p := fun x => -12 * x ^ 3 + 12 * x - 3 / 4 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 12 * x + 12 * x ^ 3 + 3 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 3 * x ^ 4 + 12 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 6 * x ^ 4 + 12 * x + 12 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero])))

theorem i8Psi4s96_eq_S (x : ℝ) : i8Psi4s96 x = i8Psi4s96S0 x := by
  unfold i8Psi4s96 i8Psi4s96S0 i8Psi4s96N0 i8Psi4s96N1 i8Psi4s96N2 i8Psi4s96N3 i8Psi4s96N4
    i8Psi4s96W
  ring

theorem continuousOn_i8Psi4s96 : ContinuousOn i8Psi4s96 (Ioc 0 1) := by
  rw [show i8Psi4s96 = fun x => i8Psi4s96S0 x from funext i8Psi4s96_eq_S]
  exact continuousOn_i8Psi4s96S0

theorem i8Psi4s96_one : i8Psi4s96 1 = -3 / 4 := by
  rw [i8Psi4s96_eq_S]
  unfold i8Psi4s96S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_zero_zero_at_one]
  norm_num

/-- Chunk 0 of `i8Psi4s97` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s97S0 (x : ℝ) : ℝ :=
    (-8 * x ^ 4 + 16 * x ^ 3 - 12 * zeta3 * x ^ 3 - 2 * π ^ 2 * x ^ 3 - 2 * zeta3 * x ^ 4 -
      π ^ 2 * x ^ 4 / 3) / x ^ 2 +
    (-32 + 8 * zeta3 + 4 / 3 * π ^ 2) * hpl [zero] x +
    (-16 * x ^ 2 + 16 * x ^ 3 + 32 * x - 8 * x * zeta3 + 2 * π ^ 2 * x ^ 2 + 4 * zeta3 * x ^ 3 +
      12 * zeta3 * x ^ 2 - 4 / 3 * π ^ 2 * x + 2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * ((1 -
      x) * hpl [one] x) +
    (32 + 8 * zeta3 + 4 / 3 * π ^ 2) * hpl [zero, one] x

theorem continuousOn_i8Psi4s97S0 : ContinuousOn i8Psi4s97S0 (Ioc 0 1) := by
  unfold i8Psi4s97S0
  exact ((((i13_cont_coef (p := fun x => -8 * x ^ 4 + 16 * x ^ 3 - 12 * zeta3 * x ^ 3 -
    2 * π ^ 2 * x ^ 3 - 2 * zeta3 * x ^ 4 - π ^ 2 * x ^ 4 / 3) (by fun_prop)).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -16 * x ^ 2 + 16 * x ^ 3 + 32 * x - 8 * x * zeta3 +
        2 * π ^ 2 * x ^ 2 + 4 * zeta3 * x ^ 3 + 12 * zeta3 * x ^ 2 - 4 / 3 * π ^ 2 * x +
        2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one])))

theorem i8Psi4s97_eq_S (x : ℝ) : i8Psi4s97 x = i8Psi4s97S0 x := by
  unfold i8Psi4s97 i8Psi4s97S0 i8Psi4s97N0 i8Psi4s97N1 i8Psi4s97N2 i8Psi4s97N3 i8Psi4s97N4
    i8Psi4s97W
  ring

theorem continuousOn_i8Psi4s97 : ContinuousOn i8Psi4s97 (Ioc 0 1) := by
  rw [show i8Psi4s97 = fun x => i8Psi4s97S0 x from funext i8Psi4s97_eq_S]
  exact continuousOn_i8Psi4s97S0

theorem i8Psi4s97_one : i8Psi4s97 1 = 8 - 14 * zeta3 + 3 * π ^ 2 + 2 / 9 * π ^ 4 +
    4 / 3 * π ^ 2 * zeta3 := by
  rw [i8Psi4s97_eq_S]
  unfold i8Psi4s97S0
  rw [hpl_zero_at_one, hpl_zero_one_at_one]
  norm_num
  ring

end QED.ThreeLoopD
