/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4V5

/-!
# Set (d), master `I₈`: continuity and values at `1` of the sub-pieces 98 to 109 of `Ψ₄`

Each sub-piece `Ψ₄⁽ⁿ⁾` is continuous on `(0, 1]` (the words beginning with `1` carry a factor
`1 - ξ`), and its value at `ξ = 1` follows from the values of the harmonic polylogarithms at `1`.

## Main results

* `QED.ThreeLoopD.continuousOn_i8Psi4s98`, `QED.ThreeLoopD.i8Psi4s98_one` and their
  companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- Chunk 0 of `i8Psi4s98` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s98S0 (x : ℝ) : ℝ :=
    (-44 * x ^ 3 - 4 * x ^ 4 + π ^ 2 * x ^ 4 / 6 + 11 / 6 * π ^ 2 * x ^ 3) / x ^ 2 +
    (-16 * x ^ 2 + 4 * x ^ 4 + 24 * x ^ 3 - π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 6 +
      2 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (4 * x ^ 3 + 16 * x + 20 * x ^ 2 - 5 / 6 * π ^ 2 * x ^ 2 - 2 / 3 * π ^ 2 * x -
      π ^ 2 * x ^ 3 / 6) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-16 + 2 / 3 * π ^ 2) * hpl [zero, zero] x +
    (8 * x ^ 4 + 16 * x + 16 * x ^ 3 - 2 / 3 * π ^ 2 * x - 2 / 3 * π ^ 2 * x ^ 3 -
      π ^ 2 * x ^ 4 / 3) / x ^ 2 * hpl [zero, one] x +
    (-24 * x ^ 2 - 8 * x ^ 3 + 16 * x + π ^ 2 * x ^ 2 - 2 / 3 * π ^ 2 * x +
      π ^ 2 * x ^ 3 / 3) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-16 + 2 / 3 * π ^ 2) * hpl [zero, zero, one] x +
    (-16 + 2 / 3 * π ^ 2) * hpl [zero, one, zero] x

theorem continuousOn_i8Psi4s98S0 : ContinuousOn i8Psi4s98S0 (Ioc 0 1) := by
  unfold i8Psi4s98S0
  exact ((((((((i13_cont_coef (p := fun x => -44 * x ^ 3 - 4 * x ^ 4 + π ^ 2 * x ^ 4 / 6 +
    11 / 6 * π ^ 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -16 * x ^ 2 + 4 * x ^ 4 + 24 * x ^ 3 - π ^ 2 * x ^ 3 -
        π ^ 2 * x ^ 4 / 6 + 2 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 3 + 16 * x + 20 * x ^ 2 - 5 / 6 * π ^ 2 * x ^ 2 -
        2 / 3 * π ^ 2 * x - π ^ 2 * x ^ 3 / 6) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 8 * x ^ 4 + 16 * x + 16 * x ^ 3 - 2 / 3 * π ^ 2 * x -
        2 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 8 * x ^ 3 + 16 * x + π ^ 2 * x ^ 2 -
        2 / 3 * π ^ 2 * x + π ^ 2 * x ^ 3 / 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero])))

theorem i8Psi4s98_eq_S (x : ℝ) : i8Psi4s98 x = i8Psi4s98S0 x := by
  unfold i8Psi4s98 i8Psi4s98S0 i8Psi4s98N0 i8Psi4s98N1 i8Psi4s98N2 i8Psi4s98N3 i8Psi4s98N4
    i8Psi4s98W
  ring

theorem continuousOn_i8Psi4s98 : ContinuousOn i8Psi4s98 (Ioc 0 1) := by
  rw [show i8Psi4s98 = fun x => i8Psi4s98S0 x from funext i8Psi4s98_eq_S]
  exact continuousOn_i8Psi4s98S0

theorem i8Psi4s98_one : i8Psi4s98 1 = -48 + 16 * zeta3 - 5 / 18 * π ^ 4 + 26 / 3 * π ^ 2 -
    2 / 3 * π ^ 2 * zeta3 := by
  rw [i8Psi4s98_eq_S]
  unfold i8Psi4s98S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_one_at_one,
    hpl_zero_one_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s99` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s99S0 (x : ℝ) : ℝ :=
    (-8 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 3) / x ^ 2 +
    (2 * π ^ 2 * x ^ 3 + π ^ 2 * x ^ 4 / 3 + 5 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (π ^ 2 * x ^ 2 + π ^ 2 * x ^ 3 / 3) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (2 * π ^ 2 * x ^ 2 + 2 / 3 * π ^ 2 * x ^ 4 + 4 / 3 * π ^ 2 * x +
      4 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [negOne, one] x +
    (-4 / 3 * π ^ 2) * hpl [zero, negOne] x +
    (-4 / 3 * π ^ 2) * hpl [zero, one] x +
    (-2 * π ^ 2 * x ^ 2 - 2 / 3 * π ^ 2 * x ^ 3 + 4 / 3 * π ^ 2 * x) / x ^ 2 * ((1 -
      x) * hpl [one, negOne] x) +
    (-4 / 3 * π ^ 2) * hpl [zero, negOne, one] x +
    (-4 / 3 * π ^ 2) * hpl [zero, one, negOne] x

theorem continuousOn_i8Psi4s99S0 : ContinuousOn i8Psi4s99S0 (Ioc 0 1) := by
  unfold i8Psi4s99S0
  exact (((((((((i13_cont_coef (p := fun x => -8 / 3 * π ^ 2 * x ^ 3 -
    π ^ 2 * x ^ 4 / 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 2 * π ^ 2 * x ^ 3 + π ^ 2 * x ^ 4 / 3 +
        5 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => π ^ 2 * x ^ 2 + π ^ 2 * x ^ 3 / 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => 2 * π ^ 2 * x ^ 2 + 2 / 3 * π ^ 2 * x ^ 4 +
        4 / 3 * π ^ 2 * x + 4 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -2 * π ^ 2 * x ^ 2 - 2 / 3 * π ^ 2 * x ^ 3 +
        4 / 3 * π ^ 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne])))

theorem i8Psi4s99_eq_S (x : ℝ) : i8Psi4s99 x = i8Psi4s99S0 x := by
  unfold i8Psi4s99 i8Psi4s99S0 i8Psi4s99N0 i8Psi4s99N1 i8Psi4s99N2 i8Psi4s99N3 i8Psi4s99N4
    i8Psi4s99W
  ring

theorem continuousOn_i8Psi4s99 : ContinuousOn i8Psi4s99 (Ioc 0 1) := by
  rw [show i8Psi4s99 = fun x => i8Psi4s99S0 x from funext i8Psi4s99_eq_S]
  exact continuousOn_i8Psi4s99S0

theorem i8Psi4s99_one : i8Psi4s99 1 = -3 * π ^ 2 + π ^ 4 / 9 + 4 * Real.log 2 * π ^ 2 -
    8 / 3 * π ^ 2 * Real.log 2 ^ 2 - 5 / 6 * π ^ 2 * zeta3 := by
  rw [i8Psi4s99_eq_S]
  unfold i8Psi4s99S0
  rw [hpl_negOne_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one, hpl_zero_one_at_one,
    hpl_zero_negOne_one_at_one, hpl_zero_one_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s100` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s100S0 (x : ℝ) : ℝ :=
    (x ^ 4 + 67 / 2 * x ^ 3) / x ^ 2 +
    (-27 * x ^ 3 - 3 / 2 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (-13 / 2 * x ^ 2 - x ^ 3 / 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (2 * x ^ 4 + 20 * x ^ 2 + 22 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (-x ^ 4 - 6 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (x ^ 3 + 7 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-8 * x - 2 * x ^ 2 + 2 * x ^ 4 + 8 * x ^ 3) / x ^ 2 * hpl [negOne, zero, one] x +
    (-8 * x - 2 * x ^ 2 + 2 * x ^ 4 + 8 * x ^ 3) / x ^ 2 * hpl [negOne, one, zero] x +
    (-12 * x ^ 3 - 2 * x ^ 4 + 8 * x ^ 2) / x ^ 2 * hpl [zero, negOne, zero] x +
    (8) * hpl [zero, zero, one] x +
    (8) * hpl [zero, one, zero] x +
    (-10 * x ^ 2 - 8 * x - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (-8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero, one] x +
    (-8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, negOne, one, zero] x +
    (8) * hpl [zero, zero, negOne, zero] x +
    (-8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, one, negOne, zero] x +
    (-8 * x + 4 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne, zero] x) +
    (8) * hpl [zero, zero, negOne, zero, one] x +
    (8) * hpl [zero, zero, negOne, one, zero] x +
    (8) * hpl [zero, zero, one, negOne, zero] x

theorem continuousOn_i8Psi4s100S0 : ContinuousOn i8Psi4s100S0 (Ioc 0 1) := by
  unfold i8Psi4s100S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 + 67 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -27 * x ^ 3 - 3 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -13 / 2 * x ^ 2 - x ^ 3 / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 20 * x ^ 2 + 22 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 6 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + 7 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x - 2 * x ^ 2 + 2 * x ^ 4 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -8 * x - 2 * x ^ 2 + 2 * x ^ 4 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 2 * x ^ 4 + 8 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -10 * x ^ 2 - 8 * x - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one]))).add
      ((i13_cont_coef (p := fun x => -8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x + 4 * x ^ 3 + 12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne, zero])))

/-- Chunk 1 of `i8Psi4s100` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s100S1 (x : ℝ) : ℝ :=
    (8) * hpl [zero, one, zero, negOne, zero] x

theorem continuousOn_i8Psi4s100S1 : ContinuousOn i8Psi4s100S1 (Ioc 0 1) := by
  unfold i8Psi4s100S1
  exact (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne, zero]))

theorem i8Psi4s100_eq_S (x : ℝ) : i8Psi4s100 x = i8Psi4s100S0 x + i8Psi4s100S1 x := by
  unfold i8Psi4s100 i8Psi4s100S0 i8Psi4s100S1 i8Psi4s100N0 i8Psi4s100N1 i8Psi4s100N2 i8Psi4s100N3
    i8Psi4s100N4 i8Psi4s100W
  ring

theorem continuousOn_i8Psi4s100 : ContinuousOn i8Psi4s100 (Ioc 0 1) := by
  rw [show i8Psi4s100 = fun x => i8Psi4s100S0 x + i8Psi4s100S1 x from funext i8Psi4s100_eq_S]
  exact (continuousOn_i8Psi4s100S0.add continuousOn_i8Psi4s100S1)

theorem i8Psi4s100_one : i8Psi4s100 1 = 69 / 2 + zeta3 - 83 / 2 * zeta5 - 29 / 6 * π ^ 2 +
    π ^ 4 / 360 + 13 / 6 * π ^ 2 * zeta3 := by
  rw [i8Psi4s100_eq_S]
  unfold i8Psi4s100S0 i8Psi4s100S1
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_one_at_one, hpl_negOne_zero_one_at_one,
    hpl_negOne_one_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_zero_one_at_one,
    hpl_zero_one_zero_at_one, hpl_zero_negOne_zero_one_at_one, hpl_zero_negOne_one_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_one_negOne_zero_at_one,
    hpl_zero_zero_negOne_zero_one_at_one, hpl_zero_zero_negOne_one_zero_at_one,
    hpl_zero_zero_one_negOne_zero_at_one, hpl_zero_one_zero_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s101` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s101S0 (x : ℝ) : ℝ :=
    (-39 * x ^ 3 - 2 * x ^ 4) / x ^ 2 +
    (3 * x ^ 4 + 34 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (x ^ 3 + 5 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-32 * x ^ 3 - 28 * x ^ 2 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (2 * x ^ 4 + 4 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-6 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (4 * x ^ 4 + 20 * x ^ 2 + 24 * x ^ 3) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (-8 * x ^ 3 - 4 * x ^ 2 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one] x +
    (-8 * x ^ 3 - 4 * x ^ 2 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero] x +
    (4 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (8 * x ^ 4 + 16 * x + 16 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero, one] x +
    (8 * x ^ 4 + 16 * x + 16 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, one, zero] x +
    (8 * x ^ 4 + 16 * x + 16 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * hpl [negOne, one, negOne, zero] x +
    (-16) * hpl [zero, negOne, negOne, zero] x +
    (-16) * hpl [zero, negOne, zero, one] x +
    (-16) * hpl [zero, negOne, one, zero] x +
    (-16) * hpl [zero, one, negOne, zero] x +
    (-24 * x ^ 2 - 8 * x ^ 3 + 16 * x) / x ^ 2 * ((1 - x) * hpl [one, negOne, negOne, zero] x) +
    (-16) * hpl [zero, negOne, negOne, zero, one] x +
    (-16) * hpl [zero, negOne, negOne, one, zero] x

theorem continuousOn_i8Psi4s101S0 : ContinuousOn i8Psi4s101S0 (Ioc 0 1) := by
  unfold i8Psi4s101S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -39 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 3 * x ^ 4 + 34 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + 5 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -32 * x ^ 3 - 28 * x ^ 2 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -6 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 20 * x ^ 2 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 3 - 4 * x ^ 2 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 3 - 4 * x ^ 2 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 3 + 12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 8 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, one]))).add
      ((i13_cont_coef (p := fun x => 8 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, one, zero]))).add
      ((i13_cont_coef (p := fun x => 8 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 8 * x ^ 3 + 16 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, one, zero])))

/-- Chunk 1 of `i8Psi4s101` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s101S1 (x : ℝ) : ℝ :=
    (-16) * hpl [zero, negOne, one, negOne, zero] x +
    (-16) * hpl [zero, one, negOne, negOne, zero] x

theorem continuousOn_i8Psi4s101S1 : ContinuousOn i8Psi4s101S1 (Ioc 0 1) := by
  unfold i8Psi4s101S1
  exact ((continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, negOne, zero])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, negOne, zero])))

theorem i8Psi4s101_eq_S (x : ℝ) : i8Psi4s101 x = i8Psi4s101S0 x + i8Psi4s101S1 x := by
  unfold i8Psi4s101 i8Psi4s101S0 i8Psi4s101S1 i8Psi4s101N0 i8Psi4s101N1 i8Psi4s101N2 i8Psi4s101N3
    i8Psi4s101N4 i8Psi4s101W
  ring

theorem continuousOn_i8Psi4s101 : ContinuousOn i8Psi4s101 (Ioc 0 1) := by
  rw [show i8Psi4s101 = fun x => i8Psi4s101S0 x + i8Psi4s101S1 x from funext i8Psi4s101_eq_S]
  exact (continuousOn_i8Psi4s101S0.add continuousOn_i8Psi4s101S1)

theorem i8Psi4s101_one : i8Psi4s101 1 = -41 - π ^ 4 + 10 * zeta5 + 32 * zeta3 +
    128 * Li 4 (1 / 2) + 16 / 3 * Real.log 2 ^ 4 + 19 / 3 * π ^ 2 - 8 * Real.log 2 * π ^ 2 -
    π ^ 2 * zeta3 / 3 + 16 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s101_eq_S]
  unfold i8Psi4s101S0 i8Psi4s101S1
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_one_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_negOne_zero_one_at_one, hpl_negOne_one_zero_at_one, hpl_negOne_negOne_zero_one_at_one,
    hpl_negOne_negOne_one_zero_at_one, hpl_negOne_one_negOne_zero_at_one,
    hpl_zero_negOne_negOne_zero_at_one, hpl_zero_negOne_zero_one_at_one,
    hpl_zero_negOne_one_zero_at_one, hpl_zero_one_negOne_zero_at_one,
    hpl_zero_negOne_negOne_zero_one_at_one, hpl_zero_negOne_negOne_one_zero_at_one,
    hpl_zero_negOne_one_negOne_zero_at_one, hpl_zero_one_negOne_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s102` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s102S0 (x : ℝ) : ℝ :=
    (-79 / 4 * x ^ 3 - x ^ 4 / 2) / x ^ 2 +
    (-4 * x ^ 2 + 3 / 4 * x ^ 4 + 31 / 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (4 * x + x ^ 3 / 4 + 17 / 4 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-x ^ 4 - 11 * x ^ 3 - 4 * x ^ 2) / x ^ 2 * hpl [zero, zero] x +
    (x ^ 4 / 2 + 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (4 * x - 9 / 2 * x ^ 2 - x ^ 3 / 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (x ^ 4 - 4 * x ^ 2 + 6 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero] x +
    (-x ^ 4 - 4 * x ^ 3 + 4 * x) / x ^ 2 * hpl [zero, zero, one] x +
    (-x ^ 4 - 4 * x ^ 3 + 4 * x) / x ^ 2 * hpl [zero, one, zero] x +
    (x ^ 3 + 4 * x + 5 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-4) * hpl [zero, zero, zero, zero] x +
    (2 * x ^ 4 + 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero, one] x +
    (2 * x ^ 4 + 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [zero, zero, one, zero] x +
    (2 * x ^ 4 + 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [zero, one, zero, zero] x +
    (-6 * x ^ 2 - 2 * x ^ 3 + 4 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero, zero] x) +
    (-4) * hpl [zero, zero, zero, zero, one] x +
    (-4) * hpl [zero, zero, zero, one, zero] x +
    (-4) * hpl [zero, zero, one, zero, zero] x +
    (-4) * hpl [zero, one, zero, zero, zero] x

theorem continuousOn_i8Psi4s102S0 : ContinuousOn i8Psi4s102S0 (Ioc 0 1) := by
  unfold i8Psi4s102S0
  exact (((((((((((((((((((i13_cont_coef (p := fun x => -79 / 4 * x ^ 3 -
    x ^ 4 / 2) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 2 + 3 / 4 * x ^ 4 + 31 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 4 * x + x ^ 3 / 4 + 17 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 11 * x ^ 3 - 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => 4 * x - 9 / 2 * x ^ 2 - x ^ 3 / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 4 * x ^ 2 + 6 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 4 * x ^ 3 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 4 * x ^ 3 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + 4 * x + 5 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -6 * x ^ 2 - 2 * x ^ 3 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero, zero])))

theorem i8Psi4s102_eq_S (x : ℝ) : i8Psi4s102 x = i8Psi4s102S0 x := by
  unfold i8Psi4s102 i8Psi4s102S0 i8Psi4s102N0 i8Psi4s102N1 i8Psi4s102N2 i8Psi4s102N3 i8Psi4s102N4
    i8Psi4s102W
  ring

theorem continuousOn_i8Psi4s102 : ContinuousOn i8Psi4s102 (Ioc 0 1) := by
  rw [show i8Psi4s102 = fun x => i8Psi4s102S0 x from funext i8Psi4s102_eq_S]
  exact continuousOn_i8Psi4s102S0

theorem i8Psi4s102_one : i8Psi4s102 1 = -81 / 4 + zeta3 + 4 * zeta5 + π ^ 4 / 9 +
    17 / 12 * π ^ 2 := by
  rw [i8Psi4s102_eq_S]
  unfold i8Psi4s102S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one, hpl_zero_zero_zero_zero_at_one,
    hpl_zero_zero_zero_one_at_one, hpl_zero_zero_one_zero_at_one, hpl_zero_one_zero_zero_at_one,
    hpl_zero_zero_zero_zero_one_at_one, hpl_zero_zero_zero_one_zero_at_one,
    hpl_zero_zero_one_zero_zero_at_one, hpl_zero_one_zero_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s103` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s103S0 (x : ℝ) : ℝ :=
    (x ^ 4 + 51 / 2 * x ^ 3) / x ^ 2 +
    (-21 * x ^ 3 - 3 / 2 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (-9 / 2 * x ^ 2 - x ^ 3 / 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (2 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-x ^ 4 - 4 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (x ^ 3 + 5 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-12 * x ^ 3 - 10 * x ^ 2 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (2 * x ^ 4 + 4 * x ^ 3) / x ^ 2 * hpl [zero, zero, one] x +
    (2 * x ^ 4 + 4 * x ^ 3) / x ^ 2 * hpl [zero, one, zero] x +
    (-6 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero, one] x +
    (-12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one, zero] x +
    (-12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero, zero] x +
    (8) * hpl [zero, negOne, zero, zero] x +
    (8) * hpl [zero, zero, zero, one] x +
    (8) * hpl [zero, zero, one, zero] x +
    (8) * hpl [zero, one, zero, zero] x +
    (-8 * x + 4 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero, zero] x) +
    (8) * hpl [zero, negOne, zero, zero, one] x +
    (8) * hpl [zero, negOne, zero, one, zero] x

theorem continuousOn_i8Psi4s103S0 : ContinuousOn i8Psi4s103S0 (Ioc 0 1) := by
  unfold i8Psi4s103S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 + 51 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -21 * x ^ 3 - 3 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -9 / 2 * x ^ 2 - x ^ 3 / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + 5 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 10 * x ^ 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -6 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, one]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x + 4 * x ^ 3 + 12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one, zero])))

/-- Chunk 1 of `i8Psi4s103` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s103S1 (x : ℝ) : ℝ :=
    (8) * hpl [zero, negOne, one, zero, zero] x +
    (8) * hpl [zero, one, negOne, zero, zero] x

theorem continuousOn_i8Psi4s103S1 : ContinuousOn i8Psi4s103S1 (Ioc 0 1) := by
  unfold i8Psi4s103S1
  exact ((continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero, zero])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero, zero])))

theorem i8Psi4s103_eq_S (x : ℝ) : i8Psi4s103 x = i8Psi4s103S0 x + i8Psi4s103S1 x := by
  unfold i8Psi4s103 i8Psi4s103S0 i8Psi4s103S1 i8Psi4s103N0 i8Psi4s103N1 i8Psi4s103N2 i8Psi4s103N3
    i8Psi4s103N4 i8Psi4s103W
  ring

theorem continuousOn_i8Psi4s103 : ContinuousOn i8Psi4s103 (Ioc 0 1) := by
  rw [show i8Psi4s103 = fun x => i8Psi4s103S0 x + i8Psi4s103S1 x from funext i8Psi4s103_eq_S]
  exact (continuousOn_i8Psi4s103S0.add continuousOn_i8Psi4s103S1)

theorem i8Psi4s103_one : i8Psi4s103 1 = 53 / 2 + π ^ 4 / 2 - 64 * Li 4 (1 / 2) - 24 * zeta3 -
    8 / 3 * Real.log 2 ^ 4 - 5 / 6 * π ^ 2 + 67 / 2 * zeta5 - 2 * π ^ 2 * zeta3 +
    8 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s103_eq_S]
  unfold i8Psi4s103S0 i8Psi4s103S1
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_negOne_zero_zero_at_one,
    hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one, hpl_negOne_zero_zero_one_at_one,
    hpl_negOne_zero_one_zero_at_one, hpl_negOne_one_zero_zero_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_zero_zero_one_at_one, hpl_zero_zero_one_zero_at_one,
    hpl_zero_one_zero_zero_at_one, hpl_zero_negOne_zero_zero_one_at_one,
    hpl_zero_negOne_zero_one_zero_at_one, hpl_zero_negOne_one_zero_zero_at_one,
    hpl_zero_one_negOne_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s104` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s104S0 (x : ℝ) : ℝ :=
    (-42 * x ^ 3 - 3 * x ^ 4) / x ^ 2 +
    (4 * x ^ 4 + 32 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (2 * x ^ 3 + 10 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-24 * x ^ 3 - 20 * x ^ 2 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (4 * x ^ 4 + 8 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-12 * x ^ 2 - 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 8 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one] x +
    (-24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 8 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero] x +
    (16) * hpl [zero, negOne, zero] x +
    (16) * hpl [zero, zero, one] x +
    (16) * hpl [zero, one, zero] x +
    (-16 * x + 8 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (16) * hpl [zero, negOne, zero, one] x +
    (16) * hpl [zero, negOne, one, zero] x +
    (16) * hpl [zero, one, negOne, zero] x

theorem continuousOn_i8Psi4s104S0 : ContinuousOn i8Psi4s104S0 (Ioc 0 1) := by
  unfold i8Psi4s104S0
  exact (((((((((((((((i13_cont_coef (p := fun x => -42 * x ^ 3 - 3 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 32 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 3 + 10 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 3 - 20 * x ^ 2 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -16 * x + 8 * x ^ 3 + 24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero])))

theorem i8Psi4s104_eq_S (x : ℝ) : i8Psi4s104 x = i8Psi4s104S0 x := by
  unfold i8Psi4s104 i8Psi4s104S0 i8Psi4s104N0 i8Psi4s104N1 i8Psi4s104N2 i8Psi4s104N3 i8Psi4s104N4
    i8Psi4s104W
  ring

theorem continuousOn_i8Psi4s104 : ContinuousOn i8Psi4s104 (Ioc 0 1) := by
  rw [show i8Psi4s104 = fun x => i8Psi4s104S0 x from funext i8Psi4s104_eq_S]
  exact continuousOn_i8Psi4s104S0

theorem i8Psi4s104_one : i8Psi4s104 1 = -45 + 6 * π ^ 2 + 64 * zeta3 - 17 / 90 * π ^ 4 -
    16 * Real.log 2 * π ^ 2 := by
  rw [i8Psi4s104_eq_S]
  unfold i8Psi4s104S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_one_at_one, hpl_negOne_zero_one_at_one,
    hpl_negOne_one_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_zero_one_at_one,
    hpl_zero_one_zero_at_one, hpl_zero_negOne_zero_one_at_one, hpl_zero_negOne_one_zero_at_one,
    hpl_zero_one_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s105` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s105S0 (x : ℝ) : ℝ :=
    (31 * x ^ 3 + 3 / 2 * x ^ 4) / x ^ 2 +
    (-22 * x ^ 3 - 8 * x ^ 2 - 2 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (-x ^ 3 - 9 * x ^ 2 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-8 * x ^ 2 + 2 * x ^ 4 + 12 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-8 * x ^ 3 - 2 * x ^ 4 + 8 * x) / x ^ 2 * hpl [zero, one] x +
    (2 * x ^ 3 + 8 * x + 10 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-8) * hpl [zero, zero, zero] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, zero, one] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, one, zero] x +
    (-12 * x ^ 2 - 4 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-8) * hpl [zero, zero, zero, one] x +
    (-8) * hpl [zero, zero, one, zero] x +
    (-8) * hpl [zero, one, zero, zero] x

theorem continuousOn_i8Psi4s105S0 : ContinuousOn i8Psi4s105S0 (Ioc 0 1) := by
  unfold i8Psi4s105S0
  exact (((((((((((((i13_cont_coef (p := fun x => 31 * x ^ 3 + 3 / 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -22 * x ^ 3 - 8 * x ^ 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 9 * x ^ 2 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 2 + 2 * x ^ 4 + 12 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 3 - 2 * x ^ 4 + 8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 3 + 8 * x + 10 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 4 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero])))

theorem i8Psi4s105_eq_S (x : ℝ) : i8Psi4s105 x = i8Psi4s105S0 x := by
  unfold i8Psi4s105 i8Psi4s105S0 i8Psi4s105N0 i8Psi4s105N1 i8Psi4s105N2 i8Psi4s105N3 i8Psi4s105N4
    i8Psi4s105W
  ring

theorem continuousOn_i8Psi4s105 : ContinuousOn i8Psi4s105 (Ioc 0 1) := by
  rw [show i8Psi4s105 = fun x => i8Psi4s105S0 x from funext i8Psi4s105_eq_S]
  exact continuousOn_i8Psi4s105S0

theorem i8Psi4s105_one : i8Psi4s105 1 = 65 / 2 - 20 * zeta3 - 4 / 45 * π ^ 4 - π ^ 2 / 3 := by
  rw [i8Psi4s105_eq_S]
  unfold i8Psi4s105S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one, hpl_zero_zero_zero_one_at_one,
    hpl_zero_zero_one_zero_at_one, hpl_zero_one_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s106` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s106S0 (x : ℝ) : ℝ :=
    (11 * x ^ 4 + 108 * x + 145 * x ^ 3 - 4 / 3 * π ^ 2 * x + π ^ 2 * x ^ 4 / 4 +
      8 / 3 * π ^ 2 * x ^ 3) / x ^ 2 +
    (-145 * x ^ 3 - 22 * x ^ 4 + 108 * x - 8 / 3 * π ^ 2 * x ^ 3 - 4 / 3 * π ^ 2 * x -
      π ^ 2 * x ^ 4 / 2) / x ^ 2 * hpl [zero] x +
    (-16 * x + 3 * x ^ 4 + 13 * x ^ 2 + 32 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (25 * x ^ 4 + 32 * x ^ 2 + 92 * x + 132 * x ^ 3 + 2 * π ^ 2 * x ^ 3 - 2 / 3 * π ^ 2 * x +
      π ^ 2 * x ^ 4 / 3 + 2 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, zero] x +
    (-84 * x ^ 2 - 64 * x ^ 3 - 32 * x - 12 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-32 * x ^ 3 - 16 * x - 6 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-48 * x ^ 3 - 6 * x ^ 4 + 60 * x + 2 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, zero, zero] x +
    (-24 * x + 12 * x ^ 4 + 36 * x ^ 2 + 72 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero, zero] x +
    (-16 * x + 8 * x ^ 4 + 16 * x ^ 2 + 48 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero, zero] x +
    (-8 * x + 4 * x ^ 4 + 8 * x ^ 2 + 24 * x ^ 3) / x ^ 2 * hpl [zero, zero, negOne, zero] x +
    (-72 * x ^ 3 - 60 * x ^ 2 - 12 * x ^ 4 + 24 * x) / x ^ 2 * hpl [zero, zero, zero, zero] x +
    (72) * hpl [zero, negOne, zero, zero, zero] x +
    (48) * hpl [zero, zero, negOne, zero, zero] x +
    (24) * hpl [zero, zero, zero, negOne, zero] x +
    (-72) * hpl [zero, zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s106S0 : ContinuousOn i8Psi4s106S0 (Ioc 0 1) := by
  unfold i8Psi4s106S0
  exact (((((((((((((((i13_cont_coef (p := fun x => 11 * x ^ 4 + 108 * x + 145 * x ^ 3 -
    4 / 3 * π ^ 2 * x + π ^ 2 * x ^ 4 / 4 + 8 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -145 * x ^ 3 - 22 * x ^ 4 + 108 * x - 8 / 3 * π ^ 2 * x ^ 3 -
        4 / 3 * π ^ 2 * x - π ^ 2 * x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -16 * x + 3 * x ^ 4 + 13 * x ^ 2 +
        32 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 25 * x ^ 4 + 32 * x ^ 2 + 92 * x + 132 * x ^ 3 +
        2 * π ^ 2 * x ^ 3 - 2 / 3 * π ^ 2 * x + π ^ 2 * x ^ 4 / 3 +
        2 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -84 * x ^ 2 - 64 * x ^ 3 - 32 * x -
        12 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -32 * x ^ 3 - 16 * x - 6 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -48 * x ^ 3 - 6 * x ^ 4 + 60 * x +
        2 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x + 12 * x ^ 4 + 36 * x ^ 2 +
        72 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -16 * x + 8 * x ^ 4 + 16 * x ^ 2 +
        48 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x + 4 * x ^ 4 + 8 * x ^ 2 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -72 * x ^ 3 - 60 * x ^ 2 - 12 * x ^ 4 +
        24 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, zero])))

theorem i8Psi4s106_eq_S (x : ℝ) : i8Psi4s106 x = i8Psi4s106S0 x := by
  unfold i8Psi4s106 i8Psi4s106S0 i8Psi4s106N0 i8Psi4s106N1 i8Psi4s106N2 i8Psi4s106N3 i8Psi4s106N4
    i8Psi4s106W
  ring

theorem continuousOn_i8Psi4s106 : ContinuousOn i8Psi4s106 (Ioc 0 1) := by
  rw [show i8Psi4s106 = fun x => i8Psi4s106S0 x from funext i8Psi4s106_eq_S]
  exact continuousOn_i8Psi4s106S0

theorem i8Psi4s106_one : i8Psi4s106 1 = 264 - 90 * zeta5 - 63 * zeta3 - 13 / 12 * π ^ 2 -
    7 / 60 * π ^ 4 := by
  have h5 : hpl [zero, zero, zero, zero, zero] 1 = 0 := by
    rw [hpl_of_allZero (by decide)]
    simp
  rw [i8Psi4s106_eq_S]
  unfold i8Psi4s106S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_zero_zero_at_one, hpl_negOne_zero_zero_zero_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_zero_at_one, hpl_zero_zero_zero_negOne_zero_at_one, h5]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s107` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s107S0 (x : ℝ) : ℝ :=
    (-39 * x ^ 3 - 27 / 2 * x ^ 4 - 2 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 3) / x ^ 2 +
    (-56 * x ^ 2 + 6 * x ^ 4 + 34 * x ^ 3 + 4 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (5 * x ^ 2 + 21 * x ^ 3 + 56 * x + 2 * π ^ 2 * x ^ 2 - 4 / 3 * π ^ 2 * x +
      2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-24 * x ^ 3 - 20 * x ^ 2 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-24 * x ^ 2 + 2 * x ^ 4 + 12 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (10 * x ^ 4 + 16 * x ^ 3 + 24 * x + 32 * x ^ 2 +
      4 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, one] x +
    (-26 * x ^ 2 - 10 * x ^ 3 + 24 * x) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 8 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one] x +
    (-24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 8 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero] x +
    (16) * hpl [zero, negOne, zero] x +
    (-8) * hpl [zero, zero, zero] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, zero, one] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, one, zero] x +
    (-16 * x + 8 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (-12 * x ^ 2 - 4 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (16) * hpl [zero, negOne, zero, one] x +
    (16) * hpl [zero, negOne, one, zero] x +
    (-8) * hpl [zero, zero, zero, one] x +
    (-8) * hpl [zero, zero, one, zero] x +
    (16) * hpl [zero, one, negOne, zero] x

theorem continuousOn_i8Psi4s107S0 : ContinuousOn i8Psi4s107S0 (Ioc 0 1) := by
  unfold i8Psi4s107S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -39 * x ^ 3 - 27 / 2 * x ^ 4 -
    2 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -56 * x ^ 2 + 6 * x ^ 4 + 34 * x ^ 3 +
        4 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 5 * x ^ 2 + 21 * x ^ 3 + 56 * x + 2 * π ^ 2 * x ^ 2 -
        4 / 3 * π ^ 2 * x + 2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 3 - 20 * x ^ 2 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 + 2 * x ^ 4 + 12 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 10 * x ^ 4 + 16 * x ^ 3 + 24 * x + 32 * x ^ 2 +
        4 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -26 * x ^ 2 - 10 * x ^ 3 + 24 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -16 * x + 8 * x ^ 3 + 24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 4 * x ^ 3 + 8 * x) (by fun_prop)).mul
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

/-- Chunk 1 of `i8Psi4s107` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s107S1 (x : ℝ) : ℝ :=
    (-8) * hpl [zero, one, zero, zero] x

theorem continuousOn_i8Psi4s107S1 : ContinuousOn i8Psi4s107S1 (Ioc 0 1) := by
  unfold i8Psi4s107S1
  exact (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero]))

theorem i8Psi4s107_eq_S (x : ℝ) : i8Psi4s107 x = i8Psi4s107S0 x + i8Psi4s107S1 x := by
  unfold i8Psi4s107 i8Psi4s107S0 i8Psi4s107S1 i8Psi4s107N0 i8Psi4s107N1 i8Psi4s107N2 i8Psi4s107N3
    i8Psi4s107N4 i8Psi4s107W
  ring

theorem continuousOn_i8Psi4s107 : ContinuousOn i8Psi4s107 (Ioc 0 1) := by
  rw [show i8Psi4s107 = fun x => i8Psi4s107S0 x + i8Psi4s107S1 x from funext i8Psi4s107_eq_S]
  exact (continuousOn_i8Psi4s107S0.add continuousOn_i8Psi4s107S1)

theorem i8Psi4s107_one : i8Psi4s107 1 = -105 / 2 + 60 * zeta3 - π ^ 4 / 18 + 46 / 3 * π ^ 2 -
    16 * Real.log 2 * π ^ 2 := by
  rw [i8Psi4s107_eq_S]
  unfold i8Psi4s107S0 i8Psi4s107S1
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one,
    hpl_negOne_zero_one_at_one, hpl_negOne_one_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one,
    hpl_zero_negOne_zero_one_at_one, hpl_zero_negOne_one_zero_at_one, hpl_zero_zero_zero_one_at_one,
    hpl_zero_zero_one_zero_at_one, hpl_zero_one_negOne_zero_at_one, hpl_zero_one_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s108k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s108k0S0 (x : ℝ) : ℝ :=
    (-146 * x ^ 3 - 6 * x ^ 4 - 9 / 2 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 6) / x ^ 2 +
    (-32 * x ^ 2 + 6 * x ^ 4 + 76 * x ^ 3 + π ^ 2 * x ^ 4 / 6 + 2 / 3 * π ^ 2 * x ^ 2 +
      7 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (6 * x ^ 3 + 32 * x + 70 * x ^ 2 - 2 / 3 * π ^ 2 * x + π ^ 2 * x ^ 3 / 6 +
      13 / 6 * π ^ 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-32 + 2 / 3 * π ^ 2) * hpl [zero, zero] x +
    (12 * x ^ 4 + 32 * x + 64 * x ^ 3 + 2 * π ^ 2 * x ^ 3 - 2 / 3 * π ^ 2 * x +
      π ^ 2 * x ^ 4 / 3) / x ^ 2 * hpl [zero, one] x +
    (-76 * x ^ 2 - 12 * x ^ 3 + 32 * x - 7 / 3 * π ^ 2 * x ^ 2 - 2 / 3 * π ^ 2 * x -
      π ^ 2 * x ^ 3 / 3) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-48 * x ^ 3 - 16 * x ^ 2 - 8 * x ^ 4 + 16 * x +
      2 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, zero, one] x +
    (-48 * x ^ 3 - 16 * x ^ 2 - 8 * x ^ 4 + 16 * x +
      2 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, one, zero] x +
    (-48) * hpl [zero, zero, zero, one] x +
    (-48) * hpl [zero, zero, one, zero] x

theorem continuousOn_i8Psi4s108k0S0 : ContinuousOn i8Psi4s108k0S0 (Ioc 0 1) := by
  unfold i8Psi4s108k0S0
  exact ((((((((((i13_cont_coef (p := fun x => -146 * x ^ 3 - 6 * x ^ 4 - 9 / 2 * π ^ 2 * x ^ 3 -
    π ^ 2 * x ^ 4 / 6) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -32 * x ^ 2 + 6 * x ^ 4 + 76 * x ^ 3 + π ^ 2 * x ^ 4 / 6 +
        2 / 3 * π ^ 2 * x ^ 2 + 7 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 6 * x ^ 3 + 32 * x + 70 * x ^ 2 - 2 / 3 * π ^ 2 * x +
        π ^ 2 * x ^ 3 / 6 + 13 / 6 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 12 * x ^ 4 + 32 * x + 64 * x ^ 3 + 2 * π ^ 2 * x ^ 3 -
        2 / 3 * π ^ 2 * x + π ^ 2 * x ^ 4 / 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -76 * x ^ 2 - 12 * x ^ 3 + 32 * x - 7 / 3 * π ^ 2 * x ^ 2 -
        2 / 3 * π ^ 2 * x - π ^ 2 * x ^ 3 / 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -48 * x ^ 3 - 16 * x ^ 2 - 8 * x ^ 4 + 16 * x +
        2 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -48 * x ^ 3 - 16 * x ^ 2 - 8 * x ^ 4 + 16 * x +
        2 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero])))

theorem i8Psi4s108k0_eq_S (x : ℝ) : i8Psi4s108k0 x = i8Psi4s108k0S0 x := by
  unfold i8Psi4s108k0 i8Psi4s108k0S0 i8Psi4s108k0N0 i8Psi4s108k0N1 i8Psi4s108k0N2 i8Psi4s108k0N3
    i8Psi4s108k0N4 i8Psi4s108k0W
  ring

theorem continuousOn_i8Psi4s108k0 : ContinuousOn i8Psi4s108k0 (Ioc 0 1) := by
  rw [show i8Psi4s108k0 = fun x => i8Psi4s108k0S0 x from funext i8Psi4s108k0_eq_S]
  exact continuousOn_i8Psi4s108k0S0

theorem i8Psi4s108k0_one : i8Psi4s108k0 1 = -152 + 56 * zeta3 + 40 / 3 * π ^ 2 +
    121 / 90 * π ^ 4 - 2 * π ^ 2 * zeta3 := by
  rw [i8Psi4s108k0_eq_S]
  unfold i8Psi4s108k0S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_one_at_one,
    hpl_zero_one_zero_at_one, hpl_zero_zero_zero_one_at_one, hpl_zero_zero_one_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s108k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s108k1S0 (x : ℝ) : ℝ :=
    (-183 * x ^ 3 - 5 / 2 * x ^ 4) / x ^ 2 +
    (4 * x ^ 4 + 142 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (x ^ 3 + 41 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-100 * x ^ 3 - 6 * x ^ 4) / x ^ 2 * hpl [zero, zero] x +
    (2 * x ^ 4 + 40 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-42 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-16) * hpl [zero, zero, zero] x +
    (-40 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, zero, one] x +
    (-40 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, one, zero] x +
    (12 * x ^ 3 + 16 * x + 100 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-16 * x + 8 * x ^ 4 + 24 * x ^ 2 + 48 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero, one] x +
    (-16 * x + 8 * x ^ 4 + 24 * x ^ 2 + 48 * x ^ 3) / x ^ 2 * hpl [negOne, zero, one, zero] x +
    (-16 * x + 8 * x ^ 4 + 24 * x ^ 2 + 48 * x ^ 3) / x ^ 2 * hpl [negOne, one, zero, zero] x +
    (16) * hpl [zero, zero, zero, one] x +
    (16) * hpl [zero, zero, one, zero] x +
    (-32) * hpl [zero, one, zero, zero] x +
    (48) * hpl [zero, negOne, zero, zero, one] x +
    (48) * hpl [zero, negOne, zero, one, zero] x +
    (48) * hpl [zero, negOne, one, zero, zero] x

theorem continuousOn_i8Psi4s108k1S0 : ContinuousOn i8Psi4s108k1S0 (Ioc 0 1) := by
  unfold i8Psi4s108k1S0
  exact (((((((((((((((((((i13_cont_coef (p := fun x => -183 * x ^ 3 -
    5 / 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 142 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + 41 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -100 * x ^ 3 - 6 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 40 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -42 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -40 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -40 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => 12 * x ^ 3 + 16 * x + 100 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -16 * x + 8 * x ^ 4 + 24 * x ^ 2 +
        48 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, one]))).add
      ((i13_cont_coef (p := fun x => -16 * x + 8 * x ^ 4 + 24 * x ^ 2 +
        48 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one, zero]))).add
      ((i13_cont_coef (p := fun x => -16 * x + 8 * x ^ 4 + 24 * x ^ 2 +
        48 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero, zero]))).add
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

theorem i8Psi4s108k1_eq_S (x : ℝ) : i8Psi4s108k1 x = i8Psi4s108k1S0 x := by
  unfold i8Psi4s108k1 i8Psi4s108k1S0 i8Psi4s108k1N0 i8Psi4s108k1N1 i8Psi4s108k1N2 i8Psi4s108k1N3
    i8Psi4s108k1N4 i8Psi4s108k1W
  ring

theorem continuousOn_i8Psi4s108k1 : ContinuousOn i8Psi4s108k1 (Ioc 0 1) := by
  rw [show i8Psi4s108k1 = fun x => i8Psi4s108k1S0 x from funext i8Psi4s108k1_eq_S]
  exact continuousOn_i8Psi4s108k1S0

theorem i8Psi4s108k1_one : i8Psi4s108k1 1 = -371 / 2 + 7 * π ^ 2 + 44 * zeta3 +
    128 * Li 4 (1 / 2) - 16 / 9 * π ^ 4 + 16 / 3 * Real.log 2 ^ 4 + 819 / 2 * zeta5 -
    18 * π ^ 2 * zeta3 - 3 * Real.log 2 * π ^ 4 - 16 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s108k1_eq_S]
  unfold i8Psi4s108k1S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one, hpl_negOne_zero_zero_one_at_one,
    hpl_negOne_zero_one_zero_at_one, hpl_negOne_one_zero_zero_at_one, hpl_zero_zero_zero_one_at_one,
    hpl_zero_zero_one_zero_at_one, hpl_zero_one_zero_zero_at_one,
    hpl_zero_negOne_zero_zero_one_at_one, hpl_zero_negOne_zero_one_zero_at_one,
    hpl_zero_negOne_one_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s108k2` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s108k2S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 4 + 115 / 4 * x ^ 3) / x ^ 2 +
    (-12 * x ^ 2 - 29 / 2 * x ^ 3 - x ^ 4 / 4) / x ^ 2 * hpl [zero] x +
    (12 * x - 57 / 4 * x ^ 2 - x ^ 3 / 4) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-12) * hpl [zero, zero] x +
    (-14 * x ^ 3 + 12 * x - x ^ 4 / 2) / x ^ 2 * hpl [zero, one] x +
    (x ^ 3 / 2 + 12 * x + 29 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-30 * x ^ 2 - 24 * x ^ 3 - 8 * x - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one] x +
    (-30 * x ^ 2 - 24 * x ^ 3 - 8 * x - 2 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero] x +
    (3 * x ^ 4 + 8 * x ^ 2 + 12 * x + 36 * x ^ 3) / x ^ 2 * hpl [zero, zero, one] x +
    (3 * x ^ 4 + 8 * x ^ 2 + 12 * x + 36 * x ^ 3) / x ^ 2 * hpl [zero, one, zero] x +
    (-8 * x + 4 * x ^ 4 + 24 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero, one] x +
    (-8 * x + 4 * x ^ 4 + 24 * x ^ 3) / x ^ 2 * hpl [zero, negOne, one, zero] x +
    (-36 * x ^ 3 - 6 * x ^ 4 + 12 * x) / x ^ 2 * hpl [zero, zero, zero, one] x +
    (-36 * x ^ 3 - 6 * x ^ 4 + 12 * x) / x ^ 2 * hpl [zero, zero, one, zero] x +
    (24) * hpl [zero, zero, negOne, zero, one] x +
    (24) * hpl [zero, zero, negOne, one, zero] x +
    (-36) * hpl [zero, zero, zero, zero, one] x +
    (-36) * hpl [zero, zero, zero, one, zero] x

theorem continuousOn_i8Psi4s108k2S0 : ContinuousOn i8Psi4s108k2S0 (Ioc 0 1) := by
  unfold i8Psi4s108k2S0
  exact ((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 / 4 +
    115 / 4 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 29 / 2 * x ^ 3 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 12 * x - 57 / 4 * x ^ 2 - x ^ 3 / 4) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -14 * x ^ 3 + 12 * x - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 + 12 * x + 29 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -30 * x ^ 2 - 24 * x ^ 3 - 8 * x -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -30 * x ^ 2 - 24 * x ^ 3 - 8 * x -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => 3 * x ^ 4 + 8 * x ^ 2 + 12 * x + 36 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => 3 * x ^ 4 + 8 * x ^ 2 + 12 * x + 36 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x + 4 * x ^ 4 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one]))).add
      ((i13_cont_coef (p := fun x => -8 * x + 4 * x ^ 4 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero]))).add
      ((i13_cont_coef (p := fun x => -36 * x ^ 3 - 6 * x ^ 4 + 12 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      ((i13_cont_coef (p := fun x => -36 * x ^ 3 - 6 * x ^ 4 + 12 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one, zero])))

theorem i8Psi4s108k2_eq_S (x : ℝ) : i8Psi4s108k2 x = i8Psi4s108k2S0 x := by
  unfold i8Psi4s108k2 i8Psi4s108k2S0 i8Psi4s108k2N0 i8Psi4s108k2N1 i8Psi4s108k2N2 i8Psi4s108k2N3
    i8Psi4s108k2N4 i8Psi4s108k2W
  ring

theorem continuousOn_i8Psi4s108k2 : ContinuousOn i8Psi4s108k2 (Ioc 0 1) := by
  rw [show i8Psi4s108k2 = fun x => i8Psi4s108k2S0 x from funext i8Psi4s108k2_eq_S]
  exact continuousOn_i8Psi4s108k2S0

theorem i8Psi4s108k2_one : i8Psi4s108k2 1 = 29 - 80 * Li 4 (1 / 2) + 45 * zeta3 -
    387 / 4 * zeta5 - 10 / 3 * Real.log 2 ^ 4 - 5 / 12 * π ^ 2 + 8 / 9 * π ^ 4 -
    16 * Real.log 2 * π ^ 2 + 9 * π ^ 2 * zeta3 + 3 / 2 * Real.log 2 * π ^ 4 +
    10 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s108k2_eq_S]
  unfold i8Psi4s108k2S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_negOne_zero_one_at_one,
    hpl_negOne_one_zero_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one,
    hpl_zero_negOne_zero_one_at_one, hpl_zero_negOne_one_zero_at_one, hpl_zero_zero_zero_one_at_one,
    hpl_zero_zero_one_zero_at_one, hpl_zero_zero_negOne_zero_one_at_one,
    hpl_zero_zero_negOne_one_zero_at_one, hpl_zero_zero_zero_zero_one_at_one,
    hpl_zero_zero_zero_one_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s108k3` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s108k3S0 (x : ℝ) : ℝ :=
    (-65 * x ^ 3 - 5 / 8 * x ^ 4) / x ^ 2 +
    (65 * x ^ 3 + 5 / 4 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (-54 * x ^ 3 - 52 * x ^ 2 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-13 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero, zero] x +
    (4 * x ^ 4 + 52 * x ^ 2 + 56 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero] x +
    (2 * x ^ 4 + 8 * x ^ 2 + 28 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-12) * hpl [zero, zero, zero] x +
    (-8 * x + 2 * x ^ 3 + 26 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (-39 * x ^ 2 - 3 * x ^ 3 + 12 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (16) * hpl [zero, negOne, zero, zero] x +
    (8) * hpl [zero, zero, negOne, zero] x +
    (-8 * x + 4 * x ^ 4 + 24 * x ^ 3) / x ^ 2 * hpl [zero, one, negOne, zero] x +
    (-36 * x ^ 3 - 6 * x ^ 4 + 12 * x) / x ^ 2 * hpl [zero, one, zero, zero] x +
    (-56 * x ^ 2 - 16 * x - 8 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero, zero] x) +
    (-28 * x ^ 2 - 8 * x - 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne, zero] x) +
    (24) * hpl [zero, zero, one, negOne, zero] x +
    (-36) * hpl [zero, zero, one, zero, zero] x +
    (48) * hpl [zero, one, negOne, zero, zero] x +
    (24) * hpl [zero, one, zero, negOne, zero] x

theorem continuousOn_i8Psi4s108k3S0 : ContinuousOn i8Psi4s108k3S0 (Ioc 0 1) := by
  unfold i8Psi4s108k3S0
  exact (((((((((((((((((((i13_cont_coef (p := fun x => -65 * x ^ 3 -
    5 / 8 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 65 * x ^ 3 + 5 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -54 * x ^ 3 - 52 * x ^ 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -13 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 52 * x ^ 2 + 56 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 8 * x ^ 2 + 28 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x + 2 * x ^ 3 + 26 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -39 * x ^ 2 - 3 * x ^ 3 + 12 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x + 4 * x ^ 4 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -36 * x ^ 3 - 6 * x ^ 4 + 12 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -56 * x ^ 2 - 16 * x - 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -28 * x ^ 2 - 8 * x - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne, zero])))

theorem i8Psi4s108k3_eq_S (x : ℝ) : i8Psi4s108k3 x = i8Psi4s108k3S0 x := by
  unfold i8Psi4s108k3 i8Psi4s108k3S0 i8Psi4s108k3N0 i8Psi4s108k3N1 i8Psi4s108k3N2 i8Psi4s108k3N3
    i8Psi4s108k3N4 i8Psi4s108k3W
  ring

theorem continuousOn_i8Psi4s108k3 : ContinuousOn i8Psi4s108k3 (Ioc 0 1) := by
  rw [show i8Psi4s108k3 = fun x => i8Psi4s108k3S0 x from funext i8Psi4s108k3_eq_S]
  exact continuousOn_i8Psi4s108k3S0

theorem i8Psi4s108k3_one : i8Psi4s108k3 1 = -525 / 8 + 9 * π ^ 2 + 27 * zeta3 +
    80 * Li 4 (1 / 2) - 1377 / 4 * zeta5 - 49 / 40 * π ^ 4 + 10 / 3 * Real.log 2 ^ 4 -
    10 / 3 * π ^ 2 * Real.log 2 ^ 2 + 3 / 2 * Real.log 2 * π ^ 4 + 7 / 2 * π ^ 2 * zeta3 := by
  rw [i8Psi4s108k3_eq_S]
  unfold i8Psi4s108k3S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_one_negOne_zero_at_one,
    hpl_zero_one_zero_zero_at_one, hpl_zero_zero_one_negOne_zero_at_one,
    hpl_zero_zero_one_zero_zero_at_one, hpl_zero_one_negOne_zero_zero_at_one,
    hpl_zero_one_zero_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s108k4` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s108k4S0 (x : ℝ) : ℝ :=
    (42 * x ^ 3 + 3 / 8 * x ^ 4) / x ^ 2 +
    (-42 * x ^ 3 - 3 / 4 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (42 * x ^ 3 + 3 / 2 * x ^ 4) / x ^ 2 * hpl [zero, zero] x +
    (-42 * x ^ 3 - 3 * x ^ 4) / x ^ 2 * hpl [zero, zero, zero] x +
    (-12) * hpl [zero, zero, zero, zero] x +
    (6 * x ^ 3 + 12 * x + 42 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, zero, zero] x) +
    (-36) * hpl [zero, one, zero, zero, zero] x

theorem continuousOn_i8Psi4s108k4S0 : ContinuousOn i8Psi4s108k4S0 (Ioc 0 1) := by
  unfold i8Psi4s108k4S0
  exact (((((((i13_cont_coef (p := fun x => 42 * x ^ 3 + 3 / 8 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -42 * x ^ 3 - 3 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 42 * x ^ 3 + 3 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -42 * x ^ 3 - 3 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 6 * x ^ 3 + 12 * x + 42 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero, zero])))

theorem i8Psi4s108k4_eq_S (x : ℝ) : i8Psi4s108k4 x = i8Psi4s108k4S0 x := by
  unfold i8Psi4s108k4 i8Psi4s108k4S0 i8Psi4s108k4N0 i8Psi4s108k4N1 i8Psi4s108k4N2 i8Psi4s108k4N3
    i8Psi4s108k4N4 i8Psi4s108k4W
  ring

theorem continuousOn_i8Psi4s108k4 : ContinuousOn i8Psi4s108k4 (Ioc 0 1) := by
  rw [show i8Psi4s108k4 = fun x => i8Psi4s108k4S0 x from funext i8Psi4s108k4_eq_S]
  exact continuousOn_i8Psi4s108k4S0

theorem i8Psi4s108k4_one : i8Psi4s108k4 1 = 339 / 8 + 144 * zeta5 := by
  rw [i8Psi4s108k4_eq_S]
  unfold i8Psi4s108k4S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_zero_zero_at_one, hpl_zero_one_zero_zero_zero_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s108 : ContinuousOn i8Psi4s108 (Ioc 0 1) := by
  rw [show i8Psi4s108 = fun x => i8Psi4s108k0 x + i8Psi4s108k1 x + i8Psi4s108k2 x +
    i8Psi4s108k3 x + i8Psi4s108k4 x from rfl]
  exact ((((continuousOn_i8Psi4s108k0.add continuousOn_i8Psi4s108k1).add
    continuousOn_i8Psi4s108k2).add continuousOn_i8Psi4s108k3).add continuousOn_i8Psi4s108k4)

theorem i8Psi4s108_one : i8Psi4s108 1 = -1327 / 4 + 128 * Li 4 (1 / 2) + 172 * zeta3 -
    277 / 360 * π ^ 4 + 16 / 3 * Real.log 2 ^ 4 + 225 / 2 * zeta5 + 347 / 12 * π ^ 2 -
    16 * Real.log 2 * π ^ 2 - 16 / 3 * π ^ 2 * Real.log 2 ^ 2 - 15 / 2 * π ^ 2 * zeta3 := by
  unfold i8Psi4s108
  rw [i8Psi4s108k0_one, i8Psi4s108k1_one, i8Psi4s108k2_one, i8Psi4s108k3_one, i8Psi4s108k4_one]
  ring

/-- Chunk 0 of `i8Psi4s109` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s109S0 (x : ℝ) : ℝ :=
    (2 * x + 2 * x ^ 3 - x ^ 4 / 4) / x ^ 2 +
    (x ^ 4 / 2 - 2 * x ^ 3 + 2 * x) / x ^ 2 * hpl [zero] x +
    (-x ^ 4 + 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (2) * hpl [zero, zero, zero] x

theorem continuousOn_i8Psi4s109S0 : ContinuousOn i8Psi4s109S0 (Ioc 0 1) := by
  unfold i8Psi4s109S0
  exact ((((i13_cont_coef (p := fun x => 2 * x + 2 * x ^ 3 - x ^ 4 / 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - 2 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 + 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero])))

theorem i8Psi4s109_eq_S (x : ℝ) : i8Psi4s109 x = i8Psi4s109S0 x := by
  unfold i8Psi4s109 i8Psi4s109S0 i8Psi4s109N0 i8Psi4s109N1 i8Psi4s109N2 i8Psi4s109N3 i8Psi4s109N4
    i8Psi4s109W
  ring

theorem continuousOn_i8Psi4s109 : ContinuousOn i8Psi4s109 (Ioc 0 1) := by
  rw [show i8Psi4s109 = fun x => i8Psi4s109S0 x from funext i8Psi4s109_eq_S]
  exact continuousOn_i8Psi4s109S0

theorem i8Psi4s109_one : i8Psi4s109 1 = 15 / 4 := by
  rw [i8Psi4s109_eq_S]
  unfold i8Psi4s109S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one]
  norm_num

end QED.ThreeLoopD
