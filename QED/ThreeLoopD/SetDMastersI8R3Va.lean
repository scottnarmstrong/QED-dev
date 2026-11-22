/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R3Ph

/-!
# Set (d), master `I₈`: continuity and values at `1` of pieces of `Ψ₃`

For the pieces `a`, `b`, `d`, `e` of `Ψ₃`: each is continuous on `(0, 1]` (the words
beginning with `1` carry a factor `1 - ξ`), and its value at `ξ = 1` follows from the values of
the harmonic polylogarithms at `1`.

## Main results

* `QED.ThreeLoopD.continuousOn_i8Psi3a`, `QED.ThreeLoopD.i8Psi3a_one`.
* `QED.ThreeLoopD.continuousOn_i8Psi3b`, `QED.ThreeLoopD.i8Psi3b_one`.
* `QED.ThreeLoopD.continuousOn_i8Psi3d`, `QED.ThreeLoopD.i8Psi3d_one`.
* `QED.ThreeLoopD.continuousOn_i8Psi3e`, `QED.ThreeLoopD.i8Psi3e_one`.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-! ### The piece `a` -/

/-- `Ψ₃⁽a⁾` as a sum over words, with the factor `1 - ξ` of the words beginning with `1`
shown. -/
noncomputable def i8Psi3aS (x : ℝ) : ℝ :=
    (-781 / 16 * x ^ 4 - 569 / 8 * x ^ 3 + 781 / 8 * x - 4 * x * zeta3 - 4 * zeta3 * x ^ 3 -
      2 * zeta3 * x ^ 4 - 19 / 6 * π ^ 2 * x ^ 3 - 13 / 6 * π ^ 2 * x -
      13 / 12 * π ^ 2 * x ^ 4) / x ^ 2 +
    (-111 / 8 - 57 / 2 * x + π ^ 2 / 6 + 57 / 2 * x ^ 3 + 111 / 8 * x ^ 4 + π ^ 2 * x ^ 4 / 2 +
      2 * π ^ 2 * x ^ 2 + 4 / 3 * π ^ 2 * x + 4 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (111 / 2 * x + 111 / 4 * x ^ 4 + 225 / 2 * x ^ 3 + 565 / 8 * x ^ 2 + π ^ 2 * x ^ 2 / 2 +
      4 * zeta3 * x ^ 2 - 2 / 3 * π ^ 2 * x + 2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (13 / 2 - 6 * x ^ 3 + 6 * x - 13 / 2 * x ^ 4) / x ^ 2 * hpl [negOne, negOne] x +
    (-13 / 2 - 102 * x ^ 2 - 70 * x ^ 3 - 58 * x - 39 / 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-39 / 4 - 35 * x - 29 * x ^ 3 - 71 / 2 * x ^ 2 - 13 / 4 * x ^ 4 -
      2 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, negOne] x +
    (-26 * x ^ 3 + 26 * x + 31 / 2 * x ^ 2 + 4 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, zero] x +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, negOne] x +
    (6 + 10 * x ^ 4 + 32 * x + 32 * x ^ 3 + 48 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (5 + 3 * x ^ 4 + 16 * x + 16 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (-2 - 24 * x + 2 * x ^ 4 + 24 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero] x +
    (3 + x ^ 4 + 8 * x + 8 * x ^ 3 + 18 * x ^ 2) / x ^ 2 * hpl [zero, negOne, negOne] x +
    (-3 - x ^ 4 - 24 * x - 6 * x ^ 2 + 8 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-9 / 2 - 21 * x ^ 2 - 20 * x - 4 * x ^ 3 -
      3 / 2 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne] x +
    (-18 * x ^ 2 - 16 * x ^ 3 - 2 * x ^ 4 + 8 * x) / x ^ 2 * hpl [zero, zero, zero] x +
    (-8) * hpl [zero, negOne, negOne, negOne] x +
    (-8) * hpl [zero, negOne, negOne, zero] x +
    (4) * hpl [zero, negOne, zero, negOne] x +
    (40) * hpl [zero, negOne, zero, zero] x +
    (4) * hpl [zero, zero, negOne, negOne] x +
    (28) * hpl [zero, zero, negOne, zero] x +
    (10) * hpl [zero, zero, zero, negOne] x +
    (-20) * hpl [zero, zero, zero, zero] x

theorem continuousOn_i8Psi3aS : ContinuousOn i8Psi3aS (Ioc 0 1) := by
  unfold i8Psi3aS
  exact (((((((((((((((((((((((i13_cont_coef (p := fun x => -781 / 16 * x ^ 4 -
    569 / 8 * x ^ 3 + 781 / 8 * x - 4 * x * zeta3 - 4 * zeta3 * x ^ 3 - 2 * zeta3 * x ^ 4 -
    19 / 6 * π ^ 2 * x ^ 3 - 13 / 6 * π ^ 2 * x - 13 / 12 * π ^ 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -111 / 8 - 57 / 2 * x + π ^ 2 / 6 + 57 / 2 * x ^ 3 +
        111 / 8 * x ^ 4 + π ^ 2 * x ^ 4 / 2 + 2 * π ^ 2 * x ^ 2 + 4 / 3 * π ^ 2 * x +
        4 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 111 / 2 * x + 111 / 4 * x ^ 4 + 225 / 2 * x ^ 3 +
        565 / 8 * x ^ 2 + π ^ 2 * x ^ 2 / 2 + 4 * zeta3 * x ^ 2 - 2 / 3 * π ^ 2 * x +
        2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 13 / 2 - 6 * x ^ 3 + 6 * x - 13 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -13 / 2 - 102 * x ^ 2 - 70 * x ^ 3 - 58 * x -
        39 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -39 / 4 - 35 * x - 29 * x ^ 3 - 71 / 2 * x ^ 2 -
        13 / 4 * x ^ 4 - 2 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -26 * x ^ 3 + 26 * x + 31 / 2 * x ^ 2 +
        4 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => 6 + 10 * x ^ 4 + 32 * x + 32 * x ^ 3 +
        48 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 5 + 3 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 - 24 * x + 2 * x ^ 4 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 3 + x ^ 4 + 8 * x + 8 * x ^ 3 + 18 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => -3 - x ^ 4 - 24 * x - 6 * x ^ 2 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -9 / 2 - 21 * x ^ 2 - 20 * x - 4 * x ^ 3 -
        3 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -18 * x ^ 2 - 16 * x ^ 3 - 2 * x ^ 4 +
        8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero])))

theorem i8Psi3a_eq_S (x : ℝ) : i8Psi3a x = i8Psi3aS x := by
  unfold i8Psi3a i8Psi3aS i8Psi3aN0 i8Psi3aN1 i8Psi3aN2 i8Psi3aN3 i8Psi3aN4 i8Psi3aW
  ring

theorem continuousOn_i8Psi3a : ContinuousOn i8Psi3a (Ioc 0 1) := by
  rw [show i8Psi3a = i8Psi3aS from funext i8Psi3a_eq_S]
  exact continuousOn_i8Psi3aS

theorem i8Psi3a_one : i8Psi3a 1 = -357 / 16 - 9 / 2 * zeta3 + 77 / 180 * π ^ 4 +
  133 / 24 * π ^ 2 := by
  rw [i8Psi3a_eq_S]
  unfold i8Psi3aS
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_negOne_at_one, hpl_negOne_zero_at_one,
    hpl_zero_negOne_at_one, hpl_zero_zero_at_one, hpl_negOne_negOne_negOne_at_one,
    hpl_negOne_negOne_zero_at_one, hpl_negOne_zero_negOne_at_one, hpl_negOne_zero_zero_at_one,
    hpl_zero_negOne_negOne_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_zero_zero_at_one, hpl_zero_negOne_negOne_negOne_at_one,
    hpl_zero_negOne_negOne_zero_at_one, hpl_zero_negOne_zero_negOne_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_zero_negOne_negOne_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_at_one,
    hpl_zero_zero_zero_zero_at_one]
  norm_num
  ring

/-! ### The piece `b` -/

/-- `Ψ₃⁽b⁾` as a sum over words, with the factor `1 - ξ` of the words beginning with `1`
shown. -/
noncomputable def i8Psi3bS (x : ℝ) : ℝ :=
    (-54 * x ^ 3 + 40 * x - 23 / 4 * x ^ 4 - 2 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x / 3 -
      π ^ 2 * x ^ 4 / 12) / x ^ 2 +
    (-48 * x ^ 2 + 33 * x ^ 3 + 40 * x - 11 / 2 * x ^ 4 - π ^ 2 * x / 3 - π ^ 2 * x ^ 3 / 3 -
      π ^ 2 * x ^ 4 / 6 + 2 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (17 * x ^ 3 + 21 * x ^ 2 + 48 * x + π ^ 2 * x ^ 2 - 2 / 3 * π ^ 2 * x +
      π ^ 2 * x ^ 3 / 3) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-x ^ 4 - 11 * x ^ 2 - 8 * x ^ 3 - 4 * x) / x ^ 2 * hpl [negOne, zero] x +
    (-8 * x ^ 2 + 10 * x ^ 4 + 24 * x ^ 3 + 28 * x +
      π ^ 2 * x ^ 2 / 3) / x ^ 2 * hpl [zero, zero] x +
    (10 * x ^ 4 + 24 * x + 24 * x ^ 2 + 28 * x ^ 3 +
      2 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, one] x +
    (-38 * x ^ 2 - 10 * x ^ 3 + 24 * x) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one] x +
    (-12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero] x +
    (-4 * x - 4 * x ^ 3 - 2 * x ^ 4 + 8 * x ^ 2) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-16 * x ^ 2 - 12 * x ^ 3 + 12 * x) / x ^ 2 * hpl [zero, zero, zero] x +
    (-8 * x ^ 2 - 8 * x ^ 3 + 8 * x) / x ^ 2 * hpl [zero, zero, one] x +
    (-8 * x ^ 2 - 8 * x ^ 3 + 8 * x) / x ^ 2 * hpl [zero, one, zero] x +
    (-8 * x + 4 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (8 * x + 8 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (8) * hpl [zero, negOne, zero, zero] x +
    (8) * hpl [zero, negOne, zero, one] x +
    (8) * hpl [zero, negOne, one, zero] x +
    (4) * hpl [zero, zero, negOne, zero] x +
    (-24) * hpl [zero, zero, zero, zero] x +
    (-16) * hpl [zero, zero, zero, one] x +
    (-16) * hpl [zero, zero, one, zero] x +
    (8) * hpl [zero, one, negOne, zero] x +
    (-16) * hpl [zero, one, zero, zero] x

theorem continuousOn_i8Psi3bS : ContinuousOn i8Psi3bS (Ioc 0 1) := by
  unfold i8Psi3bS
  exact (((((((((((((((((((((((((i13_cont_coef (p := fun x => -54 * x ^ 3 + 40 * x -
    23 / 4 * x ^ 4 - 2 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x / 3 - π ^ 2 * x ^ 4 / 12) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -48 * x ^ 2 + 33 * x ^ 3 + 40 * x - 11 / 2 * x ^ 4 -
        π ^ 2 * x / 3 - π ^ 2 * x ^ 3 / 3 - π ^ 2 * x ^ 4 / 6 +
        2 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 17 * x ^ 3 + 21 * x ^ 2 + 48 * x + π ^ 2 * x ^ 2 -
        2 / 3 * π ^ 2 * x + π ^ 2 * x ^ 3 / 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 11 * x ^ 2 - 8 * x ^ 3 - 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 2 + 10 * x ^ 4 + 24 * x ^ 3 + 28 * x +
        π ^ 2 * x ^ 2 / 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 10 * x ^ 4 + 24 * x + 24 * x ^ 2 + 28 * x ^ 3 +
        2 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -38 * x ^ 2 - 10 * x ^ 3 + 24 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x - 4 * x ^ 3 - 2 * x ^ 4 + 8 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -16 * x ^ 2 - 12 * x ^ 3 + 12 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 2 - 8 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 2 - 8 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x + 4 * x ^ 3 + 12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 8 * x + 8 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero])))

theorem i8Psi3b_eq_S (x : ℝ) : i8Psi3b x = i8Psi3bS x := by
  unfold i8Psi3b i8Psi3bS i8Psi3bN0 i8Psi3bN1 i8Psi3bN2 i8Psi3bN3 i8Psi3bN4 i8Psi3bW
  ring

theorem continuousOn_i8Psi3b : ContinuousOn i8Psi3b (Ioc 0 1) := by
  rw [show i8Psi3b = i8Psi3bS from funext i8Psi3b_eq_S]
  exact continuousOn_i8Psi3bS

theorem i8Psi3b_one : i8Psi3b 1 = -79 / 4 + 39 * zeta3 - 2 / 45 * π ^ 4 + 61 / 4 * π ^ 2 -
  8 * Real.log 2 * π ^ 2 := by
  rw [i8Psi3b_eq_S]
  unfold i8Psi3bS
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one,
    hpl_negOne_zero_zero_at_one, hpl_negOne_zero_one_at_one, hpl_negOne_one_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_zero_zero_at_one, hpl_zero_zero_one_at_one,
    hpl_zero_one_zero_at_one, hpl_zero_negOne_zero_zero_at_one, hpl_zero_negOne_zero_one_at_one,
    hpl_zero_negOne_one_zero_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_zero_at_one, hpl_zero_zero_zero_one_at_one, hpl_zero_zero_one_zero_at_one,
    hpl_zero_one_negOne_zero_at_one, hpl_zero_one_zero_zero_at_one]
  norm_num
  ring

/-! ### The piece `d` -/

/-- `Ψ₃⁽d⁾` as a sum over words, with the factor `1 - ξ` of the words beginning with `1`
shown. -/
noncomputable def i8Psi3dS (x : ℝ) : ℝ :=
    (-75 / 2 * x ^ 3 - 13 / 4 * x ^ 4 + 3 / 2 * x) / x ^ 2 +
    (-3 / 2 - 15 * x + 15 * x ^ 3 + 3 / 2 * x ^ 4) / x ^ 2 * hpl [negOne] x +
    (-3 * x ^ 4 + 3 * x + 11 * x ^ 3 + 17 / 2 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (5 * x + 8 * x ^ 3 + 13 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-3 - 11 * x ^ 2 - 10 * x - 2 * x ^ 3 + 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-5 - 8 * x + 5 * x ^ 4 + 8 * x ^ 3) / x ^ 2 * hpl [negOne, one] x +
    (-3 - 10 * x - 2 * x ^ 3 + 2 * x ^ 4 + 13 * x ^ 2) / x ^ 2 * hpl [zero, negOne] x +
    (2 * x + 3 * x ^ 4 + 9 * x ^ 2 + 10 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (2 * x + 3 * x ^ 4 + 10 * x ^ 3 + 11 * x ^ 2) / x ^ 2 * hpl [zero, one] x +
    (-5 - 13 * x - 13 * x ^ 2 - 5 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (-13 * x ^ 2 - 3 * x ^ 3 + 2 * x) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one] x +
    (-2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero] x +
    (-2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4 + 2 * x ^ 2) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-2 - 16 * x ^ 2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, one] x +
    (-2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4 + 2 * x ^ 2) / x ^ 2 * hpl [zero, zero, negOne] x +
    (2) * hpl [zero, zero, zero] x +
    (2) * hpl [zero, zero, one] x +
    (-2 - 16 * x ^ 2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, one, negOne] x +
    (2) * hpl [zero, one, zero] x +
    (-2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (-2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x)

theorem continuousOn_i8Psi3dS : ContinuousOn i8Psi3dS (Ioc 0 1) := by
  unfold i8Psi3dS
  exact (((((((((((((((((((((((i13_cont_coef (p := fun x => -75 / 2 * x ^ 3 - 13 / 4 * x ^ 4 +
    3 / 2 * x) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -3 / 2 - 15 * x + 15 * x ^ 3 +
        3 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -3 * x ^ 4 + 3 * x + 11 * x ^ 3 +
        17 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 5 * x + 8 * x ^ 3 + 13 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -3 - 11 * x ^ 2 - 10 * x - 2 * x ^ 3 +
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -5 - 8 * x + 5 * x ^ 4 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -3 - 10 * x - 2 * x ^ 3 + 2 * x ^ 4 +
        13 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => 2 * x + 3 * x ^ 4 + 9 * x ^ 2 + 10 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x + 3 * x ^ 4 + 10 * x ^ 3 + 11 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -5 - 13 * x - 13 * x ^ 2 - 5 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -13 * x ^ 2 - 3 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4 +
        2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      ((i13_cont_coef (p := fun x => -2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4 +
        2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne])))

theorem i8Psi3d_eq_S (x : ℝ) : i8Psi3d x = i8Psi3dS x := by
  unfold i8Psi3d i8Psi3dS i8Psi3dN0 i8Psi3dN1 i8Psi3dN2 i8Psi3dN3 i8Psi3dN4 i8Psi3dW
  ring

theorem continuousOn_i8Psi3d : ContinuousOn i8Psi3d (Ioc 0 1) := by
  rw [show i8Psi3d = i8Psi3dS from funext i8Psi3d_eq_S]
  exact continuousOn_i8Psi3dS

theorem i8Psi3d_one : i8Psi3d 1 = -157 / 4 + 17 * zeta3 + 19 / 3 * π ^ 2 -
  8 * Real.log 2 * π ^ 2 := by
  rw [i8Psi3d_eq_S]
  unfold i8Psi3dS
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_negOne_one_at_one,
    hpl_zero_negOne_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_negOne_zero_zero_at_one,
    hpl_negOne_zero_one_at_one, hpl_negOne_one_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_negOne_one_at_one, hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_one_at_one, hpl_zero_one_negOne_at_one, hpl_zero_one_zero_at_one]
  norm_num
  ring

/-! ### The piece `e` -/

/-- `Ψ₃⁽e⁾` as a sum over words, with the factor `1 - ξ` of the words beginning with `1`
shown. -/
noncomputable def i8Psi3eS (x : ℝ) : ℝ :=
    (x ^ 3 / 2 - 15 / 16 * x ^ 4 + 3 / 4 * x) / x ^ 2 +
    (-1 / 2 + x ^ 3 + x ^ 4 / 2 - x) / x ^ 2 * hpl [negOne] x +
    (-2 * x ^ 2 - 11 / 8 * x ^ 4 + 5 / 4 * x + 15 / 4 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-19 / 4 * x ^ 2 + 5 / 2 * x + 11 / 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (1 / 2 - 2 * x ^ 3 + 2 * x - x ^ 4 / 2) / x ^ 2 * hpl [negOne, negOne] x +
    (-3 / 4 + x - x ^ 3 + 3 / 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-3 / 2 - 2 * x ^ 3 + 2 * x + 3 / 2 * x ^ 4) / x ^ 2 * hpl [negOne, one] x +
    (-1 + x ^ 4 - 2 * x ^ 2) / x ^ 2 * hpl [zero, negOne] x +
    (1 / 4) * hpl [zero, zero] x +
    (1 / 2) * hpl [zero, one] x +
    (-3 / 2 + x / 2 + x ^ 2 / 2 - 3 / 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (1 - x ^ 4) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, one] x +
    (1 - x ^ 4) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, one, negOne] x +
    (1 - x ^ 4 - 2 * x ^ 2) / x ^ 2 * hpl [zero, negOne, negOne] x +
    (-1 / 2 + x ^ 4 / 2 - x ^ 2) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-1 + x ^ 4 - 2 * x ^ 2) / x ^ 2 * hpl [zero, negOne, one] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [zero, zero, negOne] x +
    (-1 + x ^ 4 - 2 * x ^ 2) / x ^ 2 * hpl [zero, one, negOne] x +
    (2 + 2 * x + 2 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, negOne] x) +
    (-1 - x - x ^ 2 - x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (4) * hpl [zero, negOne, negOne, zero] x +
    (8) * hpl [zero, negOne, negOne, one] x +
    (4) * hpl [zero, negOne, zero, negOne] x +
    (8) * hpl [zero, negOne, one, negOne] x +
    (4) * hpl [zero, zero, negOne, negOne] x +
    (-2) * hpl [zero, zero, negOne, zero] x +
    (-4) * hpl [zero, zero, negOne, one] x +
    (-4) * hpl [zero, zero, zero, negOne] x +
    (-4) * hpl [zero, zero, one, negOne] x +
    (8) * hpl [zero, one, negOne, negOne] x +
    (-4) * hpl [zero, one, zero, negOne] x

theorem continuousOn_i8Psi3eS : ContinuousOn i8Psi3eS (Ioc 0 1) := by
  unfold i8Psi3eS
  exact (((((((((((((((((((((((((((((((((i13_cont_coef (p := fun x => x ^ 3 / 2 -
    15 / 16 * x ^ 4 + 3 / 4 * x) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 3 + x ^ 4 / 2 - x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 2 - 11 / 8 * x ^ 4 + 5 / 4 * x +
        15 / 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -19 / 4 * x ^ 2 + 5 / 2 * x +
        11 / 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => 1 / 2 - 2 * x ^ 3 + 2 * x - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -3 / 4 + x - x ^ 3 + 3 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -3 / 2 - 2 * x ^ 3 + 2 * x + 3 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4 - 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -3 / 2 + x / 2 + x ^ 2 / 2 - 3 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, one]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, negOne]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4 - 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 4 / 2 - x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4 - 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4 - 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x + 2 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 - x - x ^ 2 - x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne])))

theorem i8Psi3e_eq_S (x : ℝ) : i8Psi3e x = i8Psi3eS x := by
  unfold i8Psi3e i8Psi3eS i8Psi3eN0 i8Psi3eN1 i8Psi3eN2 i8Psi3eN3 i8Psi3eN4 i8Psi3eW
  ring

theorem continuousOn_i8Psi3e : ContinuousOn i8Psi3e (Ioc 0 1) := by
  rw [show i8Psi3e = i8Psi3eS from funext i8Psi3e_eq_S]
  exact continuousOn_i8Psi3eS

theorem i8Psi3e_one : i8Psi3e 1 = 5 / 16 - π ^ 2 / 12 - π ^ 4 / 360 := by
  rw [i8Psi3e_eq_S]
  unfold i8Psi3eS
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_negOne_at_one, hpl_negOne_zero_at_one,
    hpl_negOne_one_at_one, hpl_zero_negOne_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one,
    hpl_negOne_negOne_zero_at_one, hpl_negOne_negOne_one_at_one, hpl_negOne_zero_negOne_at_one,
    hpl_negOne_one_negOne_at_one, hpl_zero_negOne_negOne_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_negOne_one_at_one, hpl_zero_zero_negOne_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_negOne_negOne_zero_at_one, hpl_zero_negOne_negOne_one_at_one,
    hpl_zero_negOne_zero_negOne_at_one, hpl_zero_negOne_one_negOne_at_one,
    hpl_zero_zero_negOne_negOne_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_one_at_one, hpl_zero_zero_zero_negOne_at_one,
    hpl_zero_zero_one_negOne_at_one, hpl_zero_one_negOne_negOne_at_one,
    hpl_zero_one_zero_negOne_at_one]
  norm_num
  ring

end QED.ThreeLoopD
