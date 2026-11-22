/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R3Va

/-!
# Set (d), master `I₈`: continuity and values at `1` of pieces of `Ψ₃`

For the pieces `f`, `g`, `h` of `Ψ₃`: each is continuous on `(0, 1]` (the words
beginning with `1` carry a factor `1 - ξ`), and its value at `ξ = 1` follows from the values of
the harmonic polylogarithms at `1`.

## Main results

* `QED.ThreeLoopD.continuousOn_i8Psi3f`, `QED.ThreeLoopD.i8Psi3f_one`.
* `QED.ThreeLoopD.continuousOn_i8Psi3g`, `QED.ThreeLoopD.i8Psi3g_one`.
* `QED.ThreeLoopD.continuousOn_i8Psi3h`, `QED.ThreeLoopD.i8Psi3h_one`.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-! ### The piece `f` -/

/-- `Ψ₃⁽f⁾` as a sum over words, with the factor `1 - ξ` of the words beginning with `1`
shown. -/
noncomputable def i8Psi3fS (x : ℝ) : ℝ :=
    (-15 * x ^ 3 + 10 * x - 7 / 8 * x ^ 4) / x ^ 2 +
    (-16 * x ^ 2 - 2 * x ^ 3 + 10 * x - 5 / 4 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (3 * x ^ 3 + 16 * x + 17 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-16 * x ^ 2 + 10 * x + 10 * x ^ 3 - 3 / 2 * x ^ 4) / x ^ 2 * hpl [zero, zero] x +
    (-24 * x ^ 2 - 4 * x ^ 4 + 12 * x ^ 3 + 16 * x) / x ^ 2 * hpl [zero, one] x +
    (-8 * x ^ 2 + 4 * x ^ 3 + 16 * x) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (2 * x ^ 2 + 10 * x ^ 3 + 24 * x) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-4 * x ^ 2 + 3 * x ^ 4 + 6 * x + 6 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, zero, one] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, one, zero] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 3 + 16 * x ^ 2) / x ^ 2 * hpl [zero, one, one] x +
    (-12 * x ^ 2 - 4 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-12 * x ^ 2 - 4 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, one] x) +
    (-12 * x ^ 2 - 4 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, one, zero] x) +
    (-6) * hpl [zero, zero, zero, zero] x +
    (-8) * hpl [zero, zero, zero, one] x +
    (-8) * hpl [zero, zero, one, zero] x +
    (-8) * hpl [zero, zero, one, one] x +
    (-8) * hpl [zero, one, zero, zero] x +
    (-8) * hpl [zero, one, zero, one] x +
    (-8) * hpl [zero, one, one, zero] x

theorem continuousOn_i8Psi3fS : ContinuousOn i8Psi3fS (Ioc 0 1) := by
  unfold i8Psi3fS
  exact (((((((((((((((((((((i13_cont_coef (p := fun x => -15 * x ^ 3 + 10 * x -
    7 / 8 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -16 * x ^ 2 - 2 * x ^ 3 + 10 * x -
        5 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 3 * x ^ 3 + 16 * x + 17 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -16 * x ^ 2 + 10 * x + 10 * x ^ 3 -
        3 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 4 * x ^ 4 + 12 * x ^ 3 +
        16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 2 + 4 * x ^ 3 + 16 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 2 + 10 * x ^ 3 + 24 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 2 + 3 * x ^ 4 + 6 * x + 6 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 3 + 16 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 4 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 4 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 4 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero])))

theorem i8Psi3f_eq_S (x : ℝ) : i8Psi3f x = i8Psi3fS x := by
  unfold i8Psi3f i8Psi3fS i8Psi3fN0 i8Psi3fN1 i8Psi3fN2 i8Psi3fN3 i8Psi3fN4 i8Psi3fW
  ring

theorem continuousOn_i8Psi3f : ContinuousOn i8Psi3f (Ioc 0 1) := by
  rw [show i8Psi3f = i8Psi3fS from funext i8Psi3f_eq_S]
  exact continuousOn_i8Psi3fS

theorem i8Psi3f_one : i8Psi3f 1 = -47 / 8 + 16 * zeta3 - π ^ 4 / 15 := by
  rw [i8Psi3f_eq_S]
  unfold i8Psi3fS
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one, hpl_zero_one_one_at_one,
    hpl_zero_zero_zero_zero_at_one, hpl_zero_zero_zero_one_at_one, hpl_zero_zero_one_zero_at_one,
    hpl_zero_zero_one_one_at_one, hpl_zero_one_zero_zero_at_one, hpl_zero_one_zero_one_at_one,
    hpl_zero_one_one_zero_at_one]
  norm_num
  ring

/-! ### The piece `g` -/

/-- `Ψ₃⁽g⁾` as a sum over words, with the factor `1 - ξ` of the words beginning with `1`
shown. -/
noncomputable def i8Psi3gS (x : ℝ) : ℝ :=
    (-25 / 8 * x ^ 3 - 5 / 16 * x ^ 4 + x / 8) / x ^ 2 +
    (-1 / 8 - 3 / 2 * x + x ^ 4 / 8 + 3 / 2 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (-3 / 4 * x ^ 3 - x ^ 4 / 2 + x / 4 + 7 / 8 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (x ^ 3 + x / 2 + 5 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-1 / 4 + x ^ 3 - x + x ^ 4 / 4) / x ^ 2 * hpl [negOne, zero] x +
    (-1 / 2 + x ^ 4 / 2 - 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [negOne, one] x +
    (-1 / 4 + x ^ 3 - x + x ^ 4 / 4 + 5 / 2 * x ^ 2) / x ^ 2 * hpl [zero, negOne] x +
    (x / 2 - 3 / 4 * x ^ 4 - x ^ 2 / 4 + 3 / 2 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (x + 3 * x ^ 3 - 3 / 2 * x ^ 4 - x ^ 2 / 2) / x ^ 2 * hpl [zero, one] x +
    (-1 / 2 - 5 / 2 * x - 5 / 2 * x ^ 2 - x ^ 3 / 2) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (x - 3 / 2 * x ^ 2 + 3 / 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-3 * x ^ 2 + 2 * x + 3 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-1 / 2 + x ^ 4 / 2) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [negOne, zero, one] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [negOne, one, zero] x +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [negOne, one, one] x +
    (-1 / 2 + x ^ 2 + x ^ 4 / 2) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-1 + x ^ 4 + 2 * x ^ 2) / x ^ 2 * hpl [zero, negOne, one] x +
    (-1 / 2 + x ^ 2 + x ^ 4 / 2) / x ^ 2 * hpl [zero, zero, negOne] x +
    (1 / 2) * hpl [zero, zero, zero] x +
    (1) * hpl [zero, zero, one] x +
    (-1 + x ^ 4 + 2 * x ^ 2) / x ^ 2 * hpl [zero, one, negOne] x +
    (1) * hpl [zero, one, zero] x +
    (2) * hpl [zero, one, one] x +
    (-1 - x - x ^ 2 - x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (-2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, one] x) +
    (-1 - x - x ^ 2 - x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (-2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one, negOne] x) +
    (-2) * hpl [zero, negOne, zero, zero] x +
    (-4) * hpl [zero, negOne, zero, one] x +
    (-4) * hpl [zero, negOne, one, zero] x +
    (-8) * hpl [zero, negOne, one, one] x +
    (-2) * hpl [zero, zero, negOne, zero] x +
    (-4) * hpl [zero, zero, negOne, one] x +
    (-2) * hpl [zero, zero, zero, negOne] x +
    (-4) * hpl [zero, zero, one, negOne] x +
    (-4) * hpl [zero, one, negOne, zero] x +
    (-8) * hpl [zero, one, negOne, one] x +
    (-4) * hpl [zero, one, zero, negOne] x +
    (-8) * hpl [zero, one, one, negOne] x

theorem continuousOn_i8Psi3gS : ContinuousOn i8Psi3gS (Ioc 0 1) := by
  unfold i8Psi3gS
  exact ((((((((((((((((((((((((((((((((((((((((i13_cont_coef (p := fun x => -25 / 8 * x ^ 3 -
    5 / 16 * x ^ 4 + x / 8) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -1 / 8 - 3 / 2 * x + x ^ 4 / 8 +
        3 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -3 / 4 * x ^ 3 - x ^ 4 / 2 + x / 4 +
        7 / 8 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + x / 2 + 5 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -1 / 4 + x ^ 3 - x + x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 4 / 2 - 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -1 / 4 + x ^ 3 - x + x ^ 4 / 4 +
        5 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x / 2 - 3 / 4 * x ^ 4 - x ^ 2 / 4 +
        3 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x + 3 * x ^ 3 - 3 / 2 * x ^ 4 - x ^ 2 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 - 5 / 2 * x - 5 / 2 * x ^ 2 -
        x ^ 3 / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => x - 3 / 2 * x ^ 2 + 3 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -3 * x ^ 2 + 2 * x + 3 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 2 + x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4 + 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 2 + x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4 + 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -1 - x - x ^ 2 - x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, one]))).add
      ((i13_cont_coef (p := fun x => -1 - x - x ^ 2 - x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, negOne])))

theorem i8Psi3g_eq_S (x : ℝ) : i8Psi3g x = i8Psi3gS x := by
  unfold i8Psi3g i8Psi3gS i8Psi3gN0 i8Psi3gN1 i8Psi3gN2 i8Psi3gN3 i8Psi3gN4 i8Psi3gW
  ring

theorem continuousOn_i8Psi3g : ContinuousOn i8Psi3g (Ioc 0 1) := by
  rw [show i8Psi3g = i8Psi3gS from funext i8Psi3g_eq_S]
  exact continuousOn_i8Psi3gS

theorem i8Psi3g_one : i8Psi3g 1 = -53 / 16 - π ^ 4 / 15 + 3 / 2 * zeta3 + 13 / 24 * π ^ 2 := by
  rw [i8Psi3g_eq_S]
  unfold i8Psi3gS
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_negOne_one_at_one,
    hpl_zero_negOne_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_negOne_zero_zero_at_one,
    hpl_negOne_zero_one_at_one, hpl_negOne_one_zero_at_one, hpl_negOne_one_one_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_negOne_one_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_zero_zero_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_zero_at_one, hpl_zero_one_one_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_negOne_zero_one_at_one, hpl_zero_negOne_one_zero_at_one,
    hpl_zero_negOne_one_one_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_one_at_one, hpl_zero_zero_zero_negOne_at_one,
    hpl_zero_zero_one_negOne_at_one, hpl_zero_one_negOne_zero_at_one,
    hpl_zero_one_negOne_one_at_one, hpl_zero_one_zero_negOne_at_one, hpl_zero_one_one_negOne_at_one]
  norm_num
  ring

/-! ### The piece `h` -/

/-- `Ψ₃⁽h⁾` as a sum over words, with the factor `1 - ξ` of the words beginning with `1`
shown. -/
noncomputable def i8Psi3hS (x : ℝ) : ℝ :=
    (x - 3 / 4 * x ^ 3 - x ^ 4 / 16) / x ^ 2 +
    (x - 2 * x ^ 2 - x ^ 3 / 2 - x ^ 4 / 8) / x ^ 2 * hpl [zero] x +
    (2 * x + x ^ 3 / 4 + 5 / 4 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x - 2 * x ^ 2 - x ^ 4 / 4) / x ^ 2 * hpl [zero, zero] x +
    (-4 * x ^ 2 + 2 * x - x ^ 4 / 2) / x ^ 2 * hpl [zero, one] x +
    (x ^ 2 / 2 + x ^ 3 / 2 + 2 * x) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (x ^ 2 + x ^ 3 + 4 * x) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (x + x ^ 3 - 2 * x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [zero, zero, zero] x +
    (-x ^ 4 - 4 * x ^ 2 + 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [zero, zero, one] x +
    (-x ^ 4 - 4 * x ^ 2 + 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [zero, one, zero] x +
    (-8 * x ^ 2 - 2 * x ^ 4 + 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [zero, one, one] x +
    (x ^ 3 - x ^ 2 + 2 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-2 * x ^ 2 + 2 * x ^ 3 + 4 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, one] x) +
    (-2 * x ^ 2 + 2 * x ^ 3 + 4 * x) / x ^ 2 * ((1 - x) * hpl [one, one, zero] x) +
    (-4 * x ^ 2 + 4 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, one, one] x) +
    (1) * hpl [zero, zero, zero, zero] x +
    (2) * hpl [zero, zero, zero, one] x +
    (2) * hpl [zero, zero, one, zero] x +
    (4) * hpl [zero, zero, one, one] x +
    (2) * hpl [zero, one, zero, zero] x +
    (4) * hpl [zero, one, zero, one] x +
    (4) * hpl [zero, one, one, zero] x +
    (8) * hpl [zero, one, one, one] x

theorem continuousOn_i8Psi3hS : ContinuousOn i8Psi3hS (Ioc 0 1) := by
  unfold i8Psi3hS
  exact (((((((((((((((((((((((i13_cont_coef (p := fun x => x - 3 / 4 * x ^ 3 -
    x ^ 4 / 16) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x - 2 * x ^ 2 - x ^ 3 / 2 - x ^ 4 / 8) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 2 * x + x ^ 3 / 4 + 5 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x - 2 * x ^ 2 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 2 + 2 * x - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 / 2 + x ^ 3 / 2 + 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 + x ^ 3 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      ((i13_cont_coef (p := fun x => x + x ^ 3 - 2 * x ^ 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 4 * x ^ 2 + 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 4 * x ^ 2 + 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 2 - 2 * x ^ 4 + 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - x ^ 2 + 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 2 + 2 * x ^ 3 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 2 + 2 * x ^ 3 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 2 + 4 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, one])))

theorem i8Psi3h_eq_S (x : ℝ) : i8Psi3h x = i8Psi3hS x := by
  unfold i8Psi3h i8Psi3hS i8Psi3hN0 i8Psi3hN1 i8Psi3hN2 i8Psi3hN3 i8Psi3hN4 i8Psi3hW
  ring

theorem continuousOn_i8Psi3h : ContinuousOn i8Psi3h (Ioc 0 1) := by
  rw [show i8Psi3h = i8Psi3hS from funext i8Psi3h_eq_S]
  exact continuousOn_i8Psi3hS

theorem i8Psi3h_one : i8Psi3h 1 = 3 / 16 - zeta3 - 5 / 12 * π ^ 2 + π ^ 4 / 10 := by
  rw [i8Psi3h_eq_S]
  unfold i8Psi3hS
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one, hpl_zero_one_one_at_one,
    hpl_zero_zero_zero_zero_at_one, hpl_zero_zero_zero_one_at_one, hpl_zero_zero_one_zero_at_one,
    hpl_zero_zero_one_one_at_one, hpl_zero_one_zero_zero_at_one, hpl_zero_one_zero_one_at_one,
    hpl_zero_one_one_zero_at_one, hpl_zero_one_one_one_at_one]
  norm_num
  ring

end QED.ThreeLoopD
