/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4V7

/-!
# Set (d), master `I₈`: continuity and values at `1` of the sub-pieces 119 to 127 of `Ψ₄`

Each sub-piece `Ψ₄⁽ⁿ⁾` is continuous on `(0, 1]` (the words beginning with `1` carry a factor
`1 - ξ`), and its value at `ξ = 1` follows from the values of the harmonic polylogarithms at `1`.

## Main results

* `QED.ThreeLoopD.continuousOn_i8Psi4s119`, `QED.ThreeLoopD.i8Psi4s119_one` and their
  companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- Chunk 0 of `i8Psi4s119k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s119k0S0 (x : ℝ) : ℝ :=
    (-x ^ 4 + 7 * x ^ 3) / x ^ 2 +
    (x ^ 4 / 2 - x ^ 3 - 3 / 2 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (-11 / 2 * x ^ 2 + 3 / 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-2 * x ^ 2 + 2 * x ^ 4) / x ^ 2 * hpl [negOne, one] x +
    (x ^ 2 - x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (x ^ 3 - 5 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-4 * x ^ 3 - 2 * x ^ 4 + 2 * x ^ 2 + 4 * x) / x ^ 2 * hpl [negOne, negOne, one] x +
    (-4 * x ^ 3 - 2 * x ^ 2 + 2 * x ^ 4 + 4 * x) / x ^ 2 * hpl [negOne, one, one] x +
    (-8) * hpl [zero, negOne, one] x +
    (-4) * hpl [zero, one, negOne] x +
    (-4) * hpl [zero, one, one] x +
    (-2 * x ^ 3 + 2 * x ^ 2 + 4 * x) / x ^ 2 * ((1 - x) * hpl [one, negOne, one] x) +
    (-2 * x ^ 3 + 2 * x ^ 2 + 4 * x) / x ^ 2 * ((1 - x) * hpl [one, one, negOne] x) +
    (4 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, one, one] x +
    (4 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, one, negOne, one] x +
    (4 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, one, one, negOne] x +
    (-4) * hpl [zero, negOne, negOne, one] x +
    (4) * hpl [zero, negOne, one, one] x +
    (4) * hpl [zero, one, negOne, one] x +
    (4) * hpl [zero, one, one, negOne] x

theorem continuousOn_i8Psi4s119k0S0 : ContinuousOn i8Psi4s119k0S0 (Ioc 0 1) := by
  unfold i8Psi4s119k0S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -x ^ 4 + 7 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - x ^ 3 - 3 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -11 / 2 * x ^ 2 + 3 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 - x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - 5 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 3 - 2 * x ^ 4 + 2 * x ^ 2 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, one]))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 3 - 2 * x ^ 2 + 2 * x ^ 4 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 3 + 2 * x ^ 2 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, one]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 3 + 2 * x ^ 2 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, negOne]))).add
      ((i13_cont_coef (p := fun x => 4 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, one, one]))).add
      ((i13_cont_coef (p := fun x => 4 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, negOne, one]))).add
      ((i13_cont_coef (p := fun x => 4 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, negOne])))

/-- Chunk 1 of `i8Psi4s119k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s119k0S1 (x : ℝ) : ℝ :=
    (4 + 4 * x + 4 * x ^ 2 + 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, negOne, one] x) +
    (16) * hpl [zero, negOne, negOne, one, one] x +
    (16) * hpl [zero, negOne, one, negOne, one] x +
    (16) * hpl [zero, negOne, one, one, negOne] x +
    (16) * hpl [zero, one, negOne, negOne, one] x

theorem continuousOn_i8Psi4s119k0S1 : ContinuousOn i8Psi4s119k0S1 (Ioc 0 1) := by
  unfold i8Psi4s119k0S1
  exact ((((((i13_cont_coef (p := fun x => 4 + 4 * x + 4 * x ^ 2 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, negOne, one])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, negOne, one])))

theorem i8Psi4s119k0_eq_S (x : ℝ) : i8Psi4s119k0 x = i8Psi4s119k0S0 x + i8Psi4s119k0S1 x := by
  unfold i8Psi4s119k0 i8Psi4s119k0S0 i8Psi4s119k0S1 i8Psi4s119k0N0 i8Psi4s119k0N1 i8Psi4s119k0N2
    i8Psi4s119k0N3 i8Psi4s119k0N4 i8Psi4s119k0W
  ring

theorem continuousOn_i8Psi4s119k0 : ContinuousOn i8Psi4s119k0 (Ioc 0 1) := by
  rw [show i8Psi4s119k0 = fun x => i8Psi4s119k0S0 x +
    i8Psi4s119k0S1 x from funext i8Psi4s119k0_eq_S]
  exact (continuousOn_i8Psi4s119k0S0.add continuousOn_i8Psi4s119k0S1)

theorem i8Psi4s119k0_one : i8Psi4s119k0 1 = 6 - 48 * Li 5 (1 / 2) - 13 * zeta3 -
    4 * Li 4 (1 / 2) - 2 * Real.log 2 - Real.log 2 ^ 4 / 6 + 13 / 360 * π ^ 4 +
    16 / 15 * Real.log 2 ^ 5 + 163 / 4 * zeta5 + Real.log 2 * π ^ 2 + π ^ 2 * zeta3 / 2 +
    16 * Real.log 2 * Li 4 (1 / 2) - 19 / 45 * Real.log 2 * π ^ 4 - π ^ 2 * Real.log 2 ^ 2 / 3 +
    7 / 2 * Real.log 2 * zeta3 := by
  rw [i8Psi4s119k0_eq_S]
  unfold i8Psi4s119k0S0 i8Psi4s119k0S1
  rw [hpl_negOne_at_one, hpl_negOne_one_at_one, hpl_negOne_negOne_one_at_one,
    hpl_negOne_one_one_at_one, hpl_zero_negOne_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_one_at_one, hpl_negOne_negOne_one_one_at_one, hpl_negOne_one_negOne_one_at_one,
    hpl_negOne_one_one_negOne_at_one, hpl_zero_negOne_negOne_one_at_one,
    hpl_zero_negOne_one_one_at_one, hpl_zero_one_negOne_one_at_one, hpl_zero_one_one_negOne_at_one,
    hpl_zero_negOne_negOne_one_one_at_one, hpl_zero_negOne_one_negOne_one_at_one,
    hpl_zero_negOne_one_one_negOne_at_one, hpl_zero_one_negOne_negOne_one_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s119k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s119k1S0 (x : ℝ) : ℝ :=
    (-7 * x ^ 3 - x ^ 4 / 2) / x ^ 2 +
    (x ^ 4 + 7 * x ^ 2 + 8 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (-x ^ 4 - 6 * x ^ 3 - 5 * x ^ 2) / x ^ 2 * hpl [negOne, negOne] x +
    (-x ^ 3 - 3 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (-4 * x ^ 3 - 2 * x ^ 4 + 2 * x ^ 2 + 4 * x) / x ^ 2 * hpl [negOne, one, negOne] x +
    (-4) * hpl [zero, negOne, negOne] x +
    (-4) * hpl [zero, one, negOne] x +
    (2 * x ^ 3 + 4 * x + 6 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, negOne] x) +
    (-4) * hpl [zero, negOne, one, negOne] x +
    (-4) * hpl [zero, one, negOne, negOne] x +
    (4 + 4 * x + 4 * x ^ 2 + 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, one, negOne] x) +
    (4 + 4 * x + 4 * x ^ 2 + 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one, negOne, negOne] x) +
    (16) * hpl [zero, one, negOne, one, negOne] x +
    (16) * hpl [zero, one, one, negOne, negOne] x

theorem continuousOn_i8Psi4s119k1S0 : ContinuousOn i8Psi4s119k1S0 (Ioc 0 1) := by
  unfold i8Psi4s119k1S0
  exact ((((((((((((((i13_cont_coef (p := fun x => -7 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 7 * x ^ 2 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 6 * x ^ 3 - 5 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 3 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 3 - 2 * x ^ 4 + 2 * x ^ 2 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 3 + 4 * x + 6 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x + 4 * x ^ 2 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, one, negOne]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x + 4 * x ^ 2 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, negOne, negOne])))

theorem i8Psi4s119k1_eq_S (x : ℝ) : i8Psi4s119k1 x = i8Psi4s119k1S0 x := by
  unfold i8Psi4s119k1 i8Psi4s119k1S0 i8Psi4s119k1N0 i8Psi4s119k1N1 i8Psi4s119k1N2 i8Psi4s119k1N3
    i8Psi4s119k1N4 i8Psi4s119k1W
  ring

theorem continuousOn_i8Psi4s119k1 : ContinuousOn i8Psi4s119k1 (Ioc 0 1) := by
  rw [show i8Psi4s119k1 = fun x => i8Psi4s119k1S0 x from funext i8Psi4s119k1_eq_S]
  exact continuousOn_i8Psi4s119k1S0

theorem i8Psi4s119k1_one : i8Psi4s119k1 1 = -15 / 2 - 6 * Real.log 2 ^ 2 + 8 * Li 4 (1 / 2) +
    16 * Real.log 2 + 64 * Li 5 (1 / 2) - 213 / 4 * zeta5 - 8 / 15 * Real.log 2 ^ 5 -
    7 / 120 * π ^ 4 + Real.log 2 ^ 4 / 3 + 7 / 2 * zeta3 - Real.log 2 * π ^ 2 +
    7 * zeta3 * Real.log 2 ^ 2 - 4 / 9 * π ^ 2 * Real.log 2 ^ 3 - π ^ 2 * zeta3 / 2 +
    π ^ 2 * Real.log 2 ^ 2 / 6 + 19 / 45 * Real.log 2 * π ^ 4 := by
  rw [i8Psi4s119k1_eq_S]
  unfold i8Psi4s119k1S0
  rw [hpl_negOne_at_one, hpl_negOne_negOne_at_one, hpl_negOne_one_negOne_at_one,
    hpl_zero_negOne_negOne_at_one, hpl_zero_one_negOne_at_one, hpl_zero_negOne_one_negOne_at_one,
    hpl_zero_one_negOne_negOne_at_one, hpl_zero_one_negOne_one_negOne_at_one,
    hpl_zero_one_one_negOne_negOne_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s119 : ContinuousOn i8Psi4s119 (Ioc 0 1) := by
  rw [show i8Psi4s119 = fun x => i8Psi4s119k0 x + i8Psi4s119k1 x from rfl]
  exact (continuousOn_i8Psi4s119k0.add continuousOn_i8Psi4s119k1)

theorem i8Psi4s119_one : i8Psi4s119 1 = -3 / 2 - 6 * Real.log 2 ^ 2 + 4 * Li 4 (1 / 2) +
    14 * Real.log 2 + 16 * Li 5 (1 / 2) - 25 / 2 * zeta5 - 19 / 2 * zeta3 - π ^ 4 / 45 +
    Real.log 2 ^ 4 / 6 + 8 / 15 * Real.log 2 ^ 5 + 7 * zeta3 * Real.log 2 ^ 2 +
    16 * Real.log 2 * Li 4 (1 / 2) - 4 / 9 * π ^ 2 * Real.log 2 ^ 3 - π ^ 2 * Real.log 2 ^ 2 / 6 +
    7 / 2 * Real.log 2 * zeta3 := by
  unfold i8Psi4s119
  rw [i8Psi4s119k0_one, i8Psi4s119k1_one]
  ring

/-- Chunk 0 of `i8Psi4s120k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s120k0S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 + 7 / 2 * x ^ 3) / x ^ 2 +
    (-5 / 4 * x ^ 2 - 3 / 2 * x ^ 3 - x ^ 4 / 4) / x ^ 2 * hpl [negOne] x +
    (-9 / 4 * x ^ 2 - 3 / 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-x ^ 4 - 5 * x ^ 2 - 3 * x - 3 * x ^ 3) / x ^ 2 * hpl [negOne, one] x +
    (1) * hpl [zero, negOne] x +
    (4) * hpl [zero, one] x +
    (x ^ 3 / 2 - x + 3 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (x ^ 2 / 2 - x - x ^ 3 / 2) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-1 - x ^ 4 + 2 * x ^ 2) / x ^ 2 * hpl [negOne, one, one] x +
    (x ^ 2 + x ^ 4 - 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [zero, negOne, one] x +
    (1) * hpl [zero, one, negOne] x +
    (-1) * hpl [zero, one, one] x +
    (-1 + x ^ 2 + x ^ 3 - x) / x ^ 2 * ((1 - x) * hpl [one, negOne, one] x) +
    (-1 + x ^ 2 + x ^ 3 - x) / x ^ 2 * ((1 - x) * hpl [one, one, negOne] x) +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, one, one] x +
    (2) * hpl [zero, zero, negOne, one] x +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [zero, one, negOne, one] x +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [zero, one, one, negOne] x +
    (-2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne, one] x) +
    (-8) * hpl [zero, zero, negOne, one, one] x

theorem continuousOn_i8Psi4s120k0S0 : ContinuousOn i8Psi4s120k0S0 (Ioc 0 1) := by
  unfold i8Psi4s120k0S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 / 2 +
    7 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -5 / 4 * x ^ 2 - 3 / 2 * x ^ 3 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -9 / 4 * x ^ 2 - 3 / 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 5 * x ^ 2 - 3 * x - 3 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 - x + 3 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 / 2 - x - x ^ 3 / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 4 + 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 + x ^ 4 - 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 2 + x ^ 3 - x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, one]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 2 + x ^ 3 - x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, one]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one, one])))

/-- Chunk 1 of `i8Psi4s120k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s120k0S1 (x : ℝ) : ℝ :=
    (-8) * hpl [zero, zero, one, negOne, one] x +
    (-8) * hpl [zero, zero, one, one, negOne] x +
    (-8) * hpl [zero, one, zero, negOne, one] x

theorem continuousOn_i8Psi4s120k0S1 : ContinuousOn i8Psi4s120k0S1 (Ioc 0 1) := by
  unfold i8Psi4s120k0S1
  exact (((continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne, one])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne, one])))

theorem i8Psi4s120k0_eq_S (x : ℝ) : i8Psi4s120k0 x = i8Psi4s120k0S0 x + i8Psi4s120k0S1 x := by
  unfold i8Psi4s120k0 i8Psi4s120k0S0 i8Psi4s120k0S1 i8Psi4s120k0N0 i8Psi4s120k0N1 i8Psi4s120k0N2
    i8Psi4s120k0N3 i8Psi4s120k0N4 i8Psi4s120k0W
  ring

theorem continuousOn_i8Psi4s120k0 : ContinuousOn i8Psi4s120k0 (Ioc 0 1) := by
  rw [show i8Psi4s120k0 = fun x => i8Psi4s120k0S0 x +
    i8Psi4s120k0S1 x from funext i8Psi4s120k0_eq_S]
  exact (continuousOn_i8Psi4s120k0S0.add continuousOn_i8Psi4s120k0S1)

theorem i8Psi4s120k0_one : i8Psi4s120k0 1 = 4 - 3 * Real.log 2 + 4 * Li 4 (1 / 2) +
    6 * Real.log 2 ^ 2 + 48 * Li 5 (1 / 2) - 371 / 8 * zeta5 - π ^ 2 / 4 - π ^ 4 / 90 +
    Real.log 2 ^ 4 / 6 + 4 / 15 * Real.log 2 ^ 5 + 5 / 4 * zeta3 - 7 * zeta3 * Real.log 2 ^ 2 +
    16 * Real.log 2 * Li 4 (1 / 2) - 11 / 12 * π ^ 2 * zeta3 - Real.log 2 * π ^ 2 / 4 -
    π ^ 2 * Real.log 2 ^ 2 / 6 + 83 / 180 * Real.log 2 * π ^ 4 := by
  rw [i8Psi4s120k0_eq_S]
  unfold i8Psi4s120k0S0 i8Psi4s120k0S1
  rw [hpl_negOne_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one, hpl_zero_one_at_one,
    hpl_negOne_one_one_at_one, hpl_zero_negOne_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_one_at_one, hpl_zero_negOne_one_one_at_one, hpl_zero_zero_negOne_one_at_one,
    hpl_zero_one_negOne_one_at_one, hpl_zero_one_one_negOne_at_one,
    hpl_zero_zero_negOne_one_one_at_one, hpl_zero_zero_one_negOne_one_at_one,
    hpl_zero_zero_one_one_negOne_at_one, hpl_zero_one_zero_negOne_one_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s120k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s120k1S0 (x : ℝ) : ℝ :=
    (5 * x ^ 3 + x ^ 4 / 4) / x ^ 2 +
    (-5 * x ^ 2 - 11 / 2 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [negOne] x +
    (x ^ 4 / 2 + 2 * x ^ 2 + 3 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (x ^ 3 / 2 - 2 * x + 5 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (2) * hpl [zero, zero, negOne] x +
    (x ^ 4 - 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [zero, one, negOne] x +
    (-x ^ 3 - 3 * x ^ 2 - 2 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (2) * hpl [zero, zero, one, negOne] x +
    (2) * hpl [zero, one, zero, negOne] x +
    (-2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, one, negOne] x) +
    (-2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one, zero, negOne] x) +
    (-8) * hpl [zero, one, zero, one, negOne] x +
    (-8) * hpl [zero, one, one, zero, negOne] x

theorem continuousOn_i8Psi4s120k1S0 : ContinuousOn i8Psi4s120k1S0 (Ioc 0 1) := by
  unfold i8Psi4s120k1S0
  exact (((((((((((((i13_cont_coef (p := fun x => 5 * x ^ 3 + x ^ 4 / 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -5 * x ^ 2 - 11 / 2 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 2 * x ^ 2 + 3 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 - 2 * x + 5 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 3 * x ^ 2 - 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero, negOne])))

theorem i8Psi4s120k1_eq_S (x : ℝ) : i8Psi4s120k1 x = i8Psi4s120k1S0 x := by
  unfold i8Psi4s120k1 i8Psi4s120k1S0 i8Psi4s120k1N0 i8Psi4s120k1N1 i8Psi4s120k1N2 i8Psi4s120k1N3
    i8Psi4s120k1N4 i8Psi4s120k1W
  ring

theorem continuousOn_i8Psi4s120k1 : ContinuousOn i8Psi4s120k1 (Ioc 0 1) := by
  rw [show i8Psi4s120k1 = fun x => i8Psi4s120k1S0 x from funext i8Psi4s120k1_eq_S]
  exact continuousOn_i8Psi4s120k1S0

theorem i8Psi4s120k1_one : i8Psi4s120k1 1 = 21 / 4 + zeta3 / 2 - 64 * Li 5 (1 / 2) -
    11 * Real.log 2 - 8 * Li 4 (1 / 2) - 4 / 5 * Real.log 2 ^ 5 - Real.log 2 ^ 4 / 3 +
    11 / 24 * π ^ 2 + 13 / 180 * π ^ 4 + 401 / 8 * zeta5 - 32 * Real.log 2 * Li 4 (1 / 2) -
    83 / 180 * Real.log 2 * π ^ 4 - 7 / 2 * Real.log 2 * zeta3 +
    π ^ 2 * Real.log 2 ^ 2 / 3 + Real.log 2 * π ^ 2 / 4 + 4 / 9 * π ^ 2 * Real.log 2 ^ 3 +
    17 / 12 * π ^ 2 * zeta3 := by
  rw [i8Psi4s120k1_eq_S]
  unfold i8Psi4s120k1S0
  rw [hpl_negOne_at_one, hpl_zero_negOne_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_one_negOne_at_one, hpl_zero_zero_one_negOne_at_one, hpl_zero_one_zero_negOne_at_one,
    hpl_zero_one_zero_one_negOne_at_one, hpl_zero_one_one_zero_negOne_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s120 : ContinuousOn i8Psi4s120 (Ioc 0 1) := by
  rw [show i8Psi4s120 = fun x => i8Psi4s120k0 x + i8Psi4s120k1 x from rfl]
  exact (continuousOn_i8Psi4s120k0.add continuousOn_i8Psi4s120k1)

theorem i8Psi4s120_one : i8Psi4s120 1 = 37 / 4 - 16 * Li 5 (1 / 2) - 14 * Real.log 2 -
    4 * Li 4 (1 / 2) + 6 * Real.log 2 ^ 2 - 8 / 15 * Real.log 2 ^ 5 - Real.log 2 ^ 4 / 6 +
    5 / 24 * π ^ 2 + 7 / 4 * zeta3 + 11 / 180 * π ^ 4 + 15 / 4 * zeta5 + π ^ 2 * zeta3 / 2 -
    16 * Real.log 2 * Li 4 (1 / 2) - 7 * zeta3 * Real.log 2 ^ 2 - 7 / 2 * Real.log 2 * zeta3 +
    π ^ 2 * Real.log 2 ^ 2 / 6 + 4 / 9 * π ^ 2 * Real.log 2 ^ 3 := by
  unfold i8Psi4s120
  rw [i8Psi4s120k0_one, i8Psi4s120k1_one]
  ring

/-- Chunk 0 of `i8Psi4s121` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s121S0 (x : ℝ) : ℝ :=
    (-2 * x ^ 3 + 10 * x - 7 / 8 * x ^ 4) / x ^ 2 +
    (2 * x ^ 3 + 10 * x + 7 / 4 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (-2 * x ^ 3 + 10 * x - 7 / 2 * x ^ 4) / x ^ 2 * hpl [zero, zero] x +
    (3 * x ^ 4 + 4 * x ^ 2 + 6 * x + 6 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero] x +
    (-6) * hpl [zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s121S0 : ContinuousOn i8Psi4s121S0 (Ioc 0 1) := by
  unfold i8Psi4s121S0
  exact (((((i13_cont_coef (p := fun x => -2 * x ^ 3 + 10 * x - 7 / 8 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 3 + 10 * x + 7 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 3 + 10 * x - 7 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 3 * x ^ 4 + 4 * x ^ 2 + 6 * x + 6 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero])))

theorem i8Psi4s121_eq_S (x : ℝ) : i8Psi4s121 x = i8Psi4s121S0 x := by
  unfold i8Psi4s121 i8Psi4s121S0 i8Psi4s121N0 i8Psi4s121N1 i8Psi4s121N2 i8Psi4s121N3 i8Psi4s121N4
    i8Psi4s121W
  ring

theorem continuousOn_i8Psi4s121 : ContinuousOn i8Psi4s121 (Ioc 0 1) := by
  rw [show i8Psi4s121 = fun x => i8Psi4s121S0 x from funext i8Psi4s121_eq_S]
  exact continuousOn_i8Psi4s121S0

theorem i8Psi4s121_one : i8Psi4s121 1 = 57 / 8 := by
  rw [i8Psi4s121_eq_S]
  unfold i8Psi4s121S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_zero_zero_at_one]
  norm_num

/-- Chunk 0 of `i8Psi4s122` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s122S0 (x : ℝ) : ℝ :=
    (-311 / 8 * x ^ 3 - 73 / 8 * x - 3 / 2 * x ^ 4) / x ^ 2 +
    (-7 / 8 - 12 * x + 12 * x ^ 3 + 7 / 8 * x ^ 4) / x ^ 2 * hpl [negOne] x +
    (-33 / 4 * x + 17 / 8 * x ^ 4 + 89 / 8 * x ^ 2 + 111 / 4 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-7 / 4 - 12 * x - 12 * x ^ 3 - 41 / 2 * x ^ 2 - 7 / 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-7 / 4 - 12 * x - 12 * x ^ 3 - 7 / 4 * x ^ 4) / x ^ 2 * hpl [zero, negOne] x +
    (-35 / 2 * x ^ 3 - 13 / 2 * x - 5 / 2 * x ^ 4 + 41 / 4 * x ^ 2) / x ^ 2 * hpl [zero, zero] x +
    (-7 / 2 - 12 * x + 12 * x ^ 3 + 7 / 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-7 / 2 - 12 * x + 12 * x ^ 3 + 7 / 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-7 / 2 - 12 * x + 12 * x ^ 3 + 7 / 2 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne] x +
    (-3 * x + 9 * x ^ 3 + 3 / 2 * x ^ 4 + 17 / 2 * x ^ 2) / x ^ 2 * hpl [zero, zero, zero] x +
    (-3 - 18 * x ^ 2 - 12 * x - 12 * x ^ 3 - 3 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero, zero] x +
    (-3 - 12 * x - 12 * x ^ 3 - 8 * x ^ 2 - 3 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero, zero] x +
    (-3 - 12 * x - 12 * x ^ 3 - 8 * x ^ 2 - 3 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne, zero] x +
    (-3 - 12 * x - 12 * x ^ 3 - 8 * x ^ 2 - 3 * x ^ 4) / x ^ 2 * hpl [zero, zero, zero, negOne] x +
    (9) * hpl [zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s122S0 : ContinuousOn i8Psi4s122S0 (Ioc 0 1) := by
  unfold i8Psi4s122S0
  exact (((((((((((((((i13_cont_coef (p := fun x => -311 / 8 * x ^ 3 - 73 / 8 * x -
    3 / 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -7 / 8 - 12 * x + 12 * x ^ 3 +
        7 / 8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -33 / 4 * x + 17 / 8 * x ^ 4 + 89 / 8 * x ^ 2 +
        111 / 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -7 / 4 - 12 * x - 12 * x ^ 3 - 41 / 2 * x ^ 2 -
        7 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -7 / 4 - 12 * x - 12 * x ^ 3 -
        7 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -35 / 2 * x ^ 3 - 13 / 2 * x - 5 / 2 * x ^ 4 +
        41 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -7 / 2 - 12 * x + 12 * x ^ 3 +
        7 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -7 / 2 - 12 * x + 12 * x ^ 3 +
        7 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -7 / 2 - 12 * x + 12 * x ^ 3 +
        7 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -3 * x + 9 * x ^ 3 + 3 / 2 * x ^ 4 +
        17 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -3 - 18 * x ^ 2 - 12 * x - 12 * x ^ 3 -
        3 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -3 - 12 * x - 12 * x ^ 3 - 8 * x ^ 2 -
        3 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -3 - 12 * x - 12 * x ^ 3 - 8 * x ^ 2 -
        3 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -3 - 12 * x - 12 * x ^ 3 - 8 * x ^ 2 -
        3 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero])))

theorem i8Psi4s122_eq_S (x : ℝ) : i8Psi4s122 x = i8Psi4s122S0 x := by
  unfold i8Psi4s122 i8Psi4s122S0 i8Psi4s122N0 i8Psi4s122N1 i8Psi4s122N2 i8Psi4s122N3 i8Psi4s122N4
    i8Psi4s122W
  ring

theorem continuousOn_i8Psi4s122 : ContinuousOn i8Psi4s122 (Ioc 0 1) := by
  rw [show i8Psi4s122 = fun x => i8Psi4s122S0 x from funext i8Psi4s122_eq_S]
  exact continuousOn_i8Psi4s122S0

theorem i8Psi4s122_one : i8Psi4s122 1 = -99 / 2 + 7 / 72 * π ^ 4 + 41 / 24 * π ^ 2 := by
  rw [i8Psi4s122_eq_S]
  unfold i8Psi4s122S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one, hpl_negOne_zero_zero_zero_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_negOne_at_one, hpl_zero_zero_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s123` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s123S0 (x : ℝ) : ℝ :=
    (21 * x ^ 3 + 7 / 2 * x ^ 4) / x ^ 2 +
    (-18 * x ^ 3 - 16 * x ^ 2 - 4 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (-3 * x ^ 2 - 3 * x ^ 3 + 16 * x) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-16 * x ^ 2 + 2 * x ^ 4 + 12 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-6 * x ^ 4 + 16 * x) / x ^ 2 * hpl [zero, one] x +
    (6 * x ^ 2 + 6 * x ^ 3 + 16 * x) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-8) * hpl [zero, zero, zero] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 2 + 8 * x ^ 3) / x ^ 2 * hpl [zero, zero, one] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 2 + 8 * x ^ 3) / x ^ 2 * hpl [zero, one, zero] x +
    (-12 * x ^ 2 - 4 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-8) * hpl [zero, zero, zero, one] x +
    (-8) * hpl [zero, zero, one, zero] x +
    (-8) * hpl [zero, one, zero, zero] x

theorem continuousOn_i8Psi4s123S0 : ContinuousOn i8Psi4s123S0 (Ioc 0 1) := by
  unfold i8Psi4s123S0
  exact (((((((((((((i13_cont_coef (p := fun x => 21 * x ^ 3 + 7 / 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -18 * x ^ 3 - 16 * x ^ 2 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -3 * x ^ 2 - 3 * x ^ 3 + 16 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -16 * x ^ 2 + 2 * x ^ 4 + 12 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -6 * x ^ 4 + 16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => 6 * x ^ 2 + 6 * x ^ 3 + 16 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 2 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 2 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 4 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero])))

theorem i8Psi4s123_eq_S (x : ℝ) : i8Psi4s123 x = i8Psi4s123S0 x := by
  unfold i8Psi4s123 i8Psi4s123S0 i8Psi4s123N0 i8Psi4s123N1 i8Psi4s123N2 i8Psi4s123N3 i8Psi4s123N4
    i8Psi4s123W
  ring

theorem continuousOn_i8Psi4s123 : ContinuousOn i8Psi4s123 (Ioc 0 1) := by
  rw [show i8Psi4s123 = fun x => i8Psi4s123S0 x from funext i8Psi4s123_eq_S]
  exact continuousOn_i8Psi4s123S0

theorem i8Psi4s123_one : i8Psi4s123 1 = 49 / 2 - 28 * zeta3 - 4 / 45 * π ^ 4 + 5 / 3 * π ^ 2 := by
  rw [i8Psi4s123_eq_S]
  unfold i8Psi4s123S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one, hpl_zero_zero_zero_one_at_one,
    hpl_zero_zero_one_zero_at_one, hpl_zero_one_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s124k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s124k0S0 (x : ℝ) : ℝ :=
    (-5 * x ^ 3 + 2 * x ^ 4) / x ^ 2 +
    (-x ^ 4 - 3 * x ^ 2 - 2 * x - 2 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (-x ^ 4 + 2 * x ^ 3 + 8 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (-6 * x - 2 * x ^ 3 + 4 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-2 - 2 * x ^ 4 + 4 * x ^ 2) / x ^ 2 * hpl [negOne, one] x +
    (2) * hpl [zero, negOne] x +
    (4) * hpl [zero, zero] x +
    (-4 * x - 2 * x ^ 2 - 2 * x ^ 4 + 4 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-2 - 2 * x + 2 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (-4 * x - 2 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-4 + 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one] x +
    (-4 + 4 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero] x +
    (-4 + 4 * x ^ 4) / x ^ 2 * hpl [zero, negOne, one] x +
    (-4) * hpl [zero, zero, one] x +
    (-4 + 4 * x ^ 4) / x ^ 2 * hpl [zero, one, negOne] x +
    (-4) * hpl [zero, one, zero] x +
    (-16) * hpl [zero, negOne, zero, one] x +
    (-16) * hpl [zero, negOne, one, zero] x +
    (-16) * hpl [zero, zero, negOne, one] x +
    (-16) * hpl [zero, zero, one, negOne] x

theorem continuousOn_i8Psi4s124k0S0 : ContinuousOn i8Psi4s124k0S0 (Ioc 0 1) := by
  unfold i8Psi4s124k0S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -5 * x ^ 3 + 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 3 * x ^ 2 - 2 * x - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 + 2 * x ^ 3 + 8 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -6 * x - 2 * x ^ 3 + 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -2 - 2 * x ^ 4 + 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x - 2 * x ^ 2 - 2 * x ^ 4 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -2 - 2 * x + 2 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -4 * x - 2 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -4 + 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -4 + 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -4 + 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -4 + 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne])))

theorem i8Psi4s124k0_eq_S (x : ℝ) : i8Psi4s124k0 x = i8Psi4s124k0S0 x := by
  unfold i8Psi4s124k0 i8Psi4s124k0S0 i8Psi4s124k0N0 i8Psi4s124k0N1 i8Psi4s124k0N2 i8Psi4s124k0N3
    i8Psi4s124k0N4 i8Psi4s124k0W
  ring

theorem continuousOn_i8Psi4s124k0 : ContinuousOn i8Psi4s124k0 (Ioc 0 1) := by
  rw [show i8Psi4s124k0 = fun x => i8Psi4s124k0S0 x from funext i8Psi4s124k0_eq_S]
  exact continuousOn_i8Psi4s124k0S0

theorem i8Psi4s124k0_one : i8Psi4s124k0 1 = -3 - 8 * Real.log 2 + 4 * zeta3 + 32 * Li 4 (1 / 2) -
    π ^ 2 / 2 + 4 / 3 * Real.log 2 ^ 4 + 11 / 90 * π ^ 4 - 28 * Real.log 2 * zeta3 -
    4 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s124k0_eq_S]
  unfold i8Psi4s124k0S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_negOne_zero_one_at_one,
    hpl_negOne_one_zero_at_one, hpl_zero_negOne_one_at_one, hpl_zero_zero_one_at_one,
    hpl_zero_one_negOne_at_one, hpl_zero_one_zero_at_one, hpl_zero_negOne_zero_one_at_one,
    hpl_zero_negOne_one_zero_at_one, hpl_zero_zero_negOne_one_at_one,
    hpl_zero_zero_one_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s124k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s124k1S0 (x : ℝ) : ℝ :=
    (x ^ 4 + 5 * x ^ 3) / x ^ 2 +
    (-x ^ 4 - 7 * x ^ 2 - 4 * x - 4 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (-x ^ 4 - 2 * x ^ 3 + 4 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (-4 * x - 2 * x ^ 2 + 2 * x ^ 4 + 4 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (-4 * x + 2 * x ^ 4 + 4 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (4) * hpl [zero, zero] x +
    (4) * hpl [zero, negOne, zero] x +
    (4) * hpl [zero, zero, negOne] x +
    (-4 - 4 * x - 4 * x ^ 2 - 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (-4 - 4 * x - 4 * x ^ 2 - 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (-16) * hpl [zero, one, negOne, zero] x +
    (-16) * hpl [zero, one, zero, negOne] x

theorem continuousOn_i8Psi4s124k1S0 : ContinuousOn i8Psi4s124k1S0 (Ioc 0 1) := by
  unfold i8Psi4s124k1S0
  exact ((((((((((((i13_cont_coef (p := fun x => x ^ 4 + 5 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 7 * x ^ 2 - 4 * x - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 2 * x ^ 3 + 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -4 * x - 2 * x ^ 2 + 2 * x ^ 4 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x + 2 * x ^ 4 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -4 - 4 * x - 4 * x ^ 2 - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 4 * x - 4 * x ^ 2 - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne])))

theorem i8Psi4s124k1_eq_S (x : ℝ) : i8Psi4s124k1 x = i8Psi4s124k1S0 x := by
  unfold i8Psi4s124k1 i8Psi4s124k1S0 i8Psi4s124k1N0 i8Psi4s124k1N1 i8Psi4s124k1N2 i8Psi4s124k1N3
    i8Psi4s124k1N4 i8Psi4s124k1W
  ring

theorem continuousOn_i8Psi4s124k1 : ContinuousOn i8Psi4s124k1 (Ioc 0 1) := by
  rw [show i8Psi4s124k1 = fun x => i8Psi4s124k1S0 x from funext i8Psi4s124k1_eq_S]
  exact continuousOn_i8Psi4s124k1S0

theorem i8Psi4s124k1_one : i8Psi4s124k1 1 = 6 - 16 * Real.log 2 - 3 * zeta3 - 19 / 45 * π ^ 4 +
    π ^ 2 / 6 + 56 * Real.log 2 * zeta3 := by
  rw [i8Psi4s124k1_eq_S]
  unfold i8Psi4s124k1S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_one_negOne_zero_at_one, hpl_zero_one_zero_negOne_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s124 : ContinuousOn i8Psi4s124 (Ioc 0 1) := by
  rw [show i8Psi4s124 = fun x => i8Psi4s124k0 x + i8Psi4s124k1 x from rfl]
  exact (continuousOn_i8Psi4s124k0.add continuousOn_i8Psi4s124k1)

theorem i8Psi4s124_one : i8Psi4s124 1 = 3 + zeta3 - 24 * Real.log 2 + 32 * Li 4 (1 / 2) -
    3 / 10 * π ^ 4 - π ^ 2 / 3 + 4 / 3 * Real.log 2 ^ 4 + 28 * Real.log 2 * zeta3 -
    4 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  unfold i8Psi4s124
  rw [i8Psi4s124k0_one, i8Psi4s124k1_one]
  ring

/-- Chunk 0 of `i8Psi4s125k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s125k0S0 (x : ℝ) : ℝ :=
    (x ^ 4 + 54 * x ^ 3) / x ^ 2 +
    (-x ^ 4 - 27 * x ^ 3 + 6 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (-x ^ 3 - 27 * x ^ 2 - 6 * x) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x ^ 4 + 4 * x ^ 2 + 14 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-26 * x ^ 3 - 6 * x - 2 * x ^ 4) / x ^ 2 * hpl [zero, one] x +
    (x ^ 3 - 4 * x + 13 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [negOne, zero, one] x +
    (4) * hpl [zero, zero, zero] x +
    (-4 * x + 2 * x ^ 4 + 12 * x ^ 3 + 14 * x ^ 2) / x ^ 2 * hpl [zero, zero, one] x +
    (-4 * x + 2 * x ^ 4 + 12 * x ^ 3) / x ^ 2 * hpl [zero, one, zero] x +
    (-14 * x ^ 2 - 4 * x - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero, one] x +
    (-4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one, zero] x +
    (-4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero, zero] x +
    (-4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero, one] x +
    (12) * hpl [zero, zero, zero, one] x +
    (12) * hpl [zero, zero, one, zero] x +
    (12) * hpl [zero, one, zero, zero] x

theorem continuousOn_i8Psi4s125k0S0 : ContinuousOn i8Psi4s125k0S0 (Ioc 0 1) := by
  unfold i8Psi4s125k0S0
  exact ((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 + 54 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 27 * x ^ 3 + 6 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 27 * x ^ 2 - 6 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 4 * x ^ 2 + 14 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -26 * x ^ 3 - 6 * x - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - 4 * x + 13 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x + 2 * x ^ 4 + 12 * x ^ 3 +
        14 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -4 * x + 2 * x ^ 4 + 12 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -14 * x ^ 2 - 4 * x - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, one]))).add
      ((i13_cont_coef (p := fun x => -4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero])))

theorem i8Psi4s125k0_eq_S (x : ℝ) : i8Psi4s125k0 x = i8Psi4s125k0S0 x := by
  unfold i8Psi4s125k0 i8Psi4s125k0S0 i8Psi4s125k0N0 i8Psi4s125k0N1 i8Psi4s125k0N2 i8Psi4s125k0N3
    i8Psi4s125k0N4 i8Psi4s125k0W
  ring

theorem continuousOn_i8Psi4s125k0 : ContinuousOn i8Psi4s125k0 (Ioc 0 1) := by
  rw [show i8Psi4s125k0 = fun x => i8Psi4s125k0S0 x from funext i8Psi4s125k0_eq_S]
  exact continuousOn_i8Psi4s125k0S0

theorem i8Psi4s125k0_one : i8Psi4s125k0 1 = 55 - 128 * Li 4 (1 / 2) + 4 * zeta3 -
    17 / 3 * π ^ 2 - 16 / 3 * Real.log 2 ^ 4 + 73 / 180 * π ^ 4 +
    16 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s125k0_eq_S]
  unfold i8Psi4s125k0S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_negOne_zero_one_at_one,
    hpl_zero_zero_zero_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one,
    hpl_negOne_zero_zero_one_at_one, hpl_negOne_zero_one_zero_at_one,
    hpl_negOne_one_zero_zero_at_one, hpl_zero_negOne_zero_one_at_one, hpl_zero_zero_zero_one_at_one,
    hpl_zero_zero_one_zero_at_one, hpl_zero_one_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s125k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s125k1S0 (x : ℝ) : ℝ :=
    (x ^ 4 + 64 * x ^ 3) / x ^ 2 +
    (-x - 17 * x ^ 3 - 35 / 2 * x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [negOne] x +
    (-x ^ 4 - 32 * x ^ 3 + 2 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (-x - 31 / 2 * x ^ 2 - x ^ 3 / 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x ^ 4 - 2 * x + 15 * x ^ 2 + 18 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (-1 - x ^ 4 - 30 * x ^ 2 - 16 * x - 16 * x ^ 3) / x ^ 2 * hpl [negOne, one] x +
    (17) * hpl [zero, negOne] x +
    (4) * hpl [zero, zero] x +
    (15) * hpl [zero, one] x +
    (-1 + x ^ 3 - 17 * x + 17 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (x ^ 3 - 2 * x + 15 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [negOne, one, zero] x +
    (18) * hpl [zero, negOne, zero] x +
    (-2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [zero, negOne, one] x +
    (-2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [zero, one, negOne] x +
    (14) * hpl [zero, one, zero] x +
    (-2 - 18 * x - 18 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (-4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, negOne, one, zero] x +
    (-4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne, one] x +
    (-4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, zero, one, negOne] x

theorem continuousOn_i8Psi4s125k1S0 : ContinuousOn i8Psi4s125k1S0 (Ioc 0 1) := by
  unfold i8Psi4s125k1S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 + 64 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -x - 17 * x ^ 3 - 35 / 2 * x ^ 2 -
        x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 32 * x ^ 3 + 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x - 31 / 2 * x ^ 2 - x ^ 3 / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 2 * x + 15 * x ^ 2 + 18 * x ^ 3) (by fun_prop)).mul
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
      ((i13_cont_coef (p := fun x => x ^ 3 - 2 * x + 15 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 18 * x - 18 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one]))).add
      ((i13_cont_coef (p := fun x => -4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne])))

/-- Chunk 1 of `i8Psi4s125k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s125k1S1 (x : ℝ) : ℝ :=
    (-4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, one, negOne, zero] x

theorem continuousOn_i8Psi4s125k1S1 : ContinuousOn i8Psi4s125k1S1 (Ioc 0 1) := by
  unfold i8Psi4s125k1S1
  exact ((i13_cont_coef (p := fun x => -4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))

theorem i8Psi4s125k1_eq_S (x : ℝ) : i8Psi4s125k1 x = i8Psi4s125k1S0 x + i8Psi4s125k1S1 x := by
  unfold i8Psi4s125k1 i8Psi4s125k1S0 i8Psi4s125k1S1 i8Psi4s125k1N0 i8Psi4s125k1N1 i8Psi4s125k1N2
    i8Psi4s125k1N3 i8Psi4s125k1N4 i8Psi4s125k1W
  ring

theorem continuousOn_i8Psi4s125k1 : ContinuousOn i8Psi4s125k1 (Ioc 0 1) := by
  rw [show i8Psi4s125k1 = fun x => i8Psi4s125k1S0 x +
    i8Psi4s125k1S1 x from funext i8Psi4s125k1_eq_S]
  exact (continuousOn_i8Psi4s125k1S0.add continuousOn_i8Psi4s125k1S1)

theorem i8Psi4s125k1_one : i8Psi4s125k1 1 = 65 - 80 * Li 4 (1 / 2) - 55 * zeta3 -
    36 * Real.log 2 + 32 * Real.log 2 ^ 2 - 49 / 12 * π ^ 2 - 10 / 3 * Real.log 2 ^ 4 +
    47 / 36 * π ^ 4 - 70 * Real.log 2 * zeta3 + 10 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s125k1_eq_S]
  unfold i8Psi4s125k1S0 i8Psi4s125k1S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_negOne_one_at_one,
    hpl_zero_negOne_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_negOne_one_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_negOne_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_zero_at_one, hpl_zero_negOne_one_zero_at_one, hpl_zero_zero_negOne_one_at_one,
    hpl_zero_zero_one_negOne_at_one, hpl_zero_one_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s125k2` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s125k2S0 (x : ℝ) : ℝ :=
    (x ^ 4 + 74 * x ^ 3) / x ^ 2 +
    (-x ^ 4 - 43 * x ^ 2 - 38 * x ^ 3 - 6 * x) / x ^ 2 * hpl [negOne] x +
    (-x ^ 4 - 37 * x ^ 3 + 6 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (x ^ 4 - 4 * x + 15 * x ^ 2 + 20 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (-6 * x + 2 * x ^ 4 + 38 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (x ^ 4 + 4 * x ^ 2 + 18 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-22 * x ^ 2 - 20 * x ^ 3 - 4 * x - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-20 * x ^ 3 - 4 * x - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-20 * x ^ 3 - 4 * x - 2 * x ^ 4 + 18 * x ^ 2) / x ^ 2 * hpl [zero, zero, negOne] x +
    (4) * hpl [zero, zero, zero] x +
    (-2 - 18 * x - 18 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (20) * hpl [zero, negOne, zero, zero] x +
    (20) * hpl [zero, zero, negOne, zero] x +
    (20) * hpl [zero, zero, zero, negOne] x +
    (-4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, one, zero, negOne] x +
    (-4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero, zero] x) +
    (-4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne, zero] x) +
    (-4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, zero, negOne] x)

theorem continuousOn_i8Psi4s125k2S0 : ContinuousOn i8Psi4s125k2S0 (Ioc 0 1) := by
  unfold i8Psi4s125k2S0
  exact ((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 + 74 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 43 * x ^ 2 - 38 * x ^ 3 - 6 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 37 * x ^ 3 + 6 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 4 * x + 15 * x ^ 2 + 20 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -6 * x + 2 * x ^ 4 + 38 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 4 * x ^ 2 + 18 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -22 * x ^ 2 - 20 * x ^ 3 - 4 * x -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -20 * x ^ 3 - 4 * x - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -20 * x ^ 3 - 4 * x - 2 * x ^ 4 +
        18 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 18 * x - 18 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 20 * x + 4 * x ^ 3 + 20 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero, negOne])))

theorem i8Psi4s125k2_eq_S (x : ℝ) : i8Psi4s125k2 x = i8Psi4s125k2S0 x := by
  unfold i8Psi4s125k2 i8Psi4s125k2S0 i8Psi4s125k2N0 i8Psi4s125k2N1 i8Psi4s125k2N2 i8Psi4s125k2N3
    i8Psi4s125k2N4 i8Psi4s125k2W
  ring

theorem continuousOn_i8Psi4s125k2 : ContinuousOn i8Psi4s125k2 (Ioc 0 1) := by
  rw [show i8Psi4s125k2 = fun x => i8Psi4s125k2S0 x from funext i8Psi4s125k2_eq_S]
  exact continuousOn_i8Psi4s125k2S0

theorem i8Psi4s125k2_one : i8Psi4s125k2 1 = 75 - 88 * Real.log 2 - 3 * zeta3 +
    160 * Li 4 (1 / 2) - 16 / 9 * π ^ 4 + π ^ 2 / 6 + 20 / 3 * Real.log 2 ^ 4 +
    140 * Real.log 2 * zeta3 - 20 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s125k2_eq_S]
  unfold i8Psi4s125k2S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_at_one,
    hpl_zero_one_zero_negOne_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s125 : ContinuousOn i8Psi4s125 (Ioc 0 1) := by
  rw [show i8Psi4s125 = fun x => i8Psi4s125k0 x + i8Psi4s125k1 x + i8Psi4s125k2 x from rfl]
  exact ((continuousOn_i8Psi4s125k0.add continuousOn_i8Psi4s125k1).add continuousOn_i8Psi4s125k2)

theorem i8Psi4s125_one : i8Psi4s125 1 = 195 - 124 * Real.log 2 - 54 * zeta3 - 48 * Li 4 (1 / 2) -
    2 * Real.log 2 ^ 4 + 32 * Real.log 2 ^ 2 - 115 / 12 * π ^ 2 - π ^ 4 / 15 +
    2 * π ^ 2 * Real.log 2 ^ 2 + 70 * Real.log 2 * zeta3 := by
  unfold i8Psi4s125
  rw [i8Psi4s125k0_one, i8Psi4s125k1_one, i8Psi4s125k2_one]
  ring

/-- Chunk 0 of `i8Psi4s126` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s126S0 (x : ℝ) : ℝ :=
    (-34 * x ^ 3 - 7 / 2 * x ^ 4) / x ^ 2 +
    (x ^ 4 + 14 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (6 * x ^ 3 + 20 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-24 * x ^ 2 + 2 * x ^ 4 + 12 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-14 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (2 * x ^ 2 + 10 * x ^ 3 + 24 * x) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-8) * hpl [zero, zero, one] x +
    (-8) * hpl [zero, one, zero] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 3 + 16 * x ^ 2) / x ^ 2 * hpl [zero, one, one] x +
    (-12 * x ^ 2 - 4 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, one] x) +
    (-12 * x ^ 2 - 4 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, one, zero] x) +
    (-8) * hpl [zero, zero, one, one] x +
    (-8) * hpl [zero, one, zero, one] x +
    (-8) * hpl [zero, one, one, zero] x

theorem continuousOn_i8Psi4s126S0 : ContinuousOn i8Psi4s126S0 (Ioc 0 1) := by
  unfold i8Psi4s126S0
  exact ((((((((((((((i13_cont_coef (p := fun x => -34 * x ^ 3 - 7 / 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 14 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 6 * x ^ 3 + 20 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 + 2 * x ^ 4 + 12 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -14 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 2 + 10 * x ^ 3 + 24 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 3 + 16 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 4 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 4 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero])))

theorem i8Psi4s126_eq_S (x : ℝ) : i8Psi4s126 x = i8Psi4s126S0 x := by
  unfold i8Psi4s126 i8Psi4s126S0 i8Psi4s126N0 i8Psi4s126N1 i8Psi4s126N2 i8Psi4s126N3 i8Psi4s126N4
    i8Psi4s126W
  ring

theorem continuousOn_i8Psi4s126 : ContinuousOn i8Psi4s126 (Ioc 0 1) := by
  rw [show i8Psi4s126 = fun x => i8Psi4s126S0 x from funext i8Psi4s126_eq_S]
  exact continuousOn_i8Psi4s126S0

theorem i8Psi4s126_one : i8Psi4s126 1 = -75 / 2 + 44 * zeta3 - 5 / 3 * π ^ 2 + π ^ 4 / 45 := by
  rw [i8Psi4s126_eq_S]
  unfold i8Psi4s126S0
  rw [hpl_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one,
    hpl_zero_one_one_at_one, hpl_zero_zero_one_one_at_one, hpl_zero_one_zero_one_at_one,
    hpl_zero_one_one_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s127` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s127S0 (x : ℝ) : ℝ :=
    (-14 * x ^ 3 - 3 * x ^ 4) / x ^ 2 +
    (2 * x ^ 4 + 10 * x ^ 2 + 12 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (4 * x ^ 2 + 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-8 * x - 4 * x ^ 2 + 4 * x ^ 4 + 8 * x ^ 3) / x ^ 2 * hpl [negOne, one] x +
    (8) * hpl [zero, negOne] x +
    (16) * hpl [zero, one] x +
    (-12 * x ^ 2 - 8 * x - 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (-8 * x - 4 * x ^ 2 + 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-8 + 8 * x ^ 4) / x ^ 2 * hpl [negOne, one, one] x +
    (8) * hpl [zero, negOne, one] x +
    (8) * hpl [zero, one, negOne] x +
    (-8) * hpl [zero, one, one] x +
    (-8 - 8 * x - 8 * x ^ 2 - 8 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, one] x) +
    (-8 - 8 * x - 8 * x ^ 2 - 8 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one, negOne] x) +
    (-32) * hpl [zero, negOne, one, one] x +
    (-32) * hpl [zero, one, negOne, one] x +
    (-32) * hpl [zero, one, one, negOne] x

theorem continuousOn_i8Psi4s127S0 : ContinuousOn i8Psi4s127S0 (Ioc 0 1) := by
  unfold i8Psi4s127S0
  exact (((((((((((((((((i13_cont_coef (p := fun x => -14 * x ^ 3 - 3 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 10 * x ^ 2 + 12 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 2 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -8 * x - 4 * x ^ 2 + 4 * x ^ 4 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 8 * x - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -8 * x - 4 * x ^ 2 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      ((i13_cont_coef (p := fun x => -8 + 8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -8 - 8 * x - 8 * x ^ 2 - 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, one]))).add
      ((i13_cont_coef (p := fun x => -8 - 8 * x - 8 * x ^ 2 - 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, negOne])))

theorem i8Psi4s127_eq_S (x : ℝ) : i8Psi4s127 x = i8Psi4s127S0 x := by
  unfold i8Psi4s127 i8Psi4s127S0 i8Psi4s127N0 i8Psi4s127N1 i8Psi4s127N2 i8Psi4s127N3 i8Psi4s127N4
    i8Psi4s127W
  ring

theorem continuousOn_i8Psi4s127 : ContinuousOn i8Psi4s127 (Ioc 0 1) := by
  rw [show i8Psi4s127 = fun x => i8Psi4s127S0 x from funext i8Psi4s127_eq_S]
  exact continuousOn_i8Psi4s127S0

theorem i8Psi4s127_one : i8Psi4s127 1 = -17 - 32 * Li 4 (1 / 2) - 3 * zeta3 + 24 * Real.log 2 -
    4 / 3 * Real.log 2 ^ 4 + π ^ 4 / 9 + 10 / 3 * π ^ 2 - 28 * Real.log 2 * zeta3 +
    4 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s127_eq_S]
  unfold i8Psi4s127S0
  rw [hpl_negOne_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one, hpl_zero_one_at_one,
    hpl_negOne_one_one_at_one, hpl_zero_negOne_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_one_at_one, hpl_zero_negOne_one_one_at_one, hpl_zero_one_negOne_one_at_one,
    hpl_zero_one_one_negOne_at_one]
  norm_num
  ring

end QED.ThreeLoopD
