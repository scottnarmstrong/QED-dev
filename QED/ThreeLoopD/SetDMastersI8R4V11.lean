/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4V10

/-!
# Set (d), master `I₈`: continuity and values at `1` of the sub-pieces 146 to 155 of `Ψ₄`

Each sub-piece `Ψ₄⁽ⁿ⁾` is continuous on `(0, 1]` (the words beginning with `1` carry a factor
`1 - ξ`), and its value at `ξ = 1` follows from the values of the harmonic polylogarithms at `1`.

## Main results

* `QED.ThreeLoopD.continuousOn_i8Psi4s146`, `QED.ThreeLoopD.i8Psi4s146_one` and their
  companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- Chunk 0 of `i8Psi4s146k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s146k0S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 - 11 / 4 * x ^ 3) / x ^ 2 +
    (x ^ 3 / 2 - x ^ 4 / 4) / x ^ 2 * hpl [zero] x +
    (-3 / 4 * x ^ 3 + 9 / 4 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x ^ 3 + 3 * x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [zero, one] x +
    (x ^ 3 / 2 - x ^ 2 / 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-x ^ 3 - 3 * x + 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-1 - x ^ 4 + 2 * x ^ 2) / x ^ 2 * hpl [negOne, one, one] x +
    (2) * hpl [zero, zero, one] x +
    (2) * hpl [zero, one, zero] x +
    (-x ^ 2 - x ^ 4 - 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [zero, one, one] x +
    (x ^ 3 - x ^ 2 - 2 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, one] x) +
    (x ^ 3 - x ^ 2 - 2 * x) / x ^ 2 * ((1 - x) * hpl [one, one, zero] x) +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one, one] x +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero, one] x +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [negOne, one, one, zero] x +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, one, one] x +
    (-2) * hpl [zero, zero, one, one] x +
    (-2) * hpl [zero, one, zero, one] x +
    (-2) * hpl [zero, one, one, zero] x +
    (-8) * hpl [zero, negOne, zero, one, one] x

theorem continuousOn_i8Psi4s146k0S0 : ContinuousOn i8Psi4s146k0S0 (Ioc 0 1) := by
  unfold i8Psi4s146k0S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 / 2 -
    11 / 4 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -3 / 4 * x ^ 3 + 9 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + 3 * x ^ 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 - x ^ 2 / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 3 * x + 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 4 + 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 2 - x ^ 4 - 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - x ^ 2 - 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - x ^ 2 - 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one, one]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one, one])))

/-- Chunk 1 of `i8Psi4s146k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s146k0S1 (x : ℝ) : ℝ :=
    (-8) * hpl [zero, negOne, one, zero, one] x +
    (-8) * hpl [zero, negOne, one, one, zero] x +
    (-8) * hpl [zero, zero, negOne, one, one] x

theorem continuousOn_i8Psi4s146k0S1 : ContinuousOn i8Psi4s146k0S1 (Ioc 0 1) := by
  unfold i8Psi4s146k0S1
  exact (((continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero, one])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one, one])))

theorem i8Psi4s146k0_eq_S (x : ℝ) : i8Psi4s146k0 x = i8Psi4s146k0S0 x + i8Psi4s146k0S1 x := by
  unfold i8Psi4s146k0 i8Psi4s146k0S0 i8Psi4s146k0S1 i8Psi4s146k0N0 i8Psi4s146k0N1 i8Psi4s146k0N2
    i8Psi4s146k0N3 i8Psi4s146k0N4 i8Psi4s146k0W
  ring

theorem continuousOn_i8Psi4s146k0 : ContinuousOn i8Psi4s146k0 (Ioc 0 1) := by
  rw [show i8Psi4s146k0 = fun x => i8Psi4s146k0S0 x +
    i8Psi4s146k0S1 x from funext i8Psi4s146k0_eq_S]
  exact (continuousOn_i8Psi4s146k0S0.add continuousOn_i8Psi4s146k0S1)

theorem i8Psi4s146k0_one : i8Psi4s146k0 1 = -9 / 4 - 4 * zeta3 + 15 * zeta5 + 16 * Li 5 (1 / 2) -
    2 / 15 * Real.log 2 ^ 5 + π ^ 4 / 180 + 7 / 12 * π ^ 2 - 13 / 6 * π ^ 2 * zeta3 +
    Real.log 2 * π ^ 4 / 45 + 2 / 9 * π ^ 2 * Real.log 2 ^ 3 := by
  rw [i8Psi4s146k0_eq_S]
  unfold i8Psi4s146k0S0 i8Psi4s146k0S1
  rw [hpl_zero_at_one, hpl_zero_one_at_one, hpl_negOne_one_one_at_one, hpl_zero_zero_one_at_one,
    hpl_zero_one_zero_at_one, hpl_zero_one_one_at_one, hpl_negOne_zero_one_one_at_one,
    hpl_negOne_one_zero_one_at_one, hpl_negOne_one_one_zero_at_one, hpl_zero_negOne_one_one_at_one,
    hpl_zero_zero_one_one_at_one, hpl_zero_one_zero_one_at_one, hpl_zero_one_one_zero_at_one,
    hpl_zero_negOne_zero_one_one_at_one, hpl_zero_negOne_one_zero_one_at_one,
    hpl_zero_negOne_one_one_zero_at_one, hpl_zero_zero_negOne_one_one_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s146k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s146k1S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 + 19 / 4 * x ^ 3) / x ^ 2 +
    (-5 / 4 * x ^ 2 - 3 / 2 * x ^ 3 - x ^ 4 / 4) / x ^ 2 * hpl [negOne] x +
    (-3 / 2 * x ^ 3 - x ^ 4 / 4) / x ^ 2 * hpl [zero] x +
    (-2 * x ^ 2 - x ^ 3 / 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-x - x ^ 3 - 3 / 2 * x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [negOne, one] x +
    (1) * hpl [zero, negOne] x +
    (x ^ 2 - x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero, one] x +
    (x ^ 3 / 2 - x + 3 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (x ^ 3 / 2 + 3 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (x ^ 4 - x ^ 2 - 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [negOne, zero, one] x +
    (x ^ 4 - x ^ 2 - 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [negOne, one, zero] x +
    (1) * hpl [zero, negOne, one] x +
    (2) * hpl [zero, zero, one] x +
    (1) * hpl [zero, one, negOne] x +
    (2) * hpl [zero, one, zero] x +
    (-1 + x ^ 2 + x ^ 3 - x) / x ^ 2 * ((1 - x) * hpl [one, negOne, one] x) +
    (-1 + x ^ 2 + x ^ 3 - x) / x ^ 2 * ((1 - x) * hpl [one, one, negOne] x) +
    (2) * hpl [zero, negOne, zero, one] x +
    (2) * hpl [zero, negOne, one, zero] x +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [zero, one, negOne, one] x

theorem continuousOn_i8Psi4s146k1S0 : ContinuousOn i8Psi4s146k1S0 (Ioc 0 1) := by
  unfold i8Psi4s146k1S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 / 2 +
    19 / 4 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -5 / 4 * x ^ 2 - 3 / 2 * x ^ 3 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -3 / 2 * x ^ 3 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 2 - x ^ 3 / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -x - x ^ 3 - 3 / 2 * x ^ 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 - x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 - x + 3 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 + 3 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - x ^ 2 - 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - x ^ 2 - 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 2 + x ^ 3 - x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, one]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 2 + x ^ 3 - x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, one])))

/-- Chunk 1 of `i8Psi4s146k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s146k1S1 (x : ℝ) : ℝ :=
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [zero, one, one, negOne] x +
    (-2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero, one] x) +
    (-2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, one, zero] x) +
    (-8) * hpl [zero, zero, one, negOne, one] x +
    (-8) * hpl [zero, zero, one, one, negOne] x +
    (-8) * hpl [zero, one, negOne, zero, one] x +
    (-8) * hpl [zero, one, negOne, one, zero] x

theorem continuousOn_i8Psi4s146k1S1 : ContinuousOn i8Psi4s146k1S1 (Ioc 0 1) := by
  unfold i8Psi4s146k1S1
  exact ((((((((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, negOne])).add
      ((i13_cont_coef (p := fun x => -2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero, one]))).add
      ((i13_cont_coef (p := fun x => -2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, one, zero])))

theorem i8Psi4s146k1_eq_S (x : ℝ) : i8Psi4s146k1 x = i8Psi4s146k1S0 x + i8Psi4s146k1S1 x := by
  unfold i8Psi4s146k1 i8Psi4s146k1S0 i8Psi4s146k1S1 i8Psi4s146k1N0 i8Psi4s146k1N1 i8Psi4s146k1N2
    i8Psi4s146k1N3 i8Psi4s146k1N4 i8Psi4s146k1W
  ring

theorem continuousOn_i8Psi4s146k1 : ContinuousOn i8Psi4s146k1 (Ioc 0 1) := by
  rw [show i8Psi4s146k1 = fun x => i8Psi4s146k1S0 x +
    i8Psi4s146k1S1 x from funext i8Psi4s146k1_eq_S]
  exact (continuousOn_i8Psi4s146k1S0.add continuousOn_i8Psi4s146k1S1)

theorem i8Psi4s146k1_one : i8Psi4s146k1 1 = 21 / 4 - 32 * Li 5 (1 / 2) - 8 * Li 4 (1 / 2) -
    3 * Real.log 2 + 2 * Real.log 2 ^ 2 - 51 / 8 * zeta5 - 11 / 8 * zeta3 - π ^ 2 / 3 -
    Real.log 2 ^ 4 / 3 + π ^ 4 / 45 + 14 / 15 * Real.log 2 ^ 5 + 7 * zeta3 * Real.log 2 ^ 2 +
    16 * Real.log 2 * Li 4 (1 / 2) - 19 / 60 * Real.log 2 * π ^ 4 -
    10 / 9 * π ^ 2 * Real.log 2 ^ 3 + π ^ 2 * Real.log 2 ^ 2 / 3 + 13 / 4 * π ^ 2 * zeta3 := by
  rw [i8Psi4s146k1_eq_S]
  unfold i8Psi4s146k1S0 i8Psi4s146k1S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one,
    hpl_zero_one_at_one, hpl_negOne_zero_one_at_one, hpl_negOne_one_zero_at_one,
    hpl_zero_negOne_one_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_zero_at_one, hpl_zero_negOne_zero_one_at_one, hpl_zero_negOne_one_zero_at_one,
    hpl_zero_one_negOne_one_at_one, hpl_zero_one_one_negOne_at_one,
    hpl_zero_zero_one_negOne_one_at_one, hpl_zero_zero_one_one_negOne_at_one,
    hpl_zero_one_negOne_zero_one_at_one, hpl_zero_one_negOne_one_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s146k2` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s146k2S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 + 37 / 4 * x ^ 3) / x ^ 2 +
    (-5 * x ^ 2 - 11 / 2 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [negOne] x +
    (-5 / 2 * x ^ 3 - x ^ 4 / 4) / x ^ 2 * hpl [zero] x +
    (-7 / 4 * x ^ 2 - x ^ 3 / 4) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x ^ 4 / 2 + 3 * x ^ 3 + 5 / 2 * x ^ 2) / x ^ 2 * hpl [negOne, zero] x +
    (-2 * x - 2 * x ^ 3 - 7 / 2 * x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [negOne, one] x +
    (x ^ 4 / 2 + 2 * x ^ 2 + 3 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (2) * hpl [zero, one] x +
    (x ^ 3 / 2 - 2 * x + 5 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (2) * hpl [zero, negOne, zero] x +
    (x ^ 4 - 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [zero, negOne, one] x +
    (2) * hpl [zero, zero, negOne] x +
    (x ^ 4 - 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [zero, one, negOne] x +
    (-x ^ 3 - 3 * x ^ 2 - 2 * x) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (-x ^ 3 - 3 * x ^ 2 - 2 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (2) * hpl [zero, zero, negOne, one] x +
    (2) * hpl [zero, zero, one, negOne] x +
    (2) * hpl [zero, one, negOne, zero] x +
    (2) * hpl [zero, one, zero, negOne] x +
    (-2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne, one] x)

theorem continuousOn_i8Psi4s146k2S0 : ContinuousOn i8Psi4s146k2S0 (Ioc 0 1) := by
  unfold i8Psi4s146k2S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 / 2 +
    37 / 4 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -5 * x ^ 2 - 11 / 2 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -5 / 2 * x ^ 3 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -7 / 4 * x ^ 2 - x ^ 3 / 4) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 3 * x ^ 3 + 5 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -2 * x - 2 * x ^ 3 - 7 / 2 * x ^ 2 -
        x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 2 * x ^ 2 + 3 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 - 2 * x + 5 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 3 * x ^ 2 - 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 3 * x ^ 2 - 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne, one])))

/-- Chunk 1 of `i8Psi4s146k2` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s146k2S1 (x : ℝ) : ℝ :=
    (-2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, one, negOne] x) +
    (-2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one, negOne, zero] x) +
    (-2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one, zero, negOne] x) +
    (-8) * hpl [zero, one, zero, negOne, one] x +
    (-8) * hpl [zero, one, zero, one, negOne] x +
    (-8) * hpl [zero, one, one, negOne, zero] x +
    (-8) * hpl [zero, one, one, zero, negOne] x

theorem continuousOn_i8Psi4s146k2S1 : ContinuousOn i8Psi4s146k2S1 (Ioc 0 1) := by
  unfold i8Psi4s146k2S1
  exact ((((((((i13_cont_coef (p := fun x => -2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one, negOne])).add
      ((i13_cont_coef (p := fun x => -2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero, negOne])))

theorem i8Psi4s146k2_eq_S (x : ℝ) : i8Psi4s146k2 x = i8Psi4s146k2S0 x + i8Psi4s146k2S1 x := by
  unfold i8Psi4s146k2 i8Psi4s146k2S0 i8Psi4s146k2S1 i8Psi4s146k2N0 i8Psi4s146k2N1 i8Psi4s146k2N2
    i8Psi4s146k2N3 i8Psi4s146k2N4 i8Psi4s146k2W
  ring

theorem continuousOn_i8Psi4s146k2 : ContinuousOn i8Psi4s146k2 (Ioc 0 1) := by
  rw [show i8Psi4s146k2 = fun x => i8Psi4s146k2S0 x +
    i8Psi4s146k2S1 x from funext i8Psi4s146k2_eq_S]
  exact (continuousOn_i8Psi4s146k2S0.add continuousOn_i8Psi4s146k2S1)

theorem i8Psi4s146k2_one : i8Psi4s146k2 1 = 39 / 4 - 11 * Real.log 2 + 4 * Li 4 (1 / 2) +
    4 * Real.log 2 ^ 2 - 7 / 8 * zeta3 - 4 / 3 * Real.log 2 ^ 5 - 3 / 8 * π ^ 2 +
    Real.log 2 ^ 4 / 6 + 11 / 720 * π ^ 4 + 43 / 8 * zeta5 - 32 * Real.log 2 * Li 4 (1 / 2) -
    14 * zeta3 * Real.log 2 ^ 2 - 7 / 2 * Real.log 2 * zeta3 - 5 / 6 * π ^ 2 * zeta3 -
    π ^ 2 * Real.log 2 ^ 2 / 6 + 4 / 3 * π ^ 2 * Real.log 2 ^ 3 +
    53 / 180 * Real.log 2 * π ^ 4 := by
  rw [i8Psi4s146k2_eq_S]
  unfold i8Psi4s146k2S0 i8Psi4s146k2S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_negOne_one_at_one,
    hpl_zero_negOne_at_one, hpl_zero_one_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_negOne_one_at_one, hpl_zero_zero_negOne_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_zero_negOne_one_at_one, hpl_zero_zero_one_negOne_at_one,
    hpl_zero_one_negOne_zero_at_one, hpl_zero_one_zero_negOne_at_one,
    hpl_zero_one_zero_negOne_one_at_one, hpl_zero_one_zero_one_negOne_at_one,
    hpl_zero_one_one_negOne_zero_at_one, hpl_zero_one_one_zero_negOne_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s146 : ContinuousOn i8Psi4s146 (Ioc 0 1) := by
  rw [show i8Psi4s146 = fun x => i8Psi4s146k0 x + i8Psi4s146k1 x + i8Psi4s146k2 x from rfl]
  exact ((continuousOn_i8Psi4s146k0.add continuousOn_i8Psi4s146k1).add continuousOn_i8Psi4s146k2)

theorem i8Psi4s146_one : i8Psi4s146 1 = 51 / 4 - 16 * Li 5 (1 / 2) - 14 * Real.log 2 -
    4 * Li 4 (1 / 2) + 6 * Real.log 2 ^ 2 + 14 * zeta5 - 25 / 4 * zeta3 -
    8 / 15 * Real.log 2 ^ 5 - Real.log 2 ^ 4 / 6 - π ^ 2 / 8 + 31 / 720 * π ^ 4 -
    16 * Real.log 2 * Li 4 (1 / 2) - 7 * zeta3 * Real.log 2 ^ 2 - 7 / 2 * Real.log 2 * zeta3 +
    π ^ 2 * zeta3 / 4 + π ^ 2 * Real.log 2 ^ 2 / 6 + 4 / 9 * π ^ 2 * Real.log 2 ^ 3 := by
  unfold i8Psi4s146
  rw [i8Psi4s146k0_one, i8Psi4s146k1_one, i8Psi4s146k2_one]
  ring

/-- Chunk 0 of `i8Psi4s147` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s147S0 (x : ℝ) : ℝ :=
    (x ^ 3 - x ^ 4 / 2) / x ^ 2 +
    (x ^ 3 - x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-2 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-8) * hpl [zero, one, one] x +
    (-4 * x ^ 2 + 4 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, one, one] x) +
    (8) * hpl [zero, one, one, one] x

theorem continuousOn_i8Psi4s147S0 : ContinuousOn i8Psi4s147S0 (Ioc 0 1) := by
  unfold i8Psi4s147S0
  exact ((((((i13_cont_coef (p := fun x => x ^ 3 - x ^ 4 / 2) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 3 - x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 2 + 4 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, one])))

theorem i8Psi4s147_eq_S (x : ℝ) : i8Psi4s147 x = i8Psi4s147S0 x := by
  unfold i8Psi4s147 i8Psi4s147S0 i8Psi4s147N0 i8Psi4s147N1 i8Psi4s147N2 i8Psi4s147N3 i8Psi4s147N4
    i8Psi4s147W
  ring

theorem continuousOn_i8Psi4s147 : ContinuousOn i8Psi4s147 (Ioc 0 1) := by
  rw [show i8Psi4s147 = fun x => i8Psi4s147S0 x from funext i8Psi4s147_eq_S]
  exact continuousOn_i8Psi4s147S0

theorem i8Psi4s147_one : i8Psi4s147 1 = 1 / 2 - 8 * zeta3 + 4 / 45 * π ^ 4 := by
  rw [i8Psi4s147_eq_S]
  unfold i8Psi4s147S0
  rw [hpl_zero_one_one_at_one, hpl_zero_one_one_one_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s148k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s148k0S0 (x : ℝ) : ℝ :=
    (-x ^ 4 - 15 * x ^ 3) / x ^ 2 +
    (x ^ 4 / 2 + 7 * x ^ 3 + 13 / 2 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (3 / 2 * x ^ 3 + 17 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x ^ 4 + 5 * x ^ 2 + 6 * x ^ 3) / x ^ 2 * hpl [negOne, one] x +
    (-x ^ 3 - 7 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (2 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-4 * x - 2 * x ^ 2 + 2 * x ^ 4 + 4 * x ^ 3) / x ^ 2 * hpl [negOne, one, one] x +
    (4) * hpl [zero, negOne, one] x +
    (4) * hpl [zero, one, negOne] x +
    (8) * hpl [zero, one, one] x +
    (-6 * x ^ 2 - 4 * x - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, one] x) +
    (-6 * x ^ 2 - 4 * x - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one, negOne] x) +
    (-4 * x - 2 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one, one] x) +
    (-4 + 4 * x ^ 4) / x ^ 2 * hpl [negOne, one, one, one] x +
    (4) * hpl [zero, negOne, one, one] x +
    (4) * hpl [zero, one, negOne, one] x +
    (4) * hpl [zero, one, one, negOne] x +
    (-4) * hpl [zero, one, one, one] x +
    (-4 - 4 * x - 4 * x ^ 2 - 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, one, one] x) +
    (-4 - 4 * x - 4 * x ^ 2 - 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one, negOne, one] x)

theorem continuousOn_i8Psi4s148k0S0 : ContinuousOn i8Psi4s148k0S0 (Ioc 0 1) := by
  unfold i8Psi4s148k0S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -x ^ 4 - 15 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 7 * x ^ 3 + 13 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 3 / 2 * x ^ 3 + 17 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 5 * x ^ 2 + 6 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 7 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      ((i13_cont_coef (p := fun x => -4 * x - 2 * x ^ 2 + 2 * x ^ 4 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -6 * x ^ 2 - 4 * x - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, one]))).add
      ((i13_cont_coef (p := fun x => -6 * x ^ 2 - 4 * x - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, negOne]))).add
      ((i13_cont_coef (p := fun x => -4 * x - 2 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, one]))).add
      ((i13_cont_coef (p := fun x => -4 + 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, one]))).add
      ((i13_cont_coef (p := fun x => -4 - 4 * x - 4 * x ^ 2 - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, one, one]))).add
      ((i13_cont_coef (p := fun x => -4 - 4 * x - 4 * x ^ 2 - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, negOne, one])))

/-- Chunk 1 of `i8Psi4s148k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s148k0S1 (x : ℝ) : ℝ :=
    (-4 - 4 * x - 4 * x ^ 2 - 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one, one, negOne] x) +
    (-16) * hpl [zero, negOne, one, one, one] x +
    (-16) * hpl [zero, one, negOne, one, one] x +
    (-16) * hpl [zero, one, one, negOne, one] x +
    (-16) * hpl [zero, one, one, one, negOne] x

theorem continuousOn_i8Psi4s148k0S1 : ContinuousOn i8Psi4s148k0S1 (Ioc 0 1) := by
  unfold i8Psi4s148k0S1
  exact ((((((i13_cont_coef (p := fun x => -4 - 4 * x - 4 * x ^ 2 - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, one, negOne])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, one, negOne])))

theorem i8Psi4s148k0_eq_S (x : ℝ) : i8Psi4s148k0 x = i8Psi4s148k0S0 x + i8Psi4s148k0S1 x := by
  unfold i8Psi4s148k0 i8Psi4s148k0S0 i8Psi4s148k0S1 i8Psi4s148k0N0 i8Psi4s148k0N1 i8Psi4s148k0N2
    i8Psi4s148k0N3 i8Psi4s148k0N4 i8Psi4s148k0W
  ring

theorem continuousOn_i8Psi4s148k0 : ContinuousOn i8Psi4s148k0 (Ioc 0 1) := by
  rw [show i8Psi4s148k0 = fun x => i8Psi4s148k0S0 x +
    i8Psi4s148k0S1 x from funext i8Psi4s148k0_eq_S]
  exact (continuousOn_i8Psi4s148k0S0.add continuousOn_i8Psi4s148k0S1)

theorem i8Psi4s148k0_one : i8Psi4s148k0 1 = -16 + π ^ 2 - 6 * Real.log 2 ^ 2 + 4 * Li 4 (1 / 2) +
    14 * Real.log 2 + 16 * Li 5 (1 / 2) - 27 / 2 * zeta5 - 7 / 120 * π ^ 4 + Real.log 2 ^ 4 / 6 +
    8 / 15 * Real.log 2 ^ 5 + 21 / 2 * zeta3 + 7 * zeta3 * Real.log 2 ^ 2 +
    16 * Real.log 2 * Li 4 (1 / 2) - 7 / 6 * π ^ 2 * zeta3 - 4 / 9 * π ^ 2 * Real.log 2 ^ 3 -
    π ^ 2 * Real.log 2 ^ 2 / 6 + 7 / 2 * Real.log 2 * zeta3 := by
  rw [i8Psi4s148k0_eq_S]
  unfold i8Psi4s148k0S0 i8Psi4s148k0S1
  rw [hpl_negOne_at_one, hpl_negOne_one_at_one, hpl_negOne_one_one_at_one,
    hpl_zero_negOne_one_at_one, hpl_zero_one_negOne_at_one, hpl_zero_one_one_at_one,
    hpl_negOne_one_one_one_at_one, hpl_zero_negOne_one_one_at_one, hpl_zero_one_negOne_one_at_one,
    hpl_zero_one_one_negOne_at_one, hpl_zero_one_one_one_at_one, hpl_zero_negOne_one_one_one_at_one,
    hpl_zero_one_negOne_one_one_at_one, hpl_zero_one_one_negOne_one_at_one,
    hpl_zero_one_one_one_negOne_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s148 : ContinuousOn i8Psi4s148 (Ioc 0 1) := by
  rw [show i8Psi4s148 = fun x => i8Psi4s148k0 x from rfl]
  exact continuousOn_i8Psi4s148k0

theorem i8Psi4s148_one : i8Psi4s148 1 = -16 + π ^ 2 - 6 * Real.log 2 ^ 2 + 4 * Li 4 (1 / 2) +
    14 * Real.log 2 + 16 * Li 5 (1 / 2) - 27 / 2 * zeta5 - 7 / 120 * π ^ 4 + Real.log 2 ^ 4 / 6 +
    8 / 15 * Real.log 2 ^ 5 + 21 / 2 * zeta3 + 7 * zeta3 * Real.log 2 ^ 2 +
    16 * Real.log 2 * Li 4 (1 / 2) - 7 / 6 * π ^ 2 * zeta3 - 4 / 9 * π ^ 2 * Real.log 2 ^ 3 -
    π ^ 2 * Real.log 2 ^ 2 / 6 + 7 / 2 * Real.log 2 * zeta3 := by
  unfold i8Psi4s148
  rw [i8Psi4s148k0_one]

/-- Chunk 0 of `i8Psi4s149` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s149S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 + 4 * x ^ 3 + 12 * x) / x ^ 2 +
    (-x ^ 4 - 4 * x ^ 3 + 12 * x) / x ^ 2 * hpl [zero] x +
    (2 * x ^ 4 + 4 * x ^ 3 + 12 * x) / x ^ 2 * hpl [zero, zero] x +
    (-4 * x ^ 3 - 4 * x ^ 4 + 12 * x) / x ^ 2 * hpl [zero, zero, zero] x +
    (4 * x ^ 2 + 4 * x ^ 4 + 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero, zero] x +
    (-8) * hpl [zero, zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s149S0 : ContinuousOn i8Psi4s149S0 (Ioc 0 1) := by
  unfold i8Psi4s149S0
  exact ((((((i13_cont_coef (p := fun x => x ^ 4 / 2 + 4 * x ^ 3 + 12 * x) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 4 * x ^ 3 + 12 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 4 * x ^ 3 + 12 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 3 - 4 * x ^ 4 + 12 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 2 + 4 * x ^ 4 + 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, zero])))

theorem i8Psi4s149_eq_S (x : ℝ) : i8Psi4s149 x = i8Psi4s149S0 x := by
  unfold i8Psi4s149 i8Psi4s149S0 i8Psi4s149N0 i8Psi4s149N1 i8Psi4s149N2 i8Psi4s149N3 i8Psi4s149N4
    i8Psi4s149W
  ring

theorem continuousOn_i8Psi4s149 : ContinuousOn i8Psi4s149 (Ioc 0 1) := by
  rw [show i8Psi4s149 = fun x => i8Psi4s149S0 x from funext i8Psi4s149_eq_S]
  exact continuousOn_i8Psi4s149S0

theorem i8Psi4s149_one : i8Psi4s149 1 = 33 / 2 := by
  have h5 : hpl [zero, zero, zero, zero, zero] 1 = 0 := by
    rw [hpl_of_allZero (by decide)]
    simp
  rw [i8Psi4s149_eq_S]
  unfold i8Psi4s149S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_zero_zero_at_one, h5]
  norm_num

/-- Chunk 0 of `i8Psi4s150` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s150S0 (x : ℝ) : ℝ :=
    (-3 * x ^ 4 - 169 / 4 * x ^ 3) / x ^ 2 +
    (-20 * x ^ 2 + 17 / 4 * x ^ 4 + 73 / 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (20 * x + 7 / 4 * x ^ 3 + 23 / 4 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-29 * x ^ 3 - 20 * x ^ 2 - 5 * x ^ 4) / x ^ 2 * hpl [zero, zero] x +
    (4 * x ^ 3 + 20 * x + 7 / 2 * x ^ 4) / x ^ 2 * hpl [zero, one] x +
    (20 * x - 15 / 2 * x ^ 2 - 7 / 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-20 * x ^ 2 + 3 * x ^ 4 + 18 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero] x +
    (-7 * x ^ 4 - 4 * x ^ 3 + 20 * x) / x ^ 2 * hpl [zero, zero, one] x +
    (-7 * x ^ 4 - 4 * x ^ 3 + 20 * x) / x ^ 2 * hpl [zero, one, zero] x +
    (7 * x ^ 3 + 11 * x ^ 2 + 20 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-12) * hpl [zero, zero, zero, zero] x +
    (6 * x ^ 4 + 8 * x ^ 2 + 12 * x + 12 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero, one] x +
    (6 * x ^ 4 + 8 * x ^ 2 + 12 * x + 12 * x ^ 3) / x ^ 2 * hpl [zero, zero, one, zero] x +
    (6 * x ^ 4 + 8 * x ^ 2 + 12 * x + 12 * x ^ 3) / x ^ 2 * hpl [zero, one, zero, zero] x +
    (-18 * x ^ 2 - 6 * x ^ 3 + 12 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero, zero] x) +
    (-12) * hpl [zero, zero, zero, zero, one] x +
    (-12) * hpl [zero, zero, zero, one, zero] x +
    (-12) * hpl [zero, zero, one, zero, zero] x +
    (-12) * hpl [zero, one, zero, zero, zero] x

theorem continuousOn_i8Psi4s150S0 : ContinuousOn i8Psi4s150S0 (Ioc 0 1) := by
  unfold i8Psi4s150S0
  exact (((((((((((((((((((i13_cont_coef (p := fun x => -3 * x ^ 4 -
    169 / 4 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -20 * x ^ 2 + 17 / 4 * x ^ 4 +
        73 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 20 * x + 7 / 4 * x ^ 3 + 23 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -29 * x ^ 3 - 20 * x ^ 2 - 5 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 3 + 20 * x + 7 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => 20 * x - 15 / 2 * x ^ 2 - 7 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -20 * x ^ 2 + 3 * x ^ 4 + 18 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -7 * x ^ 4 - 4 * x ^ 3 + 20 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -7 * x ^ 4 - 4 * x ^ 3 + 20 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => 7 * x ^ 3 + 11 * x ^ 2 + 20 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 6 * x ^ 4 + 8 * x ^ 2 + 12 * x + 12 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      ((i13_cont_coef (p := fun x => 6 * x ^ 4 + 8 * x ^ 2 + 12 * x + 12 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      ((i13_cont_coef (p := fun x => 6 * x ^ 4 + 8 * x ^ 2 + 12 * x + 12 * x ^ 3) (by fun_prop)).mul
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

theorem i8Psi4s150_eq_S (x : ℝ) : i8Psi4s150 x = i8Psi4s150S0 x := by
  unfold i8Psi4s150 i8Psi4s150S0 i8Psi4s150N0 i8Psi4s150N1 i8Psi4s150N2 i8Psi4s150N3 i8Psi4s150N4
    i8Psi4s150W
  ring

theorem continuousOn_i8Psi4s150 : ContinuousOn i8Psi4s150 (Ioc 0 1) := by
  rw [show i8Psi4s150 = fun x => i8Psi4s150S0 x from funext i8Psi4s150_eq_S]
  exact continuousOn_i8Psi4s150S0

theorem i8Psi4s150_one : i8Psi4s150 1 = -181 / 4 - 9 * zeta3 + 12 * zeta5 + 19 / 45 * π ^ 4 +
    55 / 12 * π ^ 2 := by
  rw [i8Psi4s150_eq_S]
  unfold i8Psi4s150S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one, hpl_zero_zero_zero_zero_at_one,
    hpl_zero_zero_zero_one_at_one, hpl_zero_zero_one_zero_at_one, hpl_zero_one_zero_zero_at_one,
    hpl_zero_zero_zero_zero_one_at_one, hpl_zero_zero_zero_one_zero_at_one,
    hpl_zero_zero_one_zero_zero_at_one, hpl_zero_one_zero_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s151k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s151k0S0 (x : ℝ) : ℝ :=
    (-x ^ 3 + 7 / 2 * x ^ 4) / x ^ 2 +
    (-2 * x ^ 4 + 4 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-5 * x ^ 3 - 3 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-32 * x ^ 2 - 4 * x ^ 4 + 8 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-4 * x ^ 2 + 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-6 * x ^ 2 - 6 * x ^ 3 + 32 * x) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-16) * hpl [zero, zero, one] x +
    (-16) * hpl [zero, one, zero] x +
    (-12 * x ^ 4 + 32 * x) / x ^ 2 * hpl [zero, one, one] x +
    (-8 * x ^ 2 + 8 * x ^ 3 + 16 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, one] x) +
    (-8 * x ^ 2 + 8 * x ^ 3 + 16 * x) / x ^ 2 * ((1 - x) * hpl [one, one, zero] x) +
    (8 * x ^ 4 + 16 * x + 16 * x ^ 2 + 16 * x ^ 3) / x ^ 2 * hpl [zero, zero, one, one] x +
    (16) * hpl [zero, one, zero, one] x +
    (16) * hpl [zero, one, one, zero] x +
    (-16) * hpl [zero, zero, zero, one, one] x

theorem continuousOn_i8Psi4s151k0S0 : ContinuousOn i8Psi4s151k0S0 (Ioc 0 1) := by
  unfold i8Psi4s151k0S0
  exact (((((((((((((((i13_cont_coef (p := fun x => -x ^ 3 + 7 / 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 4 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -5 * x ^ 3 - 3 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -32 * x ^ 2 - 4 * x ^ 4 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 2 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -6 * x ^ 2 - 6 * x ^ 3 + 32 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 4 + 32 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 2 + 8 * x ^ 3 + 16 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 2 + 8 * x ^ 3 + 16 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero]))).add
      ((i13_cont_coef (p := fun x => 8 * x ^ 4 + 16 * x + 16 * x ^ 2 +
        16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one, one])))

theorem i8Psi4s151k0_eq_S (x : ℝ) : i8Psi4s151k0 x = i8Psi4s151k0S0 x := by
  unfold i8Psi4s151k0 i8Psi4s151k0S0 i8Psi4s151k0N0 i8Psi4s151k0N1 i8Psi4s151k0N2 i8Psi4s151k0N3
    i8Psi4s151k0N4 i8Psi4s151k0W
  ring

theorem continuousOn_i8Psi4s151k0 : ContinuousOn i8Psi4s151k0 (Ioc 0 1) := by
  rw [show i8Psi4s151k0 = fun x => i8Psi4s151k0S0 x from funext i8Psi4s151k0_eq_S]
  exact continuousOn_i8Psi4s151k0S0

theorem i8Psi4s151k0_one : i8Psi4s151k0 1 = 5 / 2 - 32 * zeta5 + 36 * zeta3 - 14 / 3 * π ^ 2 +
    π ^ 4 / 15 + 8 / 3 * π ^ 2 * zeta3 := by
  rw [i8Psi4s151k0_eq_S]
  unfold i8Psi4s151k0S0
  rw [hpl_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one,
    hpl_zero_one_one_at_one, hpl_zero_zero_one_one_at_one, hpl_zero_one_zero_one_at_one,
    hpl_zero_one_one_zero_at_one, hpl_zero_zero_zero_one_one_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s151k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s151k1S0 (x : ℝ) : ℝ :=
    (2 * x ^ 4 + 94 * x ^ 3) / x ^ 2 +
    (-48 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (-46 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-44 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, one] x +
    (4 * x ^ 3 + 48 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-16 * x ^ 2 + 4 * x ^ 4 + 24 * x ^ 3) / x ^ 2 * hpl [zero, zero, one] x +
    (-16 * x ^ 2 + 4 * x ^ 4 + 24 * x ^ 3) / x ^ 2 * hpl [zero, one, zero] x +
    (4 * x ^ 3 + 16 * x + 20 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, one] x) +
    (4 * x ^ 3 + 16 * x + 20 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one, zero] x) +
    (-16) * hpl [zero, zero, zero, one] x +
    (-16) * hpl [zero, zero, one, zero] x +
    (8 * x ^ 4 + 16 * x + 16 * x ^ 3) / x ^ 2 * hpl [zero, one, zero, one] x +
    (8 * x ^ 4 + 16 * x + 16 * x ^ 3) / x ^ 2 * hpl [zero, one, one, zero] x +
    (-24 * x ^ 2 - 8 * x ^ 3 + 16 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero, one] x) +
    (-24 * x ^ 2 - 8 * x ^ 3 + 16 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, one, zero] x) +
    (-16) * hpl [zero, zero, one, zero, one] x +
    (-16) * hpl [zero, zero, one, one, zero] x +
    (-16) * hpl [zero, one, zero, zero, one] x +
    (-16) * hpl [zero, one, zero, one, zero] x

theorem continuousOn_i8Psi4s151k1S0 : ContinuousOn i8Psi4s151k1S0 (Ioc 0 1) := by
  unfold i8Psi4s151k1S0
  exact (((((((((((((((((((i13_cont_coef (p := fun x => 2 * x ^ 4 + 94 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -48 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -46 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -44 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 3 + 48 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -16 * x ^ 2 + 4 * x ^ 4 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -16 * x ^ 2 + 4 * x ^ 4 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 3 + 16 * x + 20 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 3 + 16 * x + 20 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      ((i13_cont_coef (p := fun x => 8 * x ^ 4 + 16 * x + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => 8 * x ^ 4 + 16 * x + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 8 * x ^ 3 + 16 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero, one]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 8 * x ^ 3 + 16 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one, zero])))

theorem i8Psi4s151k1_eq_S (x : ℝ) : i8Psi4s151k1 x = i8Psi4s151k1S0 x := by
  unfold i8Psi4s151k1 i8Psi4s151k1S0 i8Psi4s151k1N0 i8Psi4s151k1N1 i8Psi4s151k1N2 i8Psi4s151k1N3
    i8Psi4s151k1N4 i8Psi4s151k1W
  ring

theorem continuousOn_i8Psi4s151k1 : ContinuousOn i8Psi4s151k1 (Ioc 0 1) := by
  rw [show i8Psi4s151k1 = fun x => i8Psi4s151k1S0 x from funext i8Psi4s151k1_eq_S]
  exact continuousOn_i8Psi4s151k1S0

theorem i8Psi4s151k1_one : i8Psi4s151k1 1 = 96 - 12 * zeta3 - 8 * π ^ 2 - 8 * zeta5 +
    2 / 15 * π ^ 4 + 8 / 3 * π ^ 2 * zeta3 := by
  rw [i8Psi4s151k1_eq_S]
  unfold i8Psi4s151k1S0
  rw [hpl_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one,
    hpl_zero_zero_zero_one_at_one, hpl_zero_zero_one_zero_at_one, hpl_zero_one_zero_one_at_one,
    hpl_zero_one_one_zero_at_one, hpl_zero_zero_one_zero_one_at_one,
    hpl_zero_zero_one_one_zero_at_one, hpl_zero_one_zero_zero_one_at_one,
    hpl_zero_one_zero_one_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s151k2` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s151k2S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 + 28 * x ^ 3) / x ^ 2 +
    (-x ^ 4 - 28 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (2 * x ^ 4 + 28 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-28 * x ^ 2 - 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-16) * hpl [zero, one, zero, zero] x +
    (-24 * x ^ 2 - 8 * x ^ 3 + 16 * x) / x ^ 2 * ((1 - x) * hpl [one, one, zero, zero] x) +
    (-16) * hpl [zero, one, one, zero, zero] x

theorem continuousOn_i8Psi4s151k2S0 : ContinuousOn i8Psi4s151k2S0 (Ioc 0 1) := by
  unfold i8Psi4s151k2S0
  exact (((((((i13_cont_coef (p := fun x => x ^ 4 / 2 + 28 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 28 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 28 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -28 * x ^ 2 - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 8 * x ^ 3 + 16 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero, zero])))

theorem i8Psi4s151k2_eq_S (x : ℝ) : i8Psi4s151k2 x = i8Psi4s151k2S0 x := by
  unfold i8Psi4s151k2 i8Psi4s151k2S0 i8Psi4s151k2N0 i8Psi4s151k2N1 i8Psi4s151k2N2 i8Psi4s151k2N3
    i8Psi4s151k2N4 i8Psi4s151k2W
  ring

theorem continuousOn_i8Psi4s151k2 : ContinuousOn i8Psi4s151k2 (Ioc 0 1) := by
  rw [show i8Psi4s151k2 = fun x => i8Psi4s151k2S0 x from funext i8Psi4s151k2_eq_S]
  exact continuousOn_i8Psi4s151k2S0

theorem i8Psi4s151k2_one : i8Psi4s151k2 1 = 57 / 2 + 8 * zeta5 - 8 / 15 * π ^ 4 -
    8 / 3 * π ^ 2 * zeta3 := by
  rw [i8Psi4s151k2_eq_S]
  unfold i8Psi4s151k2S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_zero_zero_at_one,
    hpl_zero_one_one_zero_zero_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s151 : ContinuousOn i8Psi4s151 (Ioc 0 1) := by
  rw [show i8Psi4s151 = fun x => i8Psi4s151k0 x + i8Psi4s151k1 x + i8Psi4s151k2 x from rfl]
  exact ((continuousOn_i8Psi4s151k0.add continuousOn_i8Psi4s151k1).add continuousOn_i8Psi4s151k2)

theorem i8Psi4s151_one : i8Psi4s151 1 = 127 - 32 * zeta5 + 24 * zeta3 - 38 / 3 * π ^ 2 -
    π ^ 4 / 3 + 8 / 3 * π ^ 2 * zeta3 := by
  unfold i8Psi4s151
  rw [i8Psi4s151k0_one, i8Psi4s151k1_one, i8Psi4s151k2_one]
  ring

/-- Chunk 0 of `i8Psi4s152` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s152S0 (x : ℝ) : ℝ :=
    (-105 * x ^ 3 - 4 * x ^ 4) / x ^ 2 +
    (x ^ 4 + 30 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (7 * x ^ 3 + 75 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (2 * x ^ 4 + 28 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-30 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (12 * x ^ 3 + 40 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-48 * x ^ 2 + 4 * x ^ 4 + 24 * x ^ 3) / x ^ 2 * hpl [zero, one, one] x +
    (-28 * x ^ 2 - 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, one] x) +
    (-28 * x ^ 2 - 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one, zero] x) +
    (4 * x ^ 2 + 20 * x ^ 3 + 48 * x) / x ^ 2 * ((1 - x) * hpl [one, one, one] x) +
    (-16) * hpl [zero, zero, one, one] x +
    (-16) * hpl [zero, one, zero, one] x +
    (-16) * hpl [zero, one, one, zero] x +
    (8 * x ^ 4 + 16 * x + 16 * x ^ 3 + 32 * x ^ 2) / x ^ 2 * hpl [zero, one, one, one] x +
    (-24 * x ^ 2 - 8 * x ^ 3 + 16 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, one, one] x) +
    (-24 * x ^ 2 - 8 * x ^ 3 + 16 * x) / x ^ 2 * ((1 - x) * hpl [one, one, zero, one] x) +
    (-24 * x ^ 2 - 8 * x ^ 3 + 16 * x) / x ^ 2 * ((1 - x) * hpl [one, one, one, zero] x) +
    (-16) * hpl [zero, zero, one, one, one] x +
    (-16) * hpl [zero, one, zero, one, one] x +
    (-16) * hpl [zero, one, one, zero, one] x

theorem continuousOn_i8Psi4s152S0 : ContinuousOn i8Psi4s152S0 (Ioc 0 1) := by
  unfold i8Psi4s152S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -105 * x ^ 3 -
    4 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 30 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 7 * x ^ 3 + 75 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 28 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -30 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => 12 * x ^ 3 + 40 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      ((i13_cont_coef (p := fun x => -48 * x ^ 2 + 4 * x ^ 4 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -28 * x ^ 2 - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -28 * x ^ 2 - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 2 + 20 * x ^ 3 + 48 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero]))).add
      ((i13_cont_coef (p := fun x => 8 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        32 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, one]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 8 * x ^ 3 + 16 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one, one]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 8 * x ^ 3 + 16 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 8 * x ^ 3 + 16 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero, one])))

/-- Chunk 1 of `i8Psi4s152` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s152S1 (x : ℝ) : ℝ :=
    (-16) * hpl [zero, one, one, one, zero] x

theorem continuousOn_i8Psi4s152S1 : ContinuousOn i8Psi4s152S1 (Ioc 0 1) := by
  unfold i8Psi4s152S1
  exact (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, one, zero]))

theorem i8Psi4s152_eq_S (x : ℝ) : i8Psi4s152 x = i8Psi4s152S0 x + i8Psi4s152S1 x := by
  unfold i8Psi4s152 i8Psi4s152S0 i8Psi4s152S1 i8Psi4s152N0 i8Psi4s152N1 i8Psi4s152N2 i8Psi4s152N3
    i8Psi4s152N4 i8Psi4s152W
  ring

theorem continuousOn_i8Psi4s152 : ContinuousOn i8Psi4s152 (Ioc 0 1) := by
  rw [show i8Psi4s152 = fun x => i8Psi4s152S0 x + i8Psi4s152S1 x from funext i8Psi4s152_eq_S]
  exact (continuousOn_i8Psi4s152S0.add continuousOn_i8Psi4s152S1)

theorem i8Psi4s152_one : i8Psi4s152 1 = -109 - 20 * zeta3 + 5 * π ^ 2 + 32 * zeta5 +
    38 / 45 * π ^ 4 - 8 / 3 * π ^ 2 * zeta3 := by
  rw [i8Psi4s152_eq_S]
  unfold i8Psi4s152S0 i8Psi4s152S1
  rw [hpl_zero_at_one, hpl_zero_one_at_one, hpl_zero_one_one_at_one, hpl_zero_zero_one_one_at_one,
    hpl_zero_one_zero_one_at_one, hpl_zero_one_one_zero_at_one, hpl_zero_one_one_one_at_one,
    hpl_zero_zero_one_one_one_at_one, hpl_zero_one_zero_one_one_at_one,
    hpl_zero_one_one_zero_one_at_one, hpl_zero_one_one_one_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s153` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s153S0 (x : ℝ) : ℝ :=
    (x + x ^ 3 - x ^ 4 / 32) / x ^ 2 +
    (x - x ^ 3 + x ^ 4 / 16) / x ^ 2 * hpl [zero] x +
    (x + x ^ 3 - x ^ 4 / 8) / x ^ 2 * hpl [zero, zero] x +
    (x - x ^ 3 + x ^ 4 / 4) / x ^ 2 * hpl [zero, zero, zero] x +
    (x + x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero, zero, zero, zero] x +
    (1) * hpl [zero, zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s153S0 : ContinuousOn i8Psi4s153S0 (Ioc 0 1) := by
  unfold i8Psi4s153S0
  exact ((((((i13_cont_coef (p := fun x => x + x ^ 3 - x ^ 4 / 32) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x - x ^ 3 + x ^ 4 / 16) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x + x ^ 3 - x ^ 4 / 8) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x - x ^ 3 + x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => x + x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, zero])))

theorem i8Psi4s153_eq_S (x : ℝ) : i8Psi4s153 x = i8Psi4s153S0 x := by
  unfold i8Psi4s153 i8Psi4s153S0 i8Psi4s153N0 i8Psi4s153N1 i8Psi4s153N2 i8Psi4s153N3 i8Psi4s153N4
    i8Psi4s153W
  ring

theorem continuousOn_i8Psi4s153 : ContinuousOn i8Psi4s153 (Ioc 0 1) := by
  rw [show i8Psi4s153 = fun x => i8Psi4s153S0 x from funext i8Psi4s153_eq_S]
  exact continuousOn_i8Psi4s153S0

theorem i8Psi4s153_one : i8Psi4s153 1 = 63 / 32 := by
  have h5 : hpl [zero, zero, zero, zero, zero] 1 = 0 := by
    rw [hpl_of_allZero (by decide)]
    simp
  rw [i8Psi4s153_eq_S]
  unfold i8Psi4s153S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_zero_zero_at_one, h5]
  norm_num

/-- Chunk 0 of `i8Psi4s154` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s154S0 (x : ℝ) : ℝ :=
    (-49 / 8 * x ^ 3 + x ^ 4 / 4) / x ^ 2 +
    (-2 * x ^ 2 - 3 / 8 * x ^ 4 + 17 / 4 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (2 * x - x ^ 3 / 8 + 15 / 8 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x ^ 4 / 2 - 2 * x ^ 2 - 5 / 2 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (2 * x + 2 * x ^ 3 - x ^ 4 / 4) / x ^ 2 * hpl [zero, one] x +
    (2 * x - 7 / 4 * x ^ 2 + x ^ 3 / 4) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (x ^ 3 - 2 * x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [zero, zero, zero] x +
    (x ^ 4 / 2 - 2 * x ^ 3 + 2 * x) / x ^ 2 * hpl [zero, zero, one] x +
    (x ^ 4 / 2 - 2 * x ^ 3 + 2 * x) / x ^ 2 * hpl [zero, one, zero] x +
    (2 * x - x ^ 3 / 2 + 3 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-2) * hpl [zero, zero, zero, zero] x +
    (-x ^ 4 + 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero, one] x +
    (-x ^ 4 + 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [zero, zero, one, zero] x +
    (-x ^ 4 + 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [zero, one, zero, zero] x +
    (x ^ 3 - x ^ 2 + 2 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero, zero] x) +
    (2) * hpl [zero, zero, zero, zero, one] x +
    (2) * hpl [zero, zero, zero, one, zero] x +
    (2) * hpl [zero, zero, one, zero, zero] x +
    (2) * hpl [zero, one, zero, zero, zero] x

theorem continuousOn_i8Psi4s154S0 : ContinuousOn i8Psi4s154S0 (Ioc 0 1) := by
  unfold i8Psi4s154S0
  exact (((((((((((((((((((i13_cont_coef (p := fun x => -49 / 8 * x ^ 3 +
    x ^ 4 / 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 2 - 3 / 8 * x ^ 4 + 17 / 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 2 * x - x ^ 3 / 8 + 15 / 8 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - 2 * x ^ 2 - 5 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x + 2 * x ^ 3 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => 2 * x - 7 / 4 * x ^ 2 + x ^ 3 / 4) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - 2 * x ^ 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - 2 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - 2 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x - x ^ 3 / 2 + 3 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 + 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 + 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 + 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - x ^ 2 + 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero, zero])))

theorem i8Psi4s154_eq_S (x : ℝ) : i8Psi4s154 x = i8Psi4s154S0 x := by
  unfold i8Psi4s154 i8Psi4s154S0 i8Psi4s154N0 i8Psi4s154N1 i8Psi4s154N2 i8Psi4s154N3 i8Psi4s154N4
    i8Psi4s154W
  ring

theorem continuousOn_i8Psi4s154 : ContinuousOn i8Psi4s154 (Ioc 0 1) := by
  rw [show i8Psi4s154 = fun x => i8Psi4s154S0 x from funext i8Psi4s154_eq_S]
  exact continuousOn_i8Psi4s154S0

theorem i8Psi4s154_one : i8Psi4s154 1 = -47 / 8 - 2 * zeta5 - zeta3 / 2 + π ^ 4 / 30 +
    5 / 8 * π ^ 2 := by
  rw [i8Psi4s154_eq_S]
  unfold i8Psi4s154S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one, hpl_zero_zero_zero_zero_at_one,
    hpl_zero_zero_zero_one_at_one, hpl_zero_zero_one_zero_at_one, hpl_zero_one_zero_zero_at_one,
    hpl_zero_zero_zero_zero_one_at_one, hpl_zero_zero_zero_one_zero_at_one,
    hpl_zero_zero_one_zero_zero_at_one, hpl_zero_one_zero_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s155k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s155k0S0 (x : ℝ) : ℝ :=
    (-x ^ 4 / 2 + 41 / 4 * x ^ 3) / x ^ 2 +
    (-5 / 2 * x ^ 3 + x ^ 4 / 4) / x ^ 2 * hpl [zero] x +
    (-31 / 4 * x ^ 2 + 3 / 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x ^ 4 - 5 * x ^ 3 - 4 * x ^ 2) / x ^ 2 * hpl [zero, one] x +
    (-x ^ 3 / 2 + 5 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (x ^ 3 / 2 + 4 * x - 7 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-x ^ 4 - 4 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * hpl [zero, zero, one] x +
    (-4) * hpl [zero, one, zero] x +
    (x ^ 4 - 4 * x ^ 3 + 4 * x) / x ^ 2 * hpl [zero, one, one] x +
    (-x ^ 3 + 3 * x ^ 2 + 4 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, one] x) +
    (-x ^ 3 + 3 * x ^ 2 + 4 * x) / x ^ 2 * ((1 - x) * hpl [one, one, zero] x) +
    (-4) * hpl [zero, zero, zero, one] x +
    (-2 * x ^ 4 + 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [zero, zero, one, one] x +
    (-2 * x ^ 4 + 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [zero, one, zero, one] x +
    (-2 * x ^ 4 + 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [zero, one, one, zero] x +
    (-2 * x ^ 2 + 2 * x ^ 3 + 4 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero, one] x) +
    (4) * hpl [zero, zero, zero, one, one] x +
    (4) * hpl [zero, zero, one, zero, one] x +
    (4) * hpl [zero, zero, one, one, zero] x +
    (4) * hpl [zero, one, zero, zero, one] x

theorem continuousOn_i8Psi4s155k0S0 : ContinuousOn i8Psi4s155k0S0 (Ioc 0 1) := by
  unfold i8Psi4s155k0S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -x ^ 4 / 2 +
    41 / 4 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -5 / 2 * x ^ 3 + x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -31 / 4 * x ^ 2 + 3 / 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 5 * x ^ 3 - 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 / 2 + 5 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 + 4 * x - 7 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 4 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 4 * x ^ 3 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 + 3 * x ^ 2 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 + 3 * x ^ 2 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 4 + 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 4 + 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 4 + 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 2 + 2 * x ^ 3 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero, one])))

theorem i8Psi4s155k0_eq_S (x : ℝ) : i8Psi4s155k0 x = i8Psi4s155k0S0 x := by
  unfold i8Psi4s155k0 i8Psi4s155k0S0 i8Psi4s155k0N0 i8Psi4s155k0N1 i8Psi4s155k0N2 i8Psi4s155k0N3
    i8Psi4s155k0N4 i8Psi4s155k0W
  ring

theorem continuousOn_i8Psi4s155k0 : ContinuousOn i8Psi4s155k0 (Ioc 0 1) := by
  rw [show i8Psi4s155k0 = fun x => i8Psi4s155k0S0 x from funext i8Psi4s155k0_eq_S]
  exact continuousOn_i8Psi4s155k0S0

theorem i8Psi4s155k0_one : i8Psi4s155k0 1 = 39 / 4 + 2 * zeta5 + 6 * zeta3 - 11 / 180 * π ^ 4 -
    4 / 3 * π ^ 2 := by
  rw [i8Psi4s155k0_eq_S]
  unfold i8Psi4s155k0S0
  rw [hpl_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one,
    hpl_zero_one_one_at_one, hpl_zero_zero_zero_one_at_one, hpl_zero_zero_one_one_at_one,
    hpl_zero_one_zero_one_at_one, hpl_zero_one_one_zero_at_one, hpl_zero_zero_zero_one_one_at_one,
    hpl_zero_zero_one_zero_one_at_one, hpl_zero_zero_one_one_zero_at_one,
    hpl_zero_one_zero_zero_one_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s155k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s155k1S0 (x : ℝ) : ℝ :=
    (-x ^ 4 / 4 + 5 / 2 * x ^ 3) / x ^ 2 +
    (x ^ 4 / 2 - 5 / 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero, zero] x +
    (-x ^ 3 / 2 + 3 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-x ^ 4 + 2 * x ^ 3) / x ^ 2 * hpl [zero, one, zero] x +
    (x ^ 3 - x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-4) * hpl [zero, zero, one, zero] x +
    (-4) * hpl [zero, one, zero, zero] x +
    (-2 * x ^ 2 + 2 * x ^ 3 + 4 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, one, zero] x) +
    (-2 * x ^ 2 + 2 * x ^ 3 + 4 * x) / x ^ 2 * ((1 - x) * hpl [one, one, zero, zero] x) +
    (4) * hpl [zero, one, zero, one, zero] x +
    (4) * hpl [zero, one, one, zero, zero] x

theorem continuousOn_i8Psi4s155k1S0 : ContinuousOn i8Psi4s155k1S0 (Ioc 0 1) := by
  unfold i8Psi4s155k1S0
  exact ((((((((((((i13_cont_coef (p := fun x => -x ^ 4 / 4 + 5 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - 5 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 / 2 + 3 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 2 + 2 * x ^ 3 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 2 + 2 * x ^ 3 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero, zero])))

theorem i8Psi4s155k1_eq_S (x : ℝ) : i8Psi4s155k1 x = i8Psi4s155k1S0 x := by
  unfold i8Psi4s155k1 i8Psi4s155k1S0 i8Psi4s155k1N0 i8Psi4s155k1N1 i8Psi4s155k1N2 i8Psi4s155k1N3
    i8Psi4s155k1N4 i8Psi4s155k1W
  ring

theorem continuousOn_i8Psi4s155k1 : ContinuousOn i8Psi4s155k1 (Ioc 0 1) := by
  rw [show i8Psi4s155k1 = fun x => i8Psi4s155k1S0 x from funext i8Psi4s155k1_eq_S]
  exact continuousOn_i8Psi4s155k1S0

theorem i8Psi4s155k1_one : i8Psi4s155k1 1 = 9 / 4 - 2 * zeta3 + 6 * zeta5 -
    2 / 3 * π ^ 2 * zeta3 := by
  rw [i8Psi4s155k1_eq_S]
  unfold i8Psi4s155k1S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_zero_at_one,
    hpl_zero_zero_one_zero_at_one, hpl_zero_one_zero_zero_at_one, hpl_zero_one_zero_one_zero_at_one,
    hpl_zero_one_one_zero_zero_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s155 : ContinuousOn i8Psi4s155 (Ioc 0 1) := by
  rw [show i8Psi4s155 = fun x => i8Psi4s155k0 x + i8Psi4s155k1 x from rfl]
  exact (continuousOn_i8Psi4s155k0.add continuousOn_i8Psi4s155k1)

theorem i8Psi4s155_one : i8Psi4s155 1 = 12 + 4 * zeta3 + 8 * zeta5 - 11 / 180 * π ^ 4 -
    4 / 3 * π ^ 2 - 2 / 3 * π ^ 2 * zeta3 := by
  unfold i8Psi4s155
  rw [i8Psi4s155k0_one, i8Psi4s155k1_one]
  ring

end QED.ThreeLoopD
