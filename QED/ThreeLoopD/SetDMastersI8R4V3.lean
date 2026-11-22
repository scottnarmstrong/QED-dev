/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4V2

/-!
# Set (d), master `I₈`: continuity and values at `1` of the sub-pieces 63 to 74 of `Ψ₄`

Each sub-piece `Ψ₄⁽ⁿ⁾` is continuous on `(0, 1]` (the words beginning with `1` carry a factor
`1 - ξ`), and its value at `ξ = 1` follows from the values of the harmonic polylogarithms at `1`.

## Main results

* `QED.ThreeLoopD.continuousOn_i8Psi4s63`, `QED.ThreeLoopD.i8Psi4s63_one` and their
  companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- Chunk 0 of `i8Psi4s63` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s63S0 (x : ℝ) : ℝ :=
    (-x ^ 4 + 15 * x ^ 3) / x ^ 2 +
    (-7 * x ^ 3 - 17 / 2 * x ^ 2 + 3 / 2 * x ^ 4) / x ^ 2 * hpl [negOne] x +
    (x ^ 3 / 2 - 13 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-2 * x ^ 4 + 2 * x ^ 2) / x ^ 2 * hpl [negOne, negOne] x +
    (x ^ 4 - 7 * x ^ 2 - 6 * x ^ 3) / x ^ 2 * hpl [negOne, one] x +
    (-x ^ 3 + 5 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (-4 * x - 2 * x ^ 2 + 2 * x ^ 4 + 4 * x ^ 3) / x ^ 2 * hpl [negOne, negOne, negOne] x +
    (-4 * x - 2 * x ^ 4 + 2 * x ^ 2 + 4 * x ^ 3) / x ^ 2 * hpl [negOne, negOne, one] x +
    (-4 * x - 2 * x ^ 4 + 2 * x ^ 2 + 4 * x ^ 3) / x ^ 2 * hpl [negOne, one, negOne] x +
    (8) * hpl [zero, negOne, negOne] x +
    (4) * hpl [zero, negOne, one] x +
    (4) * hpl [zero, one, negOne] x +
    (-4 * x - 2 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, negOne] x) +
    (-4 + 4 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, negOne, one] x +
    (-4 + 4 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, one, negOne] x +
    (-4 + 4 * x ^ 4) / x ^ 2 * hpl [negOne, one, negOne, negOne] x +
    (4) * hpl [zero, negOne, negOne, negOne] x +
    (-4) * hpl [zero, negOne, negOne, one] x +
    (-4) * hpl [zero, negOne, one, negOne] x +
    (-4) * hpl [zero, one, negOne, negOne] x

theorem continuousOn_i8Psi4s63S0 : ContinuousOn i8Psi4s63S0 (Ioc 0 1) := by
  unfold i8Psi4s63S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -x ^ 4 + 15 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -7 * x ^ 3 - 17 / 2 * x ^ 2 + 3 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 - 13 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 4 + 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 7 * x ^ 2 - 6 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 + 5 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -4 * x - 2 * x ^ 2 + 2 * x ^ 4 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => -4 * x - 2 * x ^ 4 + 2 * x ^ 2 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, one]))).add
      ((i13_cont_coef (p := fun x => -4 * x - 2 * x ^ 4 + 2 * x ^ 2 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -4 * x - 2 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => -4 + 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, negOne, one]))).add
      ((i13_cont_coef (p := fun x => -4 + 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, one, negOne]))).add
      ((i13_cont_coef (p := fun x => -4 + 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, negOne])))

/-- Chunk 1 of `i8Psi4s63` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s63S1 (x : ℝ) : ℝ :=
    (-4 - 4 * x - 4 * x ^ 2 - 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, negOne, negOne] x) +
    (-16) * hpl [zero, negOne, negOne, negOne, one] x +
    (-16) * hpl [zero, negOne, negOne, one, negOne] x +
    (-16) * hpl [zero, negOne, one, negOne, negOne] x +
    (-16) * hpl [zero, one, negOne, negOne, negOne] x

theorem continuousOn_i8Psi4s63S1 : ContinuousOn i8Psi4s63S1 (Ioc 0 1) := by
  unfold i8Psi4s63S1
  exact ((((((i13_cont_coef (p := fun x => -4 - 4 * x - 4 * x ^ 2 - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, negOne, negOne])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, negOne, negOne])))

theorem i8Psi4s63_eq_S (x : ℝ) : i8Psi4s63 x = i8Psi4s63S0 x + i8Psi4s63S1 x := by
  unfold i8Psi4s63 i8Psi4s63S0 i8Psi4s63S1 i8Psi4s63N0 i8Psi4s63N1 i8Psi4s63N2 i8Psi4s63N3
    i8Psi4s63N4 i8Psi4s63W
  ring

theorem continuousOn_i8Psi4s63 : ContinuousOn i8Psi4s63 (Ioc 0 1) := by
  rw [show i8Psi4s63 = fun x => i8Psi4s63S0 x + i8Psi4s63S1 x from funext i8Psi4s63_eq_S]
  exact (continuousOn_i8Psi4s63S0.add continuousOn_i8Psi4s63S1)

theorem i8Psi4s63_one : i8Psi4s63 1 = 14 - π ^ 2 - 16 * Li 5 (1 / 2) - 14 * Real.log 2 -
    4 * Li 4 (1 / 2) + 2 * zeta5 + 6 * Real.log 2 ^ 2 - 8 / 15 * Real.log 2 ^ 5 -
    Real.log 2 ^ 4 / 6 + 7 / 2 * zeta3 + 13 / 360 * π ^ 4 - 16 * Real.log 2 * Li 4 (1 / 2) -
    7 * zeta3 * Real.log 2 ^ 2 - 7 / 2 * Real.log 2 * zeta3 + π ^ 2 * Real.log 2 ^ 2 / 6 +
    4 / 9 * π ^ 2 * Real.log 2 ^ 3 + 7 / 6 * π ^ 2 * zeta3 := by
  rw [i8Psi4s63_eq_S]
  unfold i8Psi4s63S0 i8Psi4s63S1
  rw [hpl_negOne_at_one, hpl_negOne_negOne_at_one, hpl_negOne_one_at_one,
    hpl_negOne_negOne_negOne_at_one, hpl_negOne_negOne_one_at_one, hpl_negOne_one_negOne_at_one,
    hpl_zero_negOne_negOne_at_one, hpl_zero_negOne_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_negOne_negOne_negOne_one_at_one, hpl_negOne_negOne_one_negOne_at_one,
    hpl_negOne_one_negOne_negOne_at_one, hpl_zero_negOne_negOne_negOne_at_one,
    hpl_zero_negOne_negOne_one_at_one, hpl_zero_negOne_one_negOne_at_one,
    hpl_zero_one_negOne_negOne_at_one, hpl_zero_negOne_negOne_negOne_one_at_one,
    hpl_zero_negOne_negOne_one_negOne_at_one, hpl_zero_negOne_one_negOne_negOne_at_one,
    hpl_zero_one_negOne_negOne_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s64` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s64S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 - 9 / 2 * x ^ 3) / x ^ 2 +
    (-3 / 4 * x ^ 4 + 3 / 2 * x ^ 3 + 9 / 4 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (-x ^ 3 / 4 + 9 / 4 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (2 * x + 2 * x ^ 3 - x ^ 4 / 2 + 9 / 2 * x ^ 2) / x ^ 2 * hpl [negOne, one] x +
    (x ^ 4 - 2 * x ^ 2) / x ^ 2 * hpl [zero, negOne] x +
    (-2) * hpl [zero, one] x +
    (x ^ 3 / 2 + 2 * x - 3 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (x ^ 2 - x ^ 4 - 2 * x ^ 3 + 2 * x) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (x ^ 4 - 2 * x ^ 3 + 2 * x) / x ^ 2 * hpl [zero, negOne, one] x +
    (-4) * hpl [zero, zero, negOne] x +
    (x ^ 4 - 2 * x ^ 3 + 2 * x) / x ^ 2 * hpl [zero, one, negOne] x +
    (x ^ 2 - x ^ 3 + 2 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, negOne, one] x +
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one, negOne] x +
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero, negOne] x +
    (-2) * hpl [zero, negOne, zero, negOne] x +
    (2) * hpl [zero, zero, negOne, one] x +
    (2) * hpl [zero, zero, one, negOne] x +
    (2) * hpl [zero, one, zero, negOne] x +
    (2 + 2 * x + 2 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero, negOne] x)

theorem continuousOn_i8Psi4s64S0 : ContinuousOn i8Psi4s64S0 (Ioc 0 1) := by
  unfold i8Psi4s64S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 / 2 -
    9 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -3 / 4 * x ^ 4 + 3 / 2 * x ^ 3 +
        9 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 / 4 + 9 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => 2 * x + 2 * x ^ 3 - x ^ 4 / 2 +
        9 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 + 2 * x - 3 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 - x ^ 4 - 2 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 2 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 2 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 - x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, one]))).add
      ((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x + 2 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero, negOne])))

/-- Chunk 1 of `i8Psi4s64` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s64S1 (x : ℝ) : ℝ :=
    (8) * hpl [zero, negOne, zero, negOne, one] x +
    (8) * hpl [zero, negOne, zero, one, negOne] x +
    (8) * hpl [zero, negOne, one, zero, negOne] x +
    (8) * hpl [zero, one, negOne, zero, negOne] x

theorem continuousOn_i8Psi4s64S1 : ContinuousOn i8Psi4s64S1 (Ioc 0 1) := by
  unfold i8Psi4s64S1
  exact ((((continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne, one])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero, negOne])))

theorem i8Psi4s64_eq_S (x : ℝ) : i8Psi4s64 x = i8Psi4s64S0 x + i8Psi4s64S1 x := by
  unfold i8Psi4s64 i8Psi4s64S0 i8Psi4s64S1 i8Psi4s64N0 i8Psi4s64N1 i8Psi4s64N2 i8Psi4s64N3
    i8Psi4s64N4 i8Psi4s64W
  ring

theorem continuousOn_i8Psi4s64 : ContinuousOn i8Psi4s64 (Ioc 0 1) := by
  rw [show i8Psi4s64 = fun x => i8Psi4s64S0 x + i8Psi4s64S1 x from funext i8Psi4s64_eq_S]
  exact (continuousOn_i8Psi4s64S0.add continuousOn_i8Psi4s64S1)

theorem i8Psi4s64_one : i8Psi4s64 1 = -4 - 4 * Real.log 2 ^ 2 + 3 * Real.log 2 +
    4 * Li 4 (1 / 2) + 32 * Li 5 (1 / 2) - 33 / 4 * zeta5 - 19 / 8 * zeta3 - 7 / 240 * π ^ 4 +
    π ^ 2 / 4 + Real.log 2 ^ 4 / 6 + 16 / 15 * Real.log 2 ^ 5 + 14 * zeta3 * Real.log 2 ^ 2 +
    32 * Real.log 2 * Li 4 (1 / 2) - 23 / 12 * π ^ 2 * zeta3 - 8 / 9 * π ^ 2 * Real.log 2 ^ 3 -
    π ^ 2 * Real.log 2 ^ 2 / 6 + 7 / 2 * Real.log 2 * zeta3 := by
  rw [i8Psi4s64_eq_S]
  unfold i8Psi4s64S0 i8Psi4s64S1
  rw [hpl_negOne_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one, hpl_zero_one_at_one,
    hpl_negOne_zero_negOne_at_one, hpl_zero_negOne_one_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_one_negOne_at_one, hpl_negOne_zero_negOne_one_at_one,
    hpl_negOne_zero_one_negOne_at_one, hpl_negOne_one_zero_negOne_at_one,
    hpl_zero_negOne_zero_negOne_at_one, hpl_zero_zero_negOne_one_at_one,
    hpl_zero_zero_one_negOne_at_one, hpl_zero_one_zero_negOne_at_one,
    hpl_zero_negOne_zero_negOne_one_at_one, hpl_zero_negOne_zero_one_negOne_at_one,
    hpl_zero_negOne_one_zero_negOne_at_one, hpl_zero_one_negOne_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s65` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s65S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 - x ^ 3 / 2) / x ^ 2 +
    (-3 / 2 * x ^ 3 - 3 / 4 * x ^ 2 - 3 / 4 * x ^ 4) / x ^ 2 * hpl [negOne] x +
    (-x ^ 3 / 4 + 5 / 4 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x ^ 4 + 3 * x + 3 * x ^ 3 + 5 * x ^ 2) / x ^ 2 * hpl [negOne, negOne] x +
    (x + x ^ 3 - x ^ 4 / 2 + 5 / 2 * x ^ 2) / x ^ 2 * hpl [negOne, one] x +
    (-4) * hpl [zero, negOne] x +
    (-1) * hpl [zero, one] x +
    (x + x ^ 3 / 2 - x ^ 2 / 2) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (1 + x ^ 4 - 2 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, one] x +
    (1 + x ^ 4 - 2 * x ^ 2) / x ^ 2 * hpl [negOne, one, negOne] x +
    (-x ^ 2 - x ^ 4 - 2 * x ^ 3 + 2 * x) / x ^ 2 * hpl [zero, negOne, negOne] x +
    (1) * hpl [zero, negOne, one] x +
    (1) * hpl [zero, one, negOne] x +
    (1 + x - x ^ 2 - x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, negOne] x) +
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, negOne, one] x +
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, one, negOne] x +
    (-2) * hpl [zero, zero, negOne, negOne] x +
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [zero, one, negOne, negOne] x +
    (2 + 2 * x + 2 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne, negOne] x) +
    (8) * hpl [zero, zero, negOne, negOne, one] x

theorem continuousOn_i8Psi4s65S0 : ContinuousOn i8Psi4s65S0 (Ioc 0 1) := by
  unfold i8Psi4s65S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 / 2 - x ^ 3 / 2) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -3 / 2 * x ^ 3 - 3 / 4 * x ^ 2 -
        3 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 / 4 + 5 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 3 * x + 3 * x ^ 3 + 5 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x + x ^ 3 - x ^ 4 / 2 + 5 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x + x ^ 3 / 2 - x ^ 2 / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => 1 + x ^ 4 - 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, one]))).add
      ((i13_cont_coef (p := fun x => 1 + x ^ 4 - 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -x ^ 2 - x ^ 4 - 2 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      ((i13_cont_coef (p := fun x => 1 + x - x ^ 2 - x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, one]))).add
      ((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x + 2 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne, one])))

/-- Chunk 1 of `i8Psi4s65` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s65S1 (x : ℝ) : ℝ :=
    (8) * hpl [zero, zero, negOne, one, negOne] x +
    (8) * hpl [zero, zero, one, negOne, negOne] x +
    (8) * hpl [zero, one, zero, negOne, negOne] x

theorem continuousOn_i8Psi4s65S1 : ContinuousOn i8Psi4s65S1 (Ioc 0 1) := by
  unfold i8Psi4s65S1
  exact (((continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one, negOne])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne, negOne])))

theorem i8Psi4s65_eq_S (x : ℝ) : i8Psi4s65 x = i8Psi4s65S0 x + i8Psi4s65S1 x := by
  unfold i8Psi4s65 i8Psi4s65S0 i8Psi4s65S1 i8Psi4s65N0 i8Psi4s65N1 i8Psi4s65N2 i8Psi4s65N3
    i8Psi4s65N4 i8Psi4s65W
  ring

theorem continuousOn_i8Psi4s65 : ContinuousOn i8Psi4s65 (Ioc 0 1) := by
  rw [show i8Psi4s65 = fun x => i8Psi4s65S0 x + i8Psi4s65S1 x from funext i8Psi4s65_eq_S]
  exact (continuousOn_i8Psi4s65S0.add continuousOn_i8Psi4s65S1)

theorem i8Psi4s65_one : i8Psi4s65 1 = -32 * Li 5 (1 / 2) - 4 * Li 4 (1 / 2) - 3 * Real.log 2 +
    4 * Real.log 2 ^ 2 - 16 / 15 * Real.log 2 ^ 5 - π ^ 2 / 6 - Real.log 2 ^ 4 / 6 + π ^ 4 / 24 +
    3 / 8 * zeta3 + 39 / 2 * zeta5 - 32 * Real.log 2 * Li 4 (1 / 2) -
    14 * zeta3 * Real.log 2 ^ 2 - 7 / 2 * Real.log 2 * zeta3 + π ^ 2 * Real.log 2 ^ 2 / 6 +
    7 / 6 * π ^ 2 * zeta3 + 8 / 9 * π ^ 2 * Real.log 2 ^ 3 := by
  rw [i8Psi4s65_eq_S]
  unfold i8Psi4s65S0 i8Psi4s65S1
  rw [hpl_negOne_at_one, hpl_negOne_negOne_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one,
    hpl_zero_one_at_one, hpl_negOne_negOne_one_at_one, hpl_negOne_one_negOne_at_one,
    hpl_zero_negOne_negOne_at_one, hpl_zero_negOne_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_negOne_negOne_one_at_one, hpl_zero_negOne_one_negOne_at_one,
    hpl_zero_zero_negOne_negOne_at_one, hpl_zero_one_negOne_negOne_at_one,
    hpl_zero_zero_negOne_negOne_one_at_one, hpl_zero_zero_negOne_one_negOne_at_one,
    hpl_zero_zero_one_negOne_negOne_at_one, hpl_zero_one_zero_negOne_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s66` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s66S0 (x : ℝ) : ℝ :=
    (-5 / 4 * x ^ 3 - x ^ 4 / 4) / x ^ 2 +
    (-7 / 4 * x - 3 / 8 * x ^ 2 + 3 / 8 * x ^ 4 + 7 / 4 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (2) * hpl [zero] x +
    (-x / 4 - x ^ 2 / 8 + x ^ 3 / 8) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-1 / 4 + x ^ 4 / 4) / x ^ 2 * hpl [negOne, one] x +
    (-3 / 2 * x - 3 / 2 * x ^ 3 - x ^ 4 / 2 + x ^ 2 / 4) / x ^ 2 * hpl [zero, negOne] x +
    (-1 / 4) * hpl [zero, one] x +
    (-1 / 4 - x / 4 - x ^ 2 / 4 - x ^ 3 / 4) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (-1 / 2 - x ^ 4 / 2) / x ^ 2 * hpl [zero, negOne, one] x +
    (x ^ 3 + x ^ 2 / 2 + x ^ 4 / 2 - x) / x ^ 2 * hpl [zero, zero, negOne] x +
    (-1 / 2 - x ^ 4 / 2) / x ^ 2 * hpl [zero, one, negOne] x +
    (-1 / 2 + x ^ 2 / 2 + x ^ 3 / 2 - x / 2) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (-1 + x ^ 4) / x ^ 2 * hpl [zero, zero, negOne, one] x +
    (1) * hpl [zero, zero, zero, negOne] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [zero, zero, one, negOne] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [zero, one, zero, negOne] x +
    (-1 - x - x ^ 2 - x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, zero, negOne] x) +
    (-4) * hpl [zero, zero, zero, negOne, one] x +
    (-4) * hpl [zero, zero, zero, one, negOne] x +
    (-4) * hpl [zero, zero, one, zero, negOne] x

theorem continuousOn_i8Psi4s66S0 : ContinuousOn i8Psi4s66S0 (Ioc 0 1) := by
  unfold i8Psi4s66S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -5 / 4 * x ^ 3 -
    x ^ 4 / 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -7 / 4 * x - 3 / 8 * x ^ 2 + 3 / 8 * x ^ 4 +
        7 / 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x / 4 - x ^ 2 / 8 + x ^ 3 / 8) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -1 / 4 + x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -3 / 2 * x - 3 / 2 * x ^ 3 - x ^ 4 / 2 +
        x ^ 2 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -1 / 4 - x / 4 - x ^ 2 / 4 - x ^ 3 / 4) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + x ^ 2 / 2 + x ^ 4 / 2 - x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 2 / 2 + x ^ 3 / 2 - x / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 - x - x ^ 2 - x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero, negOne])))

/-- Chunk 1 of `i8Psi4s66` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s66S1 (x : ℝ) : ℝ :=
    (-4) * hpl [zero, one, zero, zero, negOne] x

theorem continuousOn_i8Psi4s66S1 : ContinuousOn i8Psi4s66S1 (Ioc 0 1) := by
  unfold i8Psi4s66S1
  exact (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero, negOne]))

theorem i8Psi4s66_eq_S (x : ℝ) : i8Psi4s66 x = i8Psi4s66S0 x + i8Psi4s66S1 x := by
  unfold i8Psi4s66 i8Psi4s66S0 i8Psi4s66S1 i8Psi4s66N0 i8Psi4s66N1 i8Psi4s66N2 i8Psi4s66N3
    i8Psi4s66N4 i8Psi4s66W
  ring

theorem continuousOn_i8Psi4s66 : ContinuousOn i8Psi4s66 (Ioc 0 1) := by
  rw [show i8Psi4s66 = fun x => i8Psi4s66S0 x + i8Psi4s66S1 x from funext i8Psi4s66_eq_S]
  exact (continuousOn_i8Psi4s66S0.add continuousOn_i8Psi4s66S1)

theorem i8Psi4s66_one : i8Psi4s66 1 = -3 / 2 - 59 / 8 * zeta5 - 5 / 16 * π ^ 2 + zeta3 / 8 +
    7 / 720 * π ^ 4 + π ^ 2 * zeta3 / 3 := by
  rw [i8Psi4s66_eq_S]
  unfold i8Psi4s66S0 i8Psi4s66S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one,
    hpl_zero_one_at_one, hpl_zero_negOne_one_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_one_negOne_at_one, hpl_zero_zero_negOne_one_at_one, hpl_zero_zero_zero_negOne_at_one,
    hpl_zero_zero_one_negOne_at_one, hpl_zero_one_zero_negOne_at_one,
    hpl_zero_zero_zero_negOne_one_at_one, hpl_zero_zero_zero_one_negOne_at_one,
    hpl_zero_zero_one_zero_negOne_at_one, hpl_zero_one_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s67` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s67S0 (x : ℝ) : ℝ :=
    (3 * x ^ 4 + 16 * x) / x ^ 2 +
    (-6 * x ^ 4 + 16 * x) / x ^ 2 * hpl [zero] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 2 + 8 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-8) * hpl [zero, zero, zero] x

theorem continuousOn_i8Psi4s67S0 : ContinuousOn i8Psi4s67S0 (Ioc 0 1) := by
  unfold i8Psi4s67S0
  exact ((((i13_cont_coef (p := fun x => 3 * x ^ 4 + 16 * x) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -6 * x ^ 4 + 16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 2 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero])))

theorem i8Psi4s67_eq_S (x : ℝ) : i8Psi4s67 x = i8Psi4s67S0 x := by
  unfold i8Psi4s67 i8Psi4s67S0 i8Psi4s67N0 i8Psi4s67N1 i8Psi4s67N2 i8Psi4s67N3 i8Psi4s67N4
    i8Psi4s67W
  ring

theorem continuousOn_i8Psi4s67 : ContinuousOn i8Psi4s67 (Ioc 0 1) := by
  rw [show i8Psi4s67 = fun x => i8Psi4s67S0 x from funext i8Psi4s67_eq_S]
  exact continuousOn_i8Psi4s67S0

theorem i8Psi4s67_one : i8Psi4s67 1 = 19 := by
  rw [i8Psi4s67_eq_S]
  unfold i8Psi4s67S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one]
  norm_num

/-- Chunk 0 of `i8Psi4s68` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s68S0 (x : ℝ) : ℝ :=
    (-13 / 2 * x + 7 / 4 * x ^ 4 + 35 / 2 * x ^ 3) / x ^ 2 +
    (-3 / 2 - 13 * x ^ 2 - 8 * x - 8 * x ^ 3 - 3 / 2 * x ^ 4) / x ^ 2 * hpl [negOne] x +
    (-11 * x ^ 3 - 5 * x - 2 * x ^ 4 + 13 / 2 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (-3 - 8 * x + 3 * x ^ 4 + 8 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (-3 - 8 * x + 3 * x ^ 4 + 8 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (x ^ 4 - 2 * x + 5 * x ^ 2 + 6 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-2 - 8 * x - 8 * x ^ 2 - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-2 - 8 * x - 8 * x ^ 2 - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne] x +
    (6) * hpl [zero, zero, zero] x

theorem continuousOn_i8Psi4s68S0 : ContinuousOn i8Psi4s68S0 (Ioc 0 1) := by
  unfold i8Psi4s68S0
  exact ((((((((((i13_cont_coef (p := fun x => -13 / 2 * x + 7 / 4 * x ^ 4 +
    35 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -3 / 2 - 13 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        3 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -11 * x ^ 3 - 5 * x - 2 * x ^ 4 +
        13 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -3 - 8 * x + 3 * x ^ 4 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -3 - 8 * x + 3 * x ^ 4 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 2 * x + 5 * x ^ 2 + 6 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 8 * x - 8 * x ^ 2 - 8 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 8 * x - 8 * x ^ 2 - 8 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero])))

theorem i8Psi4s68_eq_S (x : ℝ) : i8Psi4s68 x = i8Psi4s68S0 x := by
  unfold i8Psi4s68 i8Psi4s68S0 i8Psi4s68N0 i8Psi4s68N1 i8Psi4s68N2 i8Psi4s68N3 i8Psi4s68N4
    i8Psi4s68W
  ring

theorem continuousOn_i8Psi4s68 : ContinuousOn i8Psi4s68 (Ioc 0 1) := by
  rw [show i8Psi4s68 = fun x => i8Psi4s68S0 x from funext i8Psi4s68_eq_S]
  exact continuousOn_i8Psi4s68S0

theorem i8Psi4s68_one : i8Psi4s68 1 = 51 / 4 - 32 * Real.log 2 - 3 * zeta3 := by
  rw [i8Psi4s68_eq_S]
  unfold i8Psi4s68S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s69` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s69S0 (x : ℝ) : ℝ :=
    (-173 / 4 * x ^ 3 - 19 / 4 * x - 3 / 2 * x ^ 4) / x ^ 2 +
    (-7 / 4 - 24 * x + 24 * x ^ 3 + 7 / 4 * x ^ 4) / x ^ 2 * hpl [negOne] x +
    (-3 * x + 21 * x ^ 3 + 5 / 4 * x ^ 4 + 89 / 4 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (-2 - 28 * x ^ 2 - 16 * x - 16 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-7 / 2 - 24 * x - 24 * x ^ 3 - 7 / 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne] x +
    (-x - 7 * x ^ 3 + 14 * x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [zero, zero] x +
    (-1 + x ^ 4 - 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-4 - 16 * x + 4 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-7 - 24 * x + 7 * x ^ 4 + 24 * x ^ 3) / x ^ 2 * hpl [zero, zero, negOne] x +
    (7) * hpl [zero, zero, zero] x +
    (-2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero, zero] x +
    (-4 - 16 * x - 16 * x ^ 3 - 8 * x ^ 2 - 4 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne, zero] x +
    (-6 - 24 * x - 24 * x ^ 3 - 16 * x ^ 2 - 6 * x ^ 4) / x ^ 2 * hpl [zero, zero, zero, negOne] x

theorem continuousOn_i8Psi4s69S0 : ContinuousOn i8Psi4s69S0 (Ioc 0 1) := by
  unfold i8Psi4s69S0
  exact (((((((((((((i13_cont_coef (p := fun x => -173 / 4 * x ^ 3 - 19 / 4 * x -
    3 / 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -7 / 4 - 24 * x + 24 * x ^ 3 +
        7 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -3 * x + 21 * x ^ 3 + 5 / 4 * x ^ 4 +
        89 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -2 - 28 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -7 / 2 - 24 * x - 24 * x ^ 3 -
        7 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -x - 7 * x ^ 3 + 14 * x ^ 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4 - 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 16 * x + 4 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -7 - 24 * x + 7 * x ^ 4 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 16 * x - 16 * x ^ 3 - 8 * x ^ 2 -
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -6 - 24 * x - 24 * x ^ 3 - 16 * x ^ 2 -
        6 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne])))

theorem i8Psi4s69_eq_S (x : ℝ) : i8Psi4s69 x = i8Psi4s69S0 x := by
  unfold i8Psi4s69 i8Psi4s69S0 i8Psi4s69N0 i8Psi4s69N1 i8Psi4s69N2 i8Psi4s69N3 i8Psi4s69N4
    i8Psi4s69W
  ring

theorem continuousOn_i8Psi4s69 : ContinuousOn i8Psi4s69 (Ioc 0 1) := by
  rw [show i8Psi4s69 = fun x => i8Psi4s69S0 x from funext i8Psi4s69_eq_S]
  exact continuousOn_i8Psi4s69S0

theorem i8Psi4s69_one : i8Psi4s69 1 = -99 / 2 + 3 / 4 * π ^ 2 + 7 / 90 * π ^ 4 := by
  rw [i8Psi4s69_eq_S]
  unfold i8Psi4s69S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s70` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s70S0 (x : ℝ) : ℝ :=
    (3 * x ^ 4 + 119 / 2 * x ^ 3) / x ^ 2 +
    (-35 * x ^ 3 + 13 * x - 37 / 2 * x ^ 2 - 7 / 2 * x ^ 4) / x ^ 2 * hpl [negOne] x +
    (-28 * x ^ 3 - 13 * x ^ 2 - 5 / 2 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (3 + 3 * x ^ 4 + 16 * x + 16 * x ^ 3 + 26 * x ^ 2) / x ^ 2 * hpl [negOne, negOne] x +
    (4 * x ^ 4 + 10 * x + 22 * x ^ 3 + 28 * x ^ 2) / x ^ 2 * hpl [negOne, zero] x +
    (-13 * x ^ 2 + 4 * x ^ 4 + 10 * x + 22 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (x ^ 4 - 10 * x ^ 2 + 10 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (6 - 16 * x ^ 3 - 6 * x ^ 4 + 16 * x) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (6 - 16 * x ^ 3 - 6 * x ^ 4 + 16 * x) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (-12 * x ^ 3 - 6 * x ^ 2 - 2 * x ^ 4 + 4 * x) / x ^ 2 * hpl [negOne, zero, zero] x +
    (6 - 16 * x ^ 3 - 6 * x ^ 4 + 16 * x) / x ^ 2 * hpl [zero, negOne, negOne] x +
    (-12 * x ^ 3 - 10 * x ^ 2 - 2 * x ^ 4 + 4 * x) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-12 * x ^ 3 - 10 * x ^ 2 - 2 * x ^ 4 + 4 * x) / x ^ 2 * hpl [zero, zero, negOne] x +
    (-4) * hpl [zero, zero, zero] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
      24 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero, zero] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
      24 * x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne, zero] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
      24 * x ^ 2) / x ^ 2 * hpl [negOne, zero, zero, negOne] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 2 +
      16 * x ^ 3) / x ^ 2 * hpl [zero, negOne, negOne, zero] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 2 +
      16 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero, negOne] x +
    (-12) * hpl [zero, negOne, zero, zero] x

theorem continuousOn_i8Psi4s70S0 : ContinuousOn i8Psi4s70S0 (Ioc 0 1) := by
  unfold i8Psi4s70S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => 3 * x ^ 4 +
    119 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -35 * x ^ 3 + 13 * x - 37 / 2 * x ^ 2 -
        7 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -28 * x ^ 3 - 13 * x ^ 2 - 5 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 3 + 3 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        26 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 10 * x + 22 * x ^ 3 +
        28 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -13 * x ^ 2 + 4 * x ^ 4 + 10 * x +
        22 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 10 * x ^ 2 + 10 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 6 - 16 * x ^ 3 - 6 * x ^ 4 + 16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 6 - 16 * x ^ 3 - 6 * x ^ 4 + 16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 6 * x ^ 2 - 2 * x ^ 4 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 6 - 16 * x ^ 3 - 6 * x ^ 4 + 16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 10 * x ^ 2 - 2 * x ^ 4 +
        4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 10 * x ^ 2 - 2 * x ^ 4 +
        4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 2 +
        16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 2 +
        16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero])))

/-- Chunk 1 of `i8Psi4s70` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s70S1 (x : ℝ) : ℝ :=
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 2 +
      16 * x ^ 3) / x ^ 2 * hpl [zero, zero, negOne, negOne] x +
    (-12) * hpl [zero, zero, negOne, zero] x +
    (-12) * hpl [zero, zero, zero, negOne] x

theorem continuousOn_i8Psi4s70S1 : ContinuousOn i8Psi4s70S1 (Ioc 0 1) := by
  unfold i8Psi4s70S1
  exact ((((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 2 +
    16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne])))

theorem i8Psi4s70_eq_S (x : ℝ) : i8Psi4s70 x = i8Psi4s70S0 x + i8Psi4s70S1 x := by
  unfold i8Psi4s70 i8Psi4s70S0 i8Psi4s70S1 i8Psi4s70N0 i8Psi4s70N1 i8Psi4s70N2 i8Psi4s70N3
    i8Psi4s70N4 i8Psi4s70W
  ring

theorem continuousOn_i8Psi4s70 : ContinuousOn i8Psi4s70 (Ioc 0 1) := by
  rw [show i8Psi4s70 = fun x => i8Psi4s70S0 x + i8Psi4s70S1 x from funext i8Psi4s70_eq_S]
  exact (continuousOn_i8Psi4s70S0.add continuousOn_i8Psi4s70S1)

theorem i8Psi4s70_one : i8Psi4s70 1 = 125 / 2 - 44 * Real.log 2 + 3 * zeta3 + 16 * Li 4 (1 / 2) +
    32 * Real.log 2 ^ 2 - 41 / 12 * π ^ 2 - 17 / 60 * π ^ 4 + 2 / 3 * Real.log 2 ^ 4 +
    14 * Real.log 2 * zeta3 - 2 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s70_eq_S]
  unfold i8Psi4s70S0 i8Psi4s70S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_negOne_at_one, hpl_negOne_zero_at_one,
    hpl_zero_negOne_at_one, hpl_zero_zero_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_negOne_zero_negOne_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_negOne_negOne_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one,
    hpl_negOne_negOne_zero_zero_at_one, hpl_negOne_zero_negOne_zero_at_one,
    hpl_negOne_zero_zero_negOne_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_zero_negOne_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_negOne_negOne_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s71` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s71S0 (x : ℝ) : ℝ :=
    (-14 * x ^ 3 - 6 * x ^ 4) / x ^ 2 +
    (-24 * x ^ 2 + 2 * x ^ 4 + 12 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (2 * x ^ 2 + 10 * x ^ 3 + 24 * x) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-8) * hpl [zero, zero] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 3 + 16 * x ^ 2) / x ^ 2 * hpl [zero, one] x +
    (-12 * x ^ 2 - 4 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-8) * hpl [zero, zero, one] x +
    (-8) * hpl [zero, one, zero] x

theorem continuousOn_i8Psi4s71S0 : ContinuousOn i8Psi4s71S0 (Ioc 0 1) := by
  unfold i8Psi4s71S0
  exact ((((((((i13_cont_coef (p := fun x => -14 * x ^ 3 - 6 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 + 2 * x ^ 4 + 12 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 2 + 10 * x ^ 3 + 24 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 3 + 16 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 4 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero])))

theorem i8Psi4s71_eq_S (x : ℝ) : i8Psi4s71 x = i8Psi4s71S0 x := by
  unfold i8Psi4s71 i8Psi4s71S0 i8Psi4s71N0 i8Psi4s71N1 i8Psi4s71N2 i8Psi4s71N3 i8Psi4s71N4
    i8Psi4s71W
  ring

theorem continuousOn_i8Psi4s71 : ContinuousOn i8Psi4s71 (Ioc 0 1) := by
  rw [show i8Psi4s71 = fun x => i8Psi4s71S0 x from funext i8Psi4s71_eq_S]
  exact continuousOn_i8Psi4s71S0

theorem i8Psi4s71_one : i8Psi4s71 1 = -20 + 6 * π ^ 2 + 8 * zeta3 := by
  rw [i8Psi4s71_eq_S]
  unfold i8Psi4s71S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_one_at_one,
    hpl_zero_one_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s72` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s72S0 (x : ℝ) : ℝ :=
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

theorem continuousOn_i8Psi4s72S0 : ContinuousOn i8Psi4s72S0 (Ioc 0 1) := by
  unfold i8Psi4s72S0
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

/-- Chunk 1 of `i8Psi4s72` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s72S1 (x : ℝ) : ℝ :=
    (-2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x)

theorem continuousOn_i8Psi4s72S1 : ContinuousOn i8Psi4s72S1 (Ioc 0 1) := by
  unfold i8Psi4s72S1
  exact ((i13_cont_coef (p := fun x => -2 - 10 * x + 2 * x ^ 3 + 10 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))

theorem i8Psi4s72_eq_S (x : ℝ) : i8Psi4s72 x = i8Psi4s72S0 x + i8Psi4s72S1 x := by
  unfold i8Psi4s72 i8Psi4s72S0 i8Psi4s72S1 i8Psi4s72N0 i8Psi4s72N1 i8Psi4s72N2 i8Psi4s72N3
    i8Psi4s72N4 i8Psi4s72W
  ring

theorem continuousOn_i8Psi4s72 : ContinuousOn i8Psi4s72 (Ioc 0 1) := by
  rw [show i8Psi4s72 = fun x => i8Psi4s72S0 x + i8Psi4s72S1 x from funext i8Psi4s72_eq_S]
  exact (continuousOn_i8Psi4s72S0.add continuousOn_i8Psi4s72S1)

theorem i8Psi4s72_one : i8Psi4s72 1 = -103 / 2 + 16 * zeta3 + 32 * Real.log 2 + 10 / 3 * π ^ 2 -
    8 * Real.log 2 * π ^ 2 := by
  rw [i8Psi4s72_eq_S]
  unfold i8Psi4s72S0 i8Psi4s72S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_negOne_one_at_one,
    hpl_zero_negOne_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_negOne_zero_one_at_one,
    hpl_negOne_one_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_negOne_one_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s73` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s73S0 (x : ℝ) : ℝ :=
    (-3 * x ^ 4 + 14 * x ^ 3) / x ^ 2 +
    (-4 * x ^ 2 + 4 * x ^ 4) / x ^ 2 * hpl [negOne] x +
    (-10 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-8 * x ^ 3 - 4 * x ^ 4 + 4 * x ^ 2 + 8 * x) / x ^ 2 * hpl [negOne, negOne] x +
    (-8 * x ^ 3 - 4 * x ^ 2 + 4 * x ^ 4 + 8 * x) / x ^ 2 * hpl [negOne, one] x +
    (-16) * hpl [zero, negOne] x +
    (-8) * hpl [zero, one] x +
    (-4 * x ^ 3 + 4 * x ^ 2 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (8 - 8 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, one] x +
    (8 - 8 * x ^ 4) / x ^ 2 * hpl [negOne, one, negOne] x +
    (-8) * hpl [zero, negOne, negOne] x +
    (8) * hpl [zero, negOne, one] x +
    (8) * hpl [zero, one, negOne] x +
    (8 + 8 * x + 8 * x ^ 2 + 8 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, negOne] x) +
    (32) * hpl [zero, negOne, negOne, one] x +
    (32) * hpl [zero, negOne, one, negOne] x +
    (32) * hpl [zero, one, negOne, negOne] x

theorem continuousOn_i8Psi4s73S0 : ContinuousOn i8Psi4s73S0 (Ioc 0 1) := by
  unfold i8Psi4s73S0
  exact (((((((((((((((((i13_cont_coef (p := fun x => -3 * x ^ 4 + 14 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 2 + 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -10 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 3 - 4 * x ^ 4 + 4 * x ^ 2 + 8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 3 - 4 * x ^ 2 + 4 * x ^ 4 + 8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 3 + 4 * x ^ 2 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => 8 - 8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, one]))).add
      ((i13_cont_coef (p := fun x => 8 - 8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      ((i13_cont_coef (p := fun x => 8 + 8 * x + 8 * x ^ 2 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, negOne])))

theorem i8Psi4s73_eq_S (x : ℝ) : i8Psi4s73 x = i8Psi4s73S0 x := by
  unfold i8Psi4s73 i8Psi4s73S0 i8Psi4s73N0 i8Psi4s73N1 i8Psi4s73N2 i8Psi4s73N3 i8Psi4s73N4
    i8Psi4s73W
  ring

theorem continuousOn_i8Psi4s73 : ContinuousOn i8Psi4s73 (Ioc 0 1) := by
  rw [show i8Psi4s73 = fun x => i8Psi4s73S0 x from funext i8Psi4s73_eq_S]
  exact continuousOn_i8Psi4s73S0

theorem i8Psi4s73_one : i8Psi4s73 1 = 11 + 4 * zeta3 - 8 / 3 * π ^ 2 + π ^ 4 / 15 := by
  rw [i8Psi4s73_eq_S]
  unfold i8Psi4s73S0
  rw [hpl_negOne_at_one, hpl_negOne_negOne_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one,
    hpl_zero_one_at_one, hpl_negOne_negOne_one_at_one, hpl_negOne_one_negOne_at_one,
    hpl_zero_negOne_negOne_at_one, hpl_zero_negOne_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_negOne_negOne_one_at_one, hpl_zero_negOne_one_negOne_at_one,
    hpl_zero_one_negOne_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s74k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s74k0S0 (x : ℝ) : ℝ :=
    (-x ^ 4 - 91 / 2 * x ^ 3) / x ^ 2 +
    (x ^ 4 / 2 + 13 * x ^ 3 + 25 / 2 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (x ^ 4 / 2 + 11 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (x ^ 3 + 22 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x ^ 4 + 4 * x + 12 * x ^ 3 + 15 * x ^ 2) / x ^ 2 * hpl [negOne, one] x +
    (-4) * hpl [zero, negOne] x +
    (x ^ 4 - 4 * x ^ 2 + 10 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-x ^ 3 - 13 * x ^ 2 + 4 * x) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (-x ^ 3 - 11 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-12 * x ^ 3 - 6 * x ^ 2 - 2 * x ^ 4 + 4 * x) / x ^ 2 * hpl [negOne, zero, one] x +
    (-12 * x ^ 3 - 6 * x ^ 2 - 2 * x ^ 4 + 4 * x) / x ^ 2 * hpl [negOne, one, zero] x +
    (-12 * x ^ 3 - 2 * x ^ 4 + 4 * x) / x ^ 2 * hpl [zero, negOne, one] x +
    (-4) * hpl [zero, zero, one] x +
    (-12 * x ^ 3 - 2 * x ^ 4 + 4 * x) / x ^ 2 * hpl [zero, one, negOne] x +
    (-4) * hpl [zero, one, zero] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero, one] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, one, zero] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne, one] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * hpl [negOne, zero, one, negOne] x +
    (-12) * hpl [zero, negOne, zero, one] x

theorem continuousOn_i8Psi4s74k0S0 : ContinuousOn i8Psi4s74k0S0 (Ioc 0 1) := by
  unfold i8Psi4s74k0S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -x ^ 4 - 91 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 13 * x ^ 3 + 25 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 11 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + 22 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 4 * x + 12 * x ^ 3 + 15 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 4 * x ^ 2 + 10 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 13 * x ^ 2 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 11 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 6 * x ^ 2 - 2 * x ^ 4 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 6 * x ^ 2 - 2 * x ^ 4 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 2 * x ^ 4 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 2 * x ^ 4 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, one]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, one, zero]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, one]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one])))

/-- Chunk 1 of `i8Psi4s74k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s74k0S1 (x : ℝ) : ℝ :=
    (-12) * hpl [zero, negOne, one, zero] x +
    (-12) * hpl [zero, zero, negOne, one] x +
    (-12) * hpl [zero, zero, one, negOne] x

theorem continuousOn_i8Psi4s74k0S1 : ContinuousOn i8Psi4s74k0S1 (Ioc 0 1) := by
  unfold i8Psi4s74k0S1
  exact (((continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne])))

theorem i8Psi4s74k0_eq_S (x : ℝ) : i8Psi4s74k0 x = i8Psi4s74k0S0 x + i8Psi4s74k0S1 x := by
  unfold i8Psi4s74k0 i8Psi4s74k0S0 i8Psi4s74k0S1 i8Psi4s74k0N0 i8Psi4s74k0N1 i8Psi4s74k0N2
    i8Psi4s74k0N3 i8Psi4s74k0N4 i8Psi4s74k0W
  ring

theorem continuousOn_i8Psi4s74k0 : ContinuousOn i8Psi4s74k0 (Ioc 0 1) := by
  rw [show i8Psi4s74k0 = fun x => i8Psi4s74k0S0 x + i8Psi4s74k0S1 x from funext i8Psi4s74k0_eq_S]
  exact (continuousOn_i8Psi4s74k0S0.add continuousOn_i8Psi4s74k0S1)

theorem i8Psi4s74k0_one : i8Psi4s74k0 1 = -93 / 2 - 16 * Real.log 2 ^ 2 + 26 * Real.log 2 +
    152 * Li 4 (1 / 2) - 115 / 72 * π ^ 4 + 7 / 2 * π ^ 2 + 19 / 3 * Real.log 2 ^ 4 +
    95 / 4 * zeta3 - 4 * Real.log 2 * π ^ 2 + 83 * Real.log 2 * zeta3 +
    5 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s74k0_eq_S]
  unfold i8Psi4s74k0S0 i8Psi4s74k0S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one,
    hpl_zero_one_at_one, hpl_negOne_zero_one_at_one, hpl_negOne_one_zero_at_one,
    hpl_zero_negOne_one_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_zero_at_one, hpl_negOne_negOne_zero_one_at_one, hpl_negOne_negOne_one_zero_at_one,
    hpl_negOne_zero_negOne_one_at_one, hpl_negOne_zero_one_negOne_at_one,
    hpl_zero_negOne_zero_one_at_one, hpl_zero_negOne_one_zero_at_one,
    hpl_zero_zero_negOne_one_at_one, hpl_zero_zero_one_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s74k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s74k1S0 (x : ℝ) : ℝ :=
    (-x ^ 4 - 109 / 2 * x ^ 3) / x ^ 2 +
    (x ^ 4 + 28 * x ^ 2 + 29 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (x ^ 4 / 2 + 13 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (x ^ 3 / 2 + 27 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-x ^ 4 - 14 * x ^ 3 - 13 * x ^ 2) / x ^ 2 * hpl [negOne, zero] x +
    (x ^ 4 + 2 * x + 14 * x ^ 3 + 15 * x ^ 2) / x ^ 2 * hpl [negOne, one] x +
    (-x ^ 4 - 14 * x ^ 3 - 2 * x ^ 2) / x ^ 2 * hpl [zero, negOne] x +
    (-2) * hpl [zero, one] x +
    (-x ^ 3 - 15 * x ^ 2 + 2 * x) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) / x ^ 2 * hpl [negOne, negOne, one] x +
    (2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) / x ^ 2 * hpl [negOne, one, negOne] x +
    (-4) * hpl [zero, negOne, zero] x +
    (-14) * hpl [zero, negOne, one] x +
    (-4) * hpl [zero, zero, negOne] x +
    (-14) * hpl [zero, one, negOne] x +
    (2 * x ^ 3 + 4 * x + 14 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (2 * x ^ 3 + 4 * x + 14 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * hpl [negOne, one, negOne, zero] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * hpl [negOne, one, zero, negOne] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3) / x ^ 2 * hpl [zero, negOne, negOne, one] x

theorem continuousOn_i8Psi4s74k1S0 : ContinuousOn i8Psi4s74k1S0 (Ioc 0 1) := by
  unfold i8Psi4s74k1S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -x ^ 4 -
    109 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 28 * x ^ 2 + 29 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 13 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 + 27 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 14 * x ^ 3 - 13 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 2 * x + 14 * x ^ 3 + 15 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 14 * x ^ 3 - 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 15 * x ^ 2 + 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, one]))).add
      ((i13_cont_coef (p := fun x => 2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 3 + 4 * x + 14 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 3 + 4 * x + 14 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, one])))

/-- Chunk 1 of `i8Psi4s74k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s74k1S1 (x : ℝ) : ℝ :=
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3) / x ^ 2 * hpl [zero, negOne, one, negOne] x +
    (-12) * hpl [zero, one, negOne, zero] x +
    (-12) * hpl [zero, one, zero, negOne] x

theorem continuousOn_i8Psi4s74k1S1 : ContinuousOn i8Psi4s74k1S1 (Ioc 0 1) := by
  unfold i8Psi4s74k1S1
  exact ((((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, negOne])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne])))

theorem i8Psi4s74k1_eq_S (x : ℝ) : i8Psi4s74k1 x = i8Psi4s74k1S0 x + i8Psi4s74k1S1 x := by
  unfold i8Psi4s74k1 i8Psi4s74k1S0 i8Psi4s74k1S1 i8Psi4s74k1N0 i8Psi4s74k1N1 i8Psi4s74k1N2
    i8Psi4s74k1N3 i8Psi4s74k1N4 i8Psi4s74k1W
  ring

theorem continuousOn_i8Psi4s74k1 : ContinuousOn i8Psi4s74k1 (Ioc 0 1) := by
  rw [show i8Psi4s74k1 = fun x => i8Psi4s74k1S0 x + i8Psi4s74k1S1 x from funext i8Psi4s74k1_eq_S]
  exact (continuousOn_i8Psi4s74k1S0.add continuousOn_i8Psi4s74k1S1)

theorem i8Psi4s74k1_one : i8Psi4s74k1 1 = -111 / 2 - 176 * Li 4 (1 / 2) - 16 * Real.log 2 ^ 2 +
    58 * Real.log 2 - 23 / 4 * zeta3 - 22 / 3 * Real.log 2 ^ 4 + 13 / 4 * π ^ 2 +
    343 / 180 * π ^ 4 - 125 * Real.log 2 * zeta3 + 7 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s74k1_eq_S]
  unfold i8Psi4s74k1S0 i8Psi4s74k1S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_negOne_one_at_one,
    hpl_zero_negOne_at_one, hpl_zero_one_at_one, hpl_negOne_negOne_one_at_one,
    hpl_negOne_one_negOne_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_negOne_one_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_one_negOne_at_one, hpl_negOne_one_negOne_zero_at_one,
    hpl_negOne_one_zero_negOne_at_one, hpl_zero_negOne_negOne_one_at_one,
    hpl_zero_negOne_one_negOne_at_one, hpl_zero_one_negOne_zero_at_one,
    hpl_zero_one_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s74k2` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s74k2S0 (x : ℝ) : ℝ :=
    (-x ^ 4 - 139 / 2 * x ^ 3) / x ^ 2 +
    (54 * x ^ 3 + 3 / 2 * x ^ 4 + 105 / 2 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (x ^ 4 / 2 + 17 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-38 * x ^ 3 - 30 * x ^ 2 - 2 * x ^ 4 + 6 * x) / x ^ 2 * hpl [negOne, negOne] x +
    (-x ^ 4 - 18 * x ^ 3 - 17 * x ^ 2) / x ^ 2 * hpl [negOne, zero] x +
    (-x ^ 4 - 18 * x ^ 3 - 6 * x ^ 2) / x ^ 2 * hpl [zero, negOne] x +
    (2 * x ^ 4 + 4 * x + 20 * x ^ 3 + 22 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (2 * x ^ 4 + 4 * x + 20 * x ^ 3 + 22 * x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (-18 * x ^ 2 + 2 * x ^ 4 + 4 * x + 20 * x ^ 3) / x ^ 2 * hpl [zero, negOne, negOne] x +
    (-4) * hpl [zero, negOne, zero] x +
    (-4) * hpl [zero, zero, negOne] x +
    (2 + 2 * x ^ 3 + 18 * x + 18 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, negOne] x) +
    (-20) * hpl [zero, negOne, negOne, zero] x +
    (-20) * hpl [zero, negOne, zero, negOne] x +
    (-20) * hpl [zero, zero, negOne, negOne] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3) / x ^ 2 * hpl [zero, one, negOne, negOne] x +
    (4 - 20 * x ^ 2 - 4 * x ^ 3 + 20 * x) / x ^ 2 * ((1 - x) * hpl [one, negOne, negOne, zero] x) +
    (4 - 20 * x ^ 2 - 4 * x ^ 3 + 20 * x) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero, negOne] x) +
    (4 - 20 * x ^ 2 - 4 * x ^ 3 + 20 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne, negOne] x)

theorem continuousOn_i8Psi4s74k2S0 : ContinuousOn i8Psi4s74k2S0 (Ioc 0 1) := by
  unfold i8Psi4s74k2S0
  exact (((((((((((((((((((i13_cont_coef (p := fun x => -x ^ 4 - 139 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 54 * x ^ 3 + 3 / 2 * x ^ 4 +
        105 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 17 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -38 * x ^ 3 - 30 * x ^ 2 - 2 * x ^ 4 +
        6 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 18 * x ^ 3 - 17 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 18 * x ^ 3 - 6 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 4 * x + 20 * x ^ 3 + 22 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 4 * x + 20 * x ^ 3 + 22 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -18 * x ^ 2 + 2 * x ^ 4 + 4 * x +
        20 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x ^ 3 + 18 * x + 18 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => 4 - 20 * x ^ 2 - 4 * x ^ 3 + 20 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 4 - 20 * x ^ 2 - 4 * x ^ 3 + 20 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 4 - 20 * x ^ 2 - 4 * x ^ 3 + 20 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne, negOne])))

theorem i8Psi4s74k2_eq_S (x : ℝ) : i8Psi4s74k2 x = i8Psi4s74k2S0 x := by
  unfold i8Psi4s74k2 i8Psi4s74k2S0 i8Psi4s74k2N0 i8Psi4s74k2N1 i8Psi4s74k2N2 i8Psi4s74k2N3
    i8Psi4s74k2N4 i8Psi4s74k2W
  ring

theorem continuousOn_i8Psi4s74k2 : ContinuousOn i8Psi4s74k2 (Ioc 0 1) := by
  rw [show i8Psi4s74k2 = fun x => i8Psi4s74k2S0 x from funext i8Psi4s74k2_eq_S]
  exact continuousOn_i8Psi4s74k2S0

theorem i8Psi4s74k2_one : i8Psi4s74k2 1 = -141 / 2 - 40 * Li 4 (1 / 2) - 32 * Real.log 2 ^ 2 -
    2 * zeta3 + 108 * Real.log 2 - 5 / 3 * Real.log 2 ^ 4 + 5 / 9 * π ^ 4 + 11 / 12 * π ^ 2 -
    70 * Real.log 2 * zeta3 + 20 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s74k2_eq_S]
  unfold i8Psi4s74k2S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_negOne_at_one, hpl_negOne_zero_at_one,
    hpl_zero_negOne_at_one, hpl_negOne_negOne_zero_at_one, hpl_negOne_zero_negOne_at_one,
    hpl_zero_negOne_negOne_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_negOne_negOne_zero_at_one, hpl_zero_negOne_zero_negOne_at_one,
    hpl_zero_zero_negOne_negOne_at_one, hpl_zero_one_negOne_negOne_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s74 : ContinuousOn i8Psi4s74 (Ioc 0 1) := by
  rw [show i8Psi4s74 = fun x => i8Psi4s74k0 x + i8Psi4s74k1 x + i8Psi4s74k2 x from rfl]
  exact ((continuousOn_i8Psi4s74k0.add continuousOn_i8Psi4s74k1).add continuousOn_i8Psi4s74k2)

theorem i8Psi4s74_one : i8Psi4s74 1 = -345 / 2 - 64 * Li 4 (1 / 2) - 64 * Real.log 2 ^ 2 +
    16 * zeta3 + 192 * Real.log 2 - 8 / 3 * Real.log 2 ^ 4 + 23 / 3 * π ^ 2 +
    311 / 360 * π ^ 4 - 112 * Real.log 2 * zeta3 - 4 * Real.log 2 * π ^ 2 +
    32 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  unfold i8Psi4s74
  rw [i8Psi4s74k0_one, i8Psi4s74k1_one, i8Psi4s74k2_one]
  ring

end QED.ThreeLoopD
