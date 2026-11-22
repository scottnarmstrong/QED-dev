/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4V9

/-!
# Set (d), master `I₈`: continuity and values at `1` of the sub-pieces 138 to 145 of `Ψ₄`

Each sub-piece `Ψ₄⁽ⁿ⁾` is continuous on `(0, 1]` (the words beginning with `1` carry a factor
`1 - ξ`), and its value at `ξ = 1` follows from the values of the harmonic polylogarithms at `1`.

## Main results

* `QED.ThreeLoopD.continuousOn_i8Psi4s138`, `QED.ThreeLoopD.i8Psi4s138_one` and their
  companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- Chunk 0 of `i8Psi4s138` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s138S0 (x : ℝ) : ℝ :=
    (-44 * x ^ 3 + 28 * x - 13 / 8 * x ^ 4) / x ^ 2 +
    (28 * x + 44 * x ^ 3 + 13 / 4 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (-44 * x ^ 3 + 28 * x - 13 / 2 * x ^ 4) / x ^ 2 * hpl [zero, zero] x +
    (4 * x ^ 2 + 9 * x ^ 4 + 24 * x + 48 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero] x +
    (-36 * x ^ 3 - 12 * x ^ 2 - 6 * x ^ 4 + 12 * x) / x ^ 2 * hpl [zero, zero, zero, zero] x +
    (-36) * hpl [zero, zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s138S0 : ContinuousOn i8Psi4s138S0 (Ioc 0 1) := by
  unfold i8Psi4s138S0
  exact ((((((i13_cont_coef (p := fun x => -44 * x ^ 3 + 28 * x - 13 / 8 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 28 * x + 44 * x ^ 3 + 13 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -44 * x ^ 3 + 28 * x - 13 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 2 + 9 * x ^ 4 + 24 * x + 48 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -36 * x ^ 3 - 12 * x ^ 2 - 6 * x ^ 4 +
        12 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, zero])))

theorem i8Psi4s138_eq_S (x : ℝ) : i8Psi4s138 x = i8Psi4s138S0 x := by
  unfold i8Psi4s138 i8Psi4s138S0 i8Psi4s138N0 i8Psi4s138N1 i8Psi4s138N2 i8Psi4s138N3 i8Psi4s138N4
    i8Psi4s138W
  ring

theorem continuousOn_i8Psi4s138 : ContinuousOn i8Psi4s138 (Ioc 0 1) := by
  rw [show i8Psi4s138 = fun x => i8Psi4s138S0 x from funext i8Psi4s138_eq_S]
  exact continuousOn_i8Psi4s138S0

theorem i8Psi4s138_one : i8Psi4s138 1 = -141 / 8 := by
  have h5 : hpl [zero, zero, zero, zero, zero] 1 = 0 := by
    rw [hpl_of_allZero (by decide)]
    simp
  rw [i8Psi4s138_eq_S]
  unfold i8Psi4s138S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_zero_zero_at_one, h5]
  norm_num

/-- Chunk 0 of `i8Psi4s139` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s139S0 (x : ℝ) : ℝ :=
    (13 / 2 * x ^ 4 + 829 / 4 * x ^ 3) / x ^ 2 +
    (-36 * x ^ 2 - 317 / 2 * x ^ 3 - 33 / 4 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (36 * x - 195 / 4 * x ^ 2 - 19 / 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-36 * x ^ 2 + 7 * x ^ 4 + 105 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-44 * x ^ 3 + 36 * x - 19 / 2 * x ^ 4) / x ^ 2 * hpl [zero, one] x +
    (36 * x + 19 / 2 * x ^ 3 + 107 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-42 * x ^ 3 - 28 * x ^ 2 - 3 * x ^ 4) / x ^ 2 * hpl [zero, zero, zero] x +
    (8 * x ^ 2 + 11 * x ^ 4 + 28 * x + 52 * x ^ 3) / x ^ 2 * hpl [zero, zero, one] x +
    (8 * x ^ 2 + 11 * x ^ 4 + 28 * x + 52 * x ^ 3) / x ^ 2 * hpl [zero, one, zero] x +
    (-63 * x ^ 2 - 11 * x ^ 3 + 28 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-12) * hpl [zero, zero, zero, zero] x +
    (-36 * x ^ 3 - 16 * x ^ 2 - 6 * x ^ 4 + 12 * x) / x ^ 2 * hpl [zero, zero, zero, one] x +
    (-36 * x ^ 3 - 16 * x ^ 2 - 6 * x ^ 4 + 12 * x) / x ^ 2 * hpl [zero, zero, one, zero] x +
    (-36 * x ^ 3 - 16 * x ^ 2 - 6 * x ^ 4 + 12 * x) / x ^ 2 * hpl [zero, one, zero, zero] x +
    (6 * x ^ 3 + 12 * x + 42 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, zero, zero] x) +
    (-36) * hpl [zero, zero, zero, zero, one] x +
    (-36) * hpl [zero, zero, zero, one, zero] x +
    (-36) * hpl [zero, zero, one, zero, zero] x +
    (-36) * hpl [zero, one, zero, zero, zero] x

theorem continuousOn_i8Psi4s139S0 : ContinuousOn i8Psi4s139S0 (Ioc 0 1) := by
  unfold i8Psi4s139S0
  exact (((((((((((((((((((i13_cont_coef (p := fun x => 13 / 2 * x ^ 4 +
    829 / 4 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -36 * x ^ 2 - 317 / 2 * x ^ 3 -
        33 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 36 * x - 195 / 4 * x ^ 2 - 19 / 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -36 * x ^ 2 + 7 * x ^ 4 + 105 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -44 * x ^ 3 + 36 * x - 19 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => 36 * x + 19 / 2 * x ^ 3 + 107 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -42 * x ^ 3 - 28 * x ^ 2 - 3 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 8 * x ^ 2 + 11 * x ^ 4 + 28 * x +
        52 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => 8 * x ^ 2 + 11 * x ^ 4 + 28 * x +
        52 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -63 * x ^ 2 - 11 * x ^ 3 + 28 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -36 * x ^ 3 - 16 * x ^ 2 - 6 * x ^ 4 +
        12 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      ((i13_cont_coef (p := fun x => -36 * x ^ 3 - 16 * x ^ 2 - 6 * x ^ 4 +
        12 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      ((i13_cont_coef (p := fun x => -36 * x ^ 3 - 16 * x ^ 2 - 6 * x ^ 4 +
        12 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 6 * x ^ 3 + 12 * x + 42 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero, zero])))

theorem i8Psi4s139_eq_S (x : ℝ) : i8Psi4s139 x = i8Psi4s139S0 x := by
  unfold i8Psi4s139 i8Psi4s139S0 i8Psi4s139N0 i8Psi4s139N1 i8Psi4s139N2 i8Psi4s139N3 i8Psi4s139N4
    i8Psi4s139W
  ring

theorem continuousOn_i8Psi4s139 : ContinuousOn i8Psi4s139 (Ioc 0 1) := by
  rw [show i8Psi4s139 = fun x => i8Psi4s139S0 x from funext i8Psi4s139_eq_S]
  exact continuousOn_i8Psi4s139S0

theorem i8Psi4s139_one : i8Psi4s139 1 = 855 / 4 - 99 * zeta3 + 36 * zeta5 - 35 / 12 * π ^ 2 -
    23 / 45 * π ^ 4 := by
  rw [i8Psi4s139_eq_S]
  unfold i8Psi4s139S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one, hpl_zero_zero_zero_zero_at_one,
    hpl_zero_zero_zero_one_at_one, hpl_zero_zero_one_zero_at_one, hpl_zero_one_zero_zero_at_one,
    hpl_zero_zero_zero_zero_one_at_one, hpl_zero_zero_zero_one_zero_at_one,
    hpl_zero_zero_one_zero_zero_at_one, hpl_zero_one_zero_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s140k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s140k0S0 (x : ℝ) : ℝ :=
    (-72 * x ^ 3 - 5 * x ^ 4) / x ^ 2 +
    (2 * x ^ 4 + 28 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (8 * x ^ 3 + 44 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-32 * x ^ 2 + 4 * x ^ 4 + 24 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-28 * x ^ 2 - 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (12 * x ^ 2 + 12 * x ^ 3 + 32 * x) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-16) * hpl [zero, zero, one] x +
    (-16) * hpl [zero, one, zero] x +
    (8 * x ^ 4 + 16 * x + 16 * x ^ 2 + 16 * x ^ 3) / x ^ 2 * hpl [zero, one, one] x +
    (-24 * x ^ 2 - 8 * x ^ 3 + 16 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, one] x) +
    (-24 * x ^ 2 - 8 * x ^ 3 + 16 * x) / x ^ 2 * ((1 - x) * hpl [one, one, zero] x) +
    (-16) * hpl [zero, zero, one, one] x +
    (-16) * hpl [zero, one, zero, one] x +
    (-16) * hpl [zero, one, one, zero] x

theorem continuousOn_i8Psi4s140k0S0 : ContinuousOn i8Psi4s140k0S0 (Ioc 0 1) := by
  unfold i8Psi4s140k0S0
  exact ((((((((((((((i13_cont_coef (p := fun x => -72 * x ^ 3 - 5 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 28 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 8 * x ^ 3 + 44 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -32 * x ^ 2 + 4 * x ^ 4 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -28 * x ^ 2 - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => 12 * x ^ 2 + 12 * x ^ 3 + 32 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => 8 * x ^ 4 + 16 * x + 16 * x ^ 2 +
        16 * x ^ 3) (by fun_prop)).mul
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

theorem i8Psi4s140k0_eq_S (x : ℝ) : i8Psi4s140k0 x = i8Psi4s140k0S0 x := by
  unfold i8Psi4s140k0 i8Psi4s140k0S0 i8Psi4s140k0N0 i8Psi4s140k0N1 i8Psi4s140k0N2 i8Psi4s140k0N3
    i8Psi4s140k0N4 i8Psi4s140k0W
  ring

theorem continuousOn_i8Psi4s140k0 : ContinuousOn i8Psi4s140k0 (Ioc 0 1) := by
  rw [show i8Psi4s140k0 = fun x => i8Psi4s140k0S0 x from funext i8Psi4s140k0_eq_S]
  exact continuousOn_i8Psi4s140k0S0

theorem i8Psi4s140k0_one : i8Psi4s140k0 1 = -77 + 72 * zeta3 - 2 / 3 * π ^ 2 + 2 / 45 * π ^ 4 := by
  rw [i8Psi4s140k0_eq_S]
  unfold i8Psi4s140k0S0
  rw [hpl_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one,
    hpl_zero_one_one_at_one, hpl_zero_zero_one_one_at_one, hpl_zero_one_zero_one_at_one,
    hpl_zero_one_one_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s140k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s140k1S0 (x : ℝ) : ℝ :=
    (-x ^ 4 - 215 / 2 * x ^ 3) / x ^ 2 +
    (x ^ 4 / 2 + 27 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (3 / 2 * x ^ 3 + 161 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-8 * x ^ 2 + 2 * x ^ 4 + 54 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-x ^ 3 - 27 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (x ^ 3 + 8 * x + 25 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-28 * x ^ 3 - 8 * x ^ 2 - 2 * x ^ 4) / x ^ 2 * hpl [zero, zero, one] x +
    (-8) * hpl [zero, one, zero] x +
    (2 * x ^ 4 + 8 * x + 24 * x ^ 3) / x ^ 2 * hpl [zero, one, one] x +
    (-26 * x ^ 2 - 2 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, one] x) +
    (-26 * x ^ 2 - 2 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, one, zero] x) +
    (-8) * hpl [zero, zero, zero, one] x +
    (-24 * x ^ 3 - 4 * x ^ 4 + 8 * x) / x ^ 2 * hpl [zero, zero, one, one] x +
    (-24 * x ^ 3 - 4 * x ^ 4 + 8 * x) / x ^ 2 * hpl [zero, one, zero, one] x +
    (-24 * x ^ 3 - 4 * x ^ 4 + 8 * x) / x ^ 2 * hpl [zero, one, one, zero] x +
    (4 * x ^ 3 + 8 * x + 28 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, zero, one] x) +
    (-24) * hpl [zero, zero, zero, one, one] x +
    (-24) * hpl [zero, zero, one, zero, one] x +
    (-24) * hpl [zero, zero, one, one, zero] x +
    (-24) * hpl [zero, one, zero, zero, one] x

theorem continuousOn_i8Psi4s140k1S0 : ContinuousOn i8Psi4s140k1S0 (Ioc 0 1) := by
  unfold i8Psi4s140k1S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -x ^ 4 -
    215 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 27 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 3 / 2 * x ^ 3 + 161 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 2 + 2 * x ^ 4 + 54 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 27 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + 8 * x + 25 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      ((i13_cont_coef (p := fun x => -28 * x ^ 3 - 8 * x ^ 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 8 * x + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -26 * x ^ 2 - 2 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -26 * x ^ 2 - 2 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 3 - 4 * x ^ 4 + 8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 3 - 4 * x ^ 4 + 8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 3 - 4 * x ^ 4 + 8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 3 + 8 * x + 28 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero, one])))

theorem i8Psi4s140k1_eq_S (x : ℝ) : i8Psi4s140k1 x = i8Psi4s140k1S0 x := by
  unfold i8Psi4s140k1 i8Psi4s140k1S0 i8Psi4s140k1N0 i8Psi4s140k1N1 i8Psi4s140k1N2 i8Psi4s140k1N3
    i8Psi4s140k1N4 i8Psi4s140k1W
  ring

theorem continuousOn_i8Psi4s140k1 : ContinuousOn i8Psi4s140k1 (Ioc 0 1) := by
  rw [show i8Psi4s140k1 = fun x => i8Psi4s140k1S0 x from funext i8Psi4s140k1_eq_S]
  exact continuousOn_i8Psi4s140k1S0

theorem i8Psi4s140k1_one : i8Psi4s140k1 1 = -217 / 2 - 12 * zeta5 + 8 * π ^ 2 + 12 * zeta3 -
    π ^ 4 / 30 := by
  rw [i8Psi4s140k1_eq_S]
  unfold i8Psi4s140k1S0
  rw [hpl_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one,
    hpl_zero_one_one_at_one, hpl_zero_zero_zero_one_at_one, hpl_zero_zero_one_one_at_one,
    hpl_zero_one_zero_one_at_one, hpl_zero_one_one_zero_at_one, hpl_zero_zero_zero_one_one_at_one,
    hpl_zero_zero_one_zero_one_at_one, hpl_zero_zero_one_one_zero_at_one,
    hpl_zero_one_zero_zero_one_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s140k2` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s140k2S0 (x : ℝ) : ℝ :=
    (-59 * x ^ 3 - x ^ 4 / 2) / x ^ 2 +
    (x ^ 4 + 59 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-x ^ 4 - 30 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-x ^ 3 - 29 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-28 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, one, zero] x +
    (2 * x ^ 3 + 30 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-8) * hpl [zero, zero, one, zero] x +
    (-8) * hpl [zero, one, zero, zero] x +
    (4 * x ^ 3 + 8 * x + 28 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, one, zero] x) +
    (4 * x ^ 3 + 8 * x + 28 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one, zero, zero] x) +
    (-24) * hpl [zero, one, zero, one, zero] x +
    (-24) * hpl [zero, one, one, zero, zero] x

theorem continuousOn_i8Psi4s140k2S0 : ContinuousOn i8Psi4s140k2S0 (Ioc 0 1) := by
  unfold i8Psi4s140k2S0
  exact ((((((((((((i13_cont_coef (p := fun x => -59 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 59 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 30 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 29 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -28 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 3 + 30 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 3 + 8 * x + 28 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 3 + 8 * x + 28 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero, zero])))

theorem i8Psi4s140k2_eq_S (x : ℝ) : i8Psi4s140k2 x = i8Psi4s140k2S0 x := by
  unfold i8Psi4s140k2 i8Psi4s140k2S0 i8Psi4s140k2N0 i8Psi4s140k2N1 i8Psi4s140k2N2 i8Psi4s140k2N3
    i8Psi4s140k2N4 i8Psi4s140k2W
  ring

theorem continuousOn_i8Psi4s140k2 : ContinuousOn i8Psi4s140k2 (Ioc 0 1) := by
  rw [show i8Psi4s140k2 = fun x => i8Psi4s140k2S0 x from funext i8Psi4s140k2_eq_S]
  exact continuousOn_i8Psi4s140k2S0

theorem i8Psi4s140k2_one : i8Psi4s140k2 1 = -119 / 2 - 36 * zeta5 + 60 * zeta3 +
    4 * π ^ 2 * zeta3 := by
  rw [i8Psi4s140k2_eq_S]
  unfold i8Psi4s140k2S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_zero_at_one,
    hpl_zero_zero_one_zero_at_one, hpl_zero_one_zero_zero_at_one, hpl_zero_one_zero_one_zero_at_one,
    hpl_zero_one_one_zero_zero_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s140 : ContinuousOn i8Psi4s140 (Ioc 0 1) := by
  rw [show i8Psi4s140 = fun x => i8Psi4s140k0 x + i8Psi4s140k1 x + i8Psi4s140k2 x from rfl]
  exact ((continuousOn_i8Psi4s140k0.add continuousOn_i8Psi4s140k1).add continuousOn_i8Psi4s140k2)

theorem i8Psi4s140_one : i8Psi4s140 1 = -245 - 48 * zeta5 + 144 * zeta3 + π ^ 4 / 90 +
    22 / 3 * π ^ 2 + 4 * π ^ 2 * zeta3 := by
  unfold i8Psi4s140
  rw [i8Psi4s140k0_one, i8Psi4s140k1_one, i8Psi4s140k2_one]
  ring

/-- Chunk 0 of `i8Psi4s141` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s141S0 (x : ℝ) : ℝ :=
    (x - x ^ 3 + x ^ 4 / 16) / x ^ 2 +
    (x + x ^ 3 - x ^ 4 / 8) / x ^ 2 * hpl [zero] x +
    (x - x ^ 3 + x ^ 4 / 4) / x ^ 2 * hpl [zero, zero] x +
    (x + x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero, zero, zero] x +
    (1) * hpl [zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s141S0 : ContinuousOn i8Psi4s141S0 (Ioc 0 1) := by
  unfold i8Psi4s141S0
  exact (((((i13_cont_coef (p := fun x => x - x ^ 3 + x ^ 4 / 16) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x + x ^ 3 - x ^ 4 / 8) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x - x ^ 3 + x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x + x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero])))

theorem i8Psi4s141_eq_S (x : ℝ) : i8Psi4s141 x = i8Psi4s141S0 x := by
  unfold i8Psi4s141 i8Psi4s141S0 i8Psi4s141N0 i8Psi4s141N1 i8Psi4s141N2 i8Psi4s141N3 i8Psi4s141N4
    i8Psi4s141W
  ring

theorem continuousOn_i8Psi4s141 : ContinuousOn i8Psi4s141 (Ioc 0 1) := by
  rw [show i8Psi4s141 = fun x => i8Psi4s141S0 x from funext i8Psi4s141_eq_S]
  exact continuousOn_i8Psi4s141S0

theorem i8Psi4s141_one : i8Psi4s141 1 = 1 / 16 := by
  rw [i8Psi4s141_eq_S]
  unfold i8Psi4s141S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_zero_zero_at_one]
  norm_num

/-- Chunk 0 of `i8Psi4s142` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s142S0 (x : ℝ) : ℝ :=
    (-15 / 16 * x - 15 / 16 * x ^ 3 + x ^ 4 / 8) / x ^ 2 +
    (-1 / 16 - x ^ 4 / 16 + x ^ 2 / 8) / x ^ 2 * hpl [negOne] x +
    (-7 / 8 * x - 3 / 16 * x ^ 4 - x ^ 2 / 16 + 7 / 8 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-1 / 8 + x ^ 4 / 8) / x ^ 2 * hpl [negOne, zero] x +
    (-1 / 8 + x ^ 4 / 8) / x ^ 2 * hpl [zero, negOne] x +
    (-3 / 4 * x - 3 / 4 * x ^ 3 - x ^ 2 / 8 + x ^ 4 / 4) / x ^ 2 * hpl [zero, zero] x +
    (-1 / 4 + x ^ 2 / 2 - x ^ 4 / 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-1 / 4 - x ^ 4 / 4) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-1 / 4 - x ^ 4 / 4) / x ^ 2 * hpl [zero, zero, negOne] x +
    (x ^ 3 / 2 - x / 2 - x ^ 2 / 4 - x ^ 4 / 4) / x ^ 2 * hpl [zero, zero, zero] x +
    (-1 / 2 + x ^ 4 / 2) / x ^ 2 * hpl [negOne, zero, zero, zero] x +
    (-1 / 2 + x ^ 4 / 2) / x ^ 2 * hpl [zero, negOne, zero, zero] x +
    (-1 / 2 + x ^ 4 / 2) / x ^ 2 * hpl [zero, zero, negOne, zero] x +
    (-1 / 2 + x ^ 4 / 2) / x ^ 2 * hpl [zero, zero, zero, negOne] x +
    (-1 / 2) * hpl [zero, zero, zero, zero] x +
    (-2) * hpl [zero, negOne, zero, zero, zero] x +
    (-2) * hpl [zero, zero, negOne, zero, zero] x +
    (-2) * hpl [zero, zero, zero, negOne, zero] x +
    (-2) * hpl [zero, zero, zero, zero, negOne] x

theorem continuousOn_i8Psi4s142S0 : ContinuousOn i8Psi4s142S0 (Ioc 0 1) := by
  unfold i8Psi4s142S0
  exact (((((((((((((((((((i13_cont_coef (p := fun x => -15 / 16 * x - 15 / 16 * x ^ 3 +
    x ^ 4 / 8) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -1 / 16 - x ^ 4 / 16 + x ^ 2 / 8) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -7 / 8 * x - 3 / 16 * x ^ 4 - x ^ 2 / 16 +
        7 / 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -1 / 8 + x ^ 4 / 8) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 8 + x ^ 4 / 8) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -3 / 4 * x - 3 / 4 * x ^ 3 - x ^ 2 / 8 +
        x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 4 + x ^ 2 / 2 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 4 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 4 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 - x / 2 - x ^ 2 / 4 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 4 / 2) (by fun_prop)).mul
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

theorem i8Psi4s142_eq_S (x : ℝ) : i8Psi4s142 x = i8Psi4s142S0 x := by
  unfold i8Psi4s142 i8Psi4s142S0 i8Psi4s142N0 i8Psi4s142N1 i8Psi4s142N2 i8Psi4s142N3 i8Psi4s142N4
    i8Psi4s142W
  ring

theorem continuousOn_i8Psi4s142 : ContinuousOn i8Psi4s142 (Ioc 0 1) := by
  rw [show i8Psi4s142 = fun x => i8Psi4s142S0 x from funext i8Psi4s142_eq_S]
  exact continuousOn_i8Psi4s142S0

theorem i8Psi4s142_one : i8Psi4s142 1 = -7 / 4 + 3 / 8 * zeta3 + 15 / 8 * zeta5 := by
  rw [i8Psi4s142_eq_S]
  unfold i8Psi4s142S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one, hpl_negOne_zero_zero_zero_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_negOne_at_one, hpl_zero_zero_zero_zero_at_one,
    hpl_zero_negOne_zero_zero_zero_at_one, hpl_zero_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s143` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s143S0 (x : ℝ) : ℝ :=
    (-3 / 8 * x ^ 4 + 17 / 4 * x ^ 3) / x ^ 2 +
    (x ^ 4 / 2 - 2 * x ^ 2 - 5 / 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (2 * x - 7 / 4 * x ^ 2 + x ^ 3 / 4) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x ^ 3 - 2 * x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [zero, zero] x +
    (x ^ 4 / 2 - 2 * x ^ 3 + 2 * x) / x ^ 2 * hpl [zero, one] x +
    (2 * x - x ^ 3 / 2 + 3 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-2) * hpl [zero, zero, zero] x +
    (-x ^ 4 + 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [zero, zero, one] x +
    (-x ^ 4 + 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [zero, one, zero] x +
    (x ^ 3 - x ^ 2 + 2 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (2) * hpl [zero, zero, zero, one] x +
    (2) * hpl [zero, zero, one, zero] x +
    (2) * hpl [zero, one, zero, zero] x

theorem continuousOn_i8Psi4s143S0 : ContinuousOn i8Psi4s143S0 (Ioc 0 1) := by
  unfold i8Psi4s143S0
  exact (((((((((((((i13_cont_coef (p := fun x => -3 / 8 * x ^ 4 +
    17 / 4 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - 2 * x ^ 2 - 5 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 2 * x - 7 / 4 * x ^ 2 + x ^ 3 / 4) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - 2 * x ^ 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - 2 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => 2 * x - x ^ 3 / 2 + 3 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 + 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 + 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - x ^ 2 + 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero])))

theorem i8Psi4s143_eq_S (x : ℝ) : i8Psi4s143 x = i8Psi4s143S0 x := by
  unfold i8Psi4s143 i8Psi4s143S0 i8Psi4s143N0 i8Psi4s143N1 i8Psi4s143N2 i8Psi4s143N3 i8Psi4s143N4
    i8Psi4s143W
  ring

theorem continuousOn_i8Psi4s143 : ContinuousOn i8Psi4s143 (Ioc 0 1) := by
  rw [show i8Psi4s143 = fun x => i8Psi4s143S0 x from funext i8Psi4s143_eq_S]
  exact continuousOn_i8Psi4s143S0

theorem i8Psi4s143_one : i8Psi4s143 1 = 31 / 8 - 3 * zeta3 + π ^ 2 / 12 + π ^ 4 / 45 := by
  rw [i8Psi4s143_eq_S]
  unfold i8Psi4s143S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one, hpl_zero_zero_zero_one_at_one,
    hpl_zero_zero_one_zero_at_one, hpl_zero_one_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s144k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s144k0S0 (x : ℝ) : ℝ :=
    (-x ^ 4 / 4 + 5 / 2 * x ^ 3) / x ^ 2 +
    (-5 / 4 * x ^ 3 + x ^ 4 / 4 + 3 / 2 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (-5 / 4 * x ^ 2 - 3 / 2 * x + x ^ 3 / 4) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x ^ 2 + x ^ 3 / 2 - x ^ 4 / 4) / x ^ 2 * hpl [zero, zero] x +
    (x ^ 4 / 2 - 3 / 2 * x - 3 / 2 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-x - x ^ 3 / 4 + 3 / 4 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-1 / 2 + x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [negOne, zero, one] x +
    (1) * hpl [zero, zero, zero] x +
    (x ^ 3 - x - x ^ 2 / 2 - x ^ 4 / 2) / x ^ 2 * hpl [zero, zero, one] x +
    (x ^ 3 - x - x ^ 4 / 2) / x ^ 2 * hpl [zero, one, zero] x +
    (x ^ 3 / 2 - x - x ^ 2 / 2) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (-1 + x ^ 4) / x ^ 2 * hpl [negOne, zero, zero, one] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [negOne, zero, one, zero] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [negOne, one, zero, zero] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [zero, negOne, zero, one] x +
    (-1) * hpl [zero, zero, zero, one] x +
    (-1) * hpl [zero, zero, one, zero] x +
    (-1) * hpl [zero, one, zero, zero] x +
    (-4) * hpl [zero, negOne, zero, zero, one] x +
    (-4) * hpl [zero, negOne, zero, one, zero] x

theorem continuousOn_i8Psi4s144k0S0 : ContinuousOn i8Psi4s144k0S0 (Ioc 0 1) := by
  unfold i8Psi4s144k0S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -x ^ 4 / 4 +
    5 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -5 / 4 * x ^ 3 + x ^ 4 / 4 + 3 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -5 / 4 * x ^ 2 - 3 / 2 * x + x ^ 3 / 4) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 + x ^ 3 / 2 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - 3 / 2 * x - 3 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -x - x ^ 3 / 4 + 3 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - x - x ^ 2 / 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - x - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 - x - x ^ 2 / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, one]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
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
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one, zero])))

/-- Chunk 1 of `i8Psi4s144k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s144k0S1 (x : ℝ) : ℝ :=
    (-4) * hpl [zero, negOne, one, zero, zero] x +
    (-4) * hpl [zero, zero, negOne, zero, one] x

theorem continuousOn_i8Psi4s144k0S1 : ContinuousOn i8Psi4s144k0S1 (Ioc 0 1) := by
  unfold i8Psi4s144k0S1
  exact ((continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero, zero])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, one])))

theorem i8Psi4s144k0_eq_S (x : ℝ) : i8Psi4s144k0 x = i8Psi4s144k0S0 x + i8Psi4s144k0S1 x := by
  unfold i8Psi4s144k0 i8Psi4s144k0S0 i8Psi4s144k0S1 i8Psi4s144k0N0 i8Psi4s144k0N1 i8Psi4s144k0N2
    i8Psi4s144k0N3 i8Psi4s144k0N4 i8Psi4s144k0W
  ring

theorem continuousOn_i8Psi4s144k0 : ContinuousOn i8Psi4s144k0 (Ioc 0 1) := by
  rw [show i8Psi4s144k0 = fun x => i8Psi4s144k0S0 x +
    i8Psi4s144k0S1 x from funext i8Psi4s144k0_eq_S]
  exact (continuousOn_i8Psi4s144k0S0.add continuousOn_i8Psi4s144k0S1)

theorem i8Psi4s144k0_one : i8Psi4s144k0 1 = 9 / 4 - 139 / 8 * zeta5 - 5 / 12 * π ^ 2 -
    π ^ 4 / 90 + Real.log 2 * π ^ 4 / 4 := by
  rw [i8Psi4s144k0_eq_S]
  unfold i8Psi4s144k0S0 i8Psi4s144k0S1
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_negOne_zero_one_at_one,
    hpl_zero_zero_zero_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one,
    hpl_negOne_zero_zero_one_at_one, hpl_negOne_zero_one_zero_at_one,
    hpl_negOne_one_zero_zero_at_one, hpl_zero_negOne_zero_one_at_one, hpl_zero_zero_zero_one_at_one,
    hpl_zero_zero_one_zero_at_one, hpl_zero_one_zero_zero_at_one,
    hpl_zero_negOne_zero_zero_one_at_one, hpl_zero_negOne_zero_one_zero_at_one,
    hpl_zero_negOne_one_zero_zero_at_one, hpl_zero_zero_negOne_zero_one_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s144k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s144k1S0 (x : ℝ) : ℝ :=
    (-x ^ 4 / 4) / x ^ 2 +
    (-x / 4 - x ^ 2 / 8 + x ^ 3 / 4 + x ^ 4 / 8) / x ^ 2 * hpl [negOne] x +
    (x ^ 2 / 2 + x ^ 4 / 4) / x ^ 2 * hpl [zero] x +
    (-x / 4 - x ^ 2 / 8 + x ^ 3 / 8) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-3 / 4 * x ^ 2 - x / 2 - x ^ 3 / 2 - x ^ 4 / 4) / x ^ 2 * hpl [negOne, zero] x +
    (-1 / 4 + x ^ 4 / 4) / x ^ 2 * hpl [negOne, one] x +
    (1 / 4) * hpl [zero, negOne] x +
    (1) * hpl [zero, zero] x +
    (-1 / 4) * hpl [zero, one] x +
    (-1 / 4 - x / 4 - x ^ 2 / 4 - x ^ 3 / 4) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (-x / 2 - x ^ 3 / 4 + x ^ 2 / 4) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-1 / 2 + x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [negOne, one, zero] x +
    (1 / 2) * hpl [zero, negOne, zero] x +
    (-1 / 2 - x ^ 4 / 2) / x ^ 2 * hpl [zero, negOne, one] x +
    (-1 / 2 - x ^ 4 / 2) / x ^ 2 * hpl [zero, one, negOne] x +
    (-1 / 2) * hpl [zero, one, zero] x +
    (-1 / 2 + x ^ 2 / 2 + x ^ 3 / 2 - x / 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (-1 + x ^ 4) / x ^ 2 * hpl [zero, negOne, one, zero] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [zero, zero, negOne, one] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [zero, zero, one, negOne] x

theorem continuousOn_i8Psi4s144k1S0 : ContinuousOn i8Psi4s144k1S0 (Ioc 0 1) := by
  unfold i8Psi4s144k1S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -x ^ 4 / 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -x / 4 - x ^ 2 / 8 + x ^ 3 / 4 + x ^ 4 / 8) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 2 / 2 + x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x / 4 - x ^ 2 / 8 + x ^ 3 / 8) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -3 / 4 * x ^ 2 - x / 2 - x ^ 3 / 2 -
        x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 4 + x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -1 / 4 - x / 4 - x ^ 2 / 4 - x ^ 3 / 4) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -x / 2 - x ^ 3 / 4 + x ^ 2 / 4) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 2 / 2 + x ^ 3 / 2 - x / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne])))

/-- Chunk 1 of `i8Psi4s144k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s144k1S1 (x : ℝ) : ℝ :=
    (-1 + x ^ 4) / x ^ 2 * hpl [zero, one, negOne, zero] x +
    (-4) * hpl [zero, zero, negOne, one, zero] x +
    (-4) * hpl [zero, zero, zero, negOne, one] x +
    (-4) * hpl [zero, zero, zero, one, negOne] x +
    (-4) * hpl [zero, zero, one, negOne, zero] x

theorem continuousOn_i8Psi4s144k1S1 : ContinuousOn i8Psi4s144k1S1 (Ioc 0 1) := by
  unfold i8Psi4s144k1S1
  exact ((((((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne, zero])))

theorem i8Psi4s144k1_eq_S (x : ℝ) : i8Psi4s144k1 x = i8Psi4s144k1S0 x + i8Psi4s144k1S1 x := by
  unfold i8Psi4s144k1 i8Psi4s144k1S0 i8Psi4s144k1S1 i8Psi4s144k1N0 i8Psi4s144k1N1 i8Psi4s144k1N2
    i8Psi4s144k1N3 i8Psi4s144k1N4 i8Psi4s144k1W
  ring

theorem continuousOn_i8Psi4s144k1 : ContinuousOn i8Psi4s144k1 (Ioc 0 1) := by
  rw [show i8Psi4s144k1 = fun x => i8Psi4s144k1S0 x +
    i8Psi4s144k1S1 x from funext i8Psi4s144k1_eq_S]
  exact (continuousOn_i8Psi4s144k1S0.add continuousOn_i8Psi4s144k1S1)

theorem i8Psi4s144k1_one : i8Psi4s144k1 1 = -1 / 4 - 59 / 8 * zeta5 - 3 / 8 * zeta3 +
    7 / 48 * π ^ 2 + 5 / 6 * π ^ 2 * zeta3 := by
  rw [i8Psi4s144k1_eq_S]
  unfold i8Psi4s144k1S0 i8Psi4s144k1S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_negOne_one_at_one,
    hpl_zero_negOne_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_negOne_one_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_negOne_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_zero_at_one, hpl_zero_negOne_one_zero_at_one, hpl_zero_zero_negOne_one_at_one,
    hpl_zero_zero_one_negOne_at_one, hpl_zero_one_negOne_zero_at_one,
    hpl_zero_zero_negOne_one_zero_at_one, hpl_zero_zero_zero_negOne_one_at_one,
    hpl_zero_zero_zero_one_negOne_at_one, hpl_zero_zero_one_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s144k2` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s144k2S0 (x : ℝ) : ℝ :=
    (-5 / 2 * x ^ 3 - x ^ 4 / 4) / x ^ 2 +
    (-3 / 2 * x - x ^ 2 / 4 + x ^ 4 / 4 + 3 / 2 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (x ^ 4 / 4 + 3 / 2 * x ^ 2 + 5 / 4 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-x - x ^ 3 - 7 / 4 * x ^ 2 - x ^ 4 / 4) / x ^ 2 * hpl [negOne, zero] x +
    (-3 / 2 * x - 3 / 2 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero, negOne] x +
    (x ^ 2 - x ^ 3 / 2 - x ^ 4 / 4) / x ^ 2 * hpl [zero, zero] x +
    (x ^ 3 + x ^ 4 / 2 - x - x ^ 2 / 2) / x ^ 2 * hpl [negOne, zero, zero] x +
    (x ^ 3 + x ^ 4 / 2 - x) / x ^ 2 * hpl [zero, negOne, zero] x +
    (x ^ 3 + x ^ 2 / 2 + x ^ 4 / 2 - x) / x ^ 2 * hpl [zero, zero, negOne] x +
    (1) * hpl [zero, zero, zero] x +
    (-1 / 2 + x ^ 2 / 2 + x ^ 3 / 2 - x / 2) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (1) * hpl [zero, negOne, zero, zero] x +
    (1) * hpl [zero, zero, negOne, zero] x +
    (1) * hpl [zero, zero, zero, negOne] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [zero, one, zero, negOne] x +
    (-1 - x - x ^ 2 - x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero, zero] x) +
    (-1 - x - x ^ 2 - x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne, zero] x) +
    (-1 - x - x ^ 2 - x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, zero, negOne] x) +
    (-4) * hpl [zero, zero, one, zero, negOne] x +
    (-4) * hpl [zero, one, negOne, zero, zero] x

theorem continuousOn_i8Psi4s144k2S0 : ContinuousOn i8Psi4s144k2S0 (Ioc 0 1) := by
  unfold i8Psi4s144k2S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -5 / 2 * x ^ 3 -
    x ^ 4 / 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -3 / 2 * x - x ^ 2 / 4 + x ^ 4 / 4 +
        3 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 4 + 3 / 2 * x ^ 2 + 5 / 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x - x ^ 3 - 7 / 4 * x ^ 2 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -3 / 2 * x - 3 / 2 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 - x ^ 3 / 2 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + x ^ 4 / 2 - x - x ^ 2 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + x ^ 4 / 2 - x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + x ^ 2 / 2 + x ^ 4 / 2 - x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 2 / 2 + x ^ 3 / 2 - x / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 - x - x ^ 2 - x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 - x - x ^ 2 - x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -1 - x - x ^ 2 - x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero, zero])))

/-- Chunk 1 of `i8Psi4s144k2` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s144k2S1 (x : ℝ) : ℝ :=
    (-4) * hpl [zero, one, zero, negOne, zero] x +
    (-4) * hpl [zero, one, zero, zero, negOne] x

theorem continuousOn_i8Psi4s144k2S1 : ContinuousOn i8Psi4s144k2S1 (Ioc 0 1) := by
  unfold i8Psi4s144k2S1
  exact ((continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne, zero])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero, negOne])))

theorem i8Psi4s144k2_eq_S (x : ℝ) : i8Psi4s144k2 x = i8Psi4s144k2S0 x + i8Psi4s144k2S1 x := by
  unfold i8Psi4s144k2 i8Psi4s144k2S0 i8Psi4s144k2S1 i8Psi4s144k2N0 i8Psi4s144k2N1 i8Psi4s144k2N2
    i8Psi4s144k2N3 i8Psi4s144k2N4 i8Psi4s144k2W
  ring

theorem continuousOn_i8Psi4s144k2 : ContinuousOn i8Psi4s144k2 (Ioc 0 1) := by
  rw [show i8Psi4s144k2 = fun x => i8Psi4s144k2S0 x +
    i8Psi4s144k2S1 x from funext i8Psi4s144k2_eq_S]
  exact (continuousOn_i8Psi4s144k2S0.add continuousOn_i8Psi4s144k2S1)

theorem i8Psi4s144k2_one : i8Psi4s144k2 1 = -11 / 4 + π ^ 2 / 24 + 7 / 720 * π ^ 4 +
    171 / 8 * zeta5 - 7 / 12 * π ^ 2 * zeta3 - Real.log 2 * π ^ 4 / 4 := by
  rw [i8Psi4s144k2_eq_S]
  unfold i8Psi4s144k2S0 i8Psi4s144k2S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_at_one,
    hpl_zero_one_zero_negOne_at_one, hpl_zero_zero_one_zero_negOne_at_one,
    hpl_zero_one_negOne_zero_zero_at_one, hpl_zero_one_zero_negOne_zero_at_one,
    hpl_zero_one_zero_zero_negOne_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s144 : ContinuousOn i8Psi4s144 (Ioc 0 1) := by
  rw [show i8Psi4s144 = fun x => i8Psi4s144k0 x + i8Psi4s144k1 x + i8Psi4s144k2 x from rfl]
  exact ((continuousOn_i8Psi4s144k0.add continuousOn_i8Psi4s144k1).add continuousOn_i8Psi4s144k2)

theorem i8Psi4s144_one : i8Psi4s144 1 = -3 / 4 - 27 / 8 * zeta5 - 11 / 48 * π ^ 2 -
    3 / 8 * zeta3 - π ^ 4 / 720 + π ^ 2 * zeta3 / 4 := by
  unfold i8Psi4s144
  rw [i8Psi4s144k0_one, i8Psi4s144k1_one, i8Psi4s144k2_one]
  ring

/-- Chunk 0 of `i8Psi4s145` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s145S0 (x : ℝ) : ℝ :=
    (-5 * x ^ 3 + 3 / 4 * x ^ 4) / x ^ 2 +
    (x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero] x +
    (-x ^ 3 + 4 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-x ^ 4 - 4 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (x ^ 3 - x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-x ^ 3 + 3 * x ^ 2 + 4 * x) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-4) * hpl [zero, zero, one] x +
    (-4) * hpl [zero, one, zero] x +
    (-2 * x ^ 4 + 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [zero, one, one] x +
    (-2 * x ^ 2 + 2 * x ^ 3 + 4 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, one] x) +
    (-2 * x ^ 2 + 2 * x ^ 3 + 4 * x) / x ^ 2 * ((1 - x) * hpl [one, one, zero] x) +
    (4) * hpl [zero, zero, one, one] x +
    (4) * hpl [zero, one, zero, one] x +
    (4) * hpl [zero, one, one, zero] x

theorem continuousOn_i8Psi4s145S0 : ContinuousOn i8Psi4s145S0 (Ioc 0 1) := by
  unfold i8Psi4s145S0
  exact ((((((((((((((i13_cont_coef (p := fun x => -5 * x ^ 3 + 3 / 4 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 + 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 4 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 + 3 * x ^ 2 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 4 + 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 2 + 2 * x ^ 3 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 2 + 2 * x ^ 3 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero])))

theorem i8Psi4s145_eq_S (x : ℝ) : i8Psi4s145 x = i8Psi4s145S0 x := by
  unfold i8Psi4s145 i8Psi4s145S0 i8Psi4s145N0 i8Psi4s145N1 i8Psi4s145N2 i8Psi4s145N3 i8Psi4s145N4
    i8Psi4s145W
  ring

theorem continuousOn_i8Psi4s145 : ContinuousOn i8Psi4s145 (Ioc 0 1) := by
  rw [show i8Psi4s145 = fun x => i8Psi4s145S0 x from funext i8Psi4s145_eq_S]
  exact continuousOn_i8Psi4s145S0

theorem i8Psi4s145_one : i8Psi4s145 1 = -17 / 4 + 10 * zeta3 - π ^ 2 / 2 - π ^ 4 / 90 := by
  rw [i8Psi4s145_eq_S]
  unfold i8Psi4s145S0
  rw [hpl_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one,
    hpl_zero_one_one_at_one, hpl_zero_zero_one_one_at_one, hpl_zero_one_zero_one_at_one,
    hpl_zero_one_one_zero_at_one]
  norm_num
  ring

end QED.ThreeLoopD
