/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4V1

/-!
# Set (d), master `I₈`: continuity and values at `1` of the sub-pieces 42 to 62 of `Ψ₄`

Each sub-piece `Ψ₄⁽ⁿ⁾` is continuous on `(0, 1]` (the words beginning with `1` carry a factor
`1 - ξ`), and its value at `ξ = 1` follows from the values of the harmonic polylogarithms at `1`.

## Main results

* `QED.ThreeLoopD.continuousOn_i8Psi4s42`, `QED.ThreeLoopD.i8Psi4s42_one` and their
  companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- Chunk 0 of `i8Psi4s42` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s42S0 (x : ℝ) : ℝ :=
    (-64 * x ^ 3 - 6 * x ^ 4 + 32 * x - 4 / 3 * π ^ 2 * x + π ^ 2 * x ^ 4 / 4 +
      8 / 3 * π ^ 2 * x ^ 3) / x ^ 2 +
    (12 * x ^ 4 + 32 * x + 64 * x ^ 3 - 8 / 3 * π ^ 2 * x ^ 3 - 4 / 3 * π ^ 2 * x -
      π ^ 2 * x ^ 4 / 2) / x ^ 2 * hpl [zero] x +
    (-48 * x ^ 3 - 16 * x ^ 2 - 8 * x ^ 4 + 16 * x + 2 * π ^ 2 * x ^ 3 - 2 / 3 * π ^ 2 * x +
      π ^ 2 * x ^ 4 / 3 + 2 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, zero] x +
    (-48 + 2 * π ^ 2) * hpl [zero, zero, zero] x

theorem continuousOn_i8Psi4s42S0 : ContinuousOn i8Psi4s42S0 (Ioc 0 1) := by
  unfold i8Psi4s42S0
  exact ((((i13_cont_coef (p := fun x => -64 * x ^ 3 - 6 * x ^ 4 + 32 * x - 4 / 3 * π ^ 2 * x +
    π ^ 2 * x ^ 4 / 4 + 8 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 12 * x ^ 4 + 32 * x + 64 * x ^ 3 - 8 / 3 * π ^ 2 * x ^ 3 -
        4 / 3 * π ^ 2 * x - π ^ 2 * x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -48 * x ^ 3 - 16 * x ^ 2 - 8 * x ^ 4 + 16 * x +
        2 * π ^ 2 * x ^ 3 - 2 / 3 * π ^ 2 * x + π ^ 2 * x ^ 4 / 3 +
        2 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero])))

theorem i8Psi4s42_eq_S (x : ℝ) : i8Psi4s42 x = i8Psi4s42S0 x := by
  unfold i8Psi4s42 i8Psi4s42S0 i8Psi4s42N0 i8Psi4s42N1 i8Psi4s42N2 i8Psi4s42N3 i8Psi4s42N4
    i8Psi4s42W
  ring

theorem continuousOn_i8Psi4s42 : ContinuousOn i8Psi4s42 (Ioc 0 1) := by
  rw [show i8Psi4s42 = fun x => i8Psi4s42S0 x from funext i8Psi4s42_eq_S]
  exact continuousOn_i8Psi4s42S0

theorem i8Psi4s42_one : i8Psi4s42 1 = -38 + 19 / 12 * π ^ 2 := by
  rw [i8Psi4s42_eq_S]
  unfold i8Psi4s42S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s43` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s43S0 (x : ℝ) : ℝ :=
    (-25 / 6 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 2) / x ^ 2 +
    (2 * π ^ 2 * x + 5 / 6 * π ^ 2 * x ^ 4 + 9 / 2 * π ^ 2 * x ^ 2 +
      10 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (-2 * π ^ 2 * x ^ 2 + π ^ 2 * x ^ 4 / 6 + 5 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-π ^ 2 * x ^ 2 - 2 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 3 +
      2 / 3 * π ^ 2 * x) / x ^ 2 * hpl [negOne, zero] x +
    (-2 * π ^ 2 * x ^ 3 - 4 / 3 * π ^ 2 * x ^ 2 - π ^ 2 * x ^ 4 / 3 +
      2 / 3 * π ^ 2 * x) / x ^ 2 * hpl [zero, negOne] x +
    (-2 / 3 * π ^ 2) * hpl [zero, zero] x +
    (-2 * π ^ 2) * hpl [zero, negOne, zero] x +
    (-2 * π ^ 2) * hpl [zero, zero, negOne] x

theorem continuousOn_i8Psi4s43S0 : ContinuousOn i8Psi4s43S0 (Ioc 0 1) := by
  unfold i8Psi4s43S0
  exact ((((((((i13_cont_coef (p := fun x => -25 / 6 * π ^ 2 * x ^ 3 -
    π ^ 2 * x ^ 4 / 2) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 2 * π ^ 2 * x + 5 / 6 * π ^ 2 * x ^ 4 +
        9 / 2 * π ^ 2 * x ^ 2 + 10 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -2 * π ^ 2 * x ^ 2 + π ^ 2 * x ^ 4 / 6 +
        5 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -π ^ 2 * x ^ 2 - 2 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 3 +
        2 / 3 * π ^ 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -2 * π ^ 2 * x ^ 3 - 4 / 3 * π ^ 2 * x ^ 2 -
        π ^ 2 * x ^ 4 / 3 + 2 / 3 * π ^ 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne])))

theorem i8Psi4s43_eq_S (x : ℝ) : i8Psi4s43 x = i8Psi4s43S0 x := by
  unfold i8Psi4s43 i8Psi4s43S0 i8Psi4s43N0 i8Psi4s43N1 i8Psi4s43N2 i8Psi4s43N3 i8Psi4s43N4
    i8Psi4s43W
  ring

theorem continuousOn_i8Psi4s43 : ContinuousOn i8Psi4s43 (Ioc 0 1) := by
  rw [show i8Psi4s43 = fun x => i8Psi4s43S0 x from funext i8Psi4s43_eq_S]
  exact continuousOn_i8Psi4s43S0

theorem i8Psi4s43_one : i8Psi4s43 1 = -14 / 3 * π ^ 2 - π ^ 4 / 36 + 3 / 2 * π ^ 2 * zeta3 +
    32 / 3 * Real.log 2 * π ^ 2 := by
  rw [i8Psi4s43_eq_S]
  unfold i8Psi4s43S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s44` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s44S0 (x : ℝ) : ℝ :=
    (x ^ 4 + 51 * x ^ 3) / x ^ 2 +
    (-51 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (-16 * x + 3 * x ^ 4 + 13 * x ^ 2 + 32 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (x ^ 4 + 16 * x ^ 2 + 22 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-30 * x ^ 2 - 24 * x ^ 3 - 8 * x - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-32 * x ^ 3 - 16 * x - 6 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero] x +
    (8) * hpl [zero, zero, zero] x +
    (-8 * x + 4 * x ^ 4 + 24 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero, zero] x +
    (-8 * x + 4 * x ^ 4 + 8 * x ^ 2 + 24 * x ^ 3) / x ^ 2 * hpl [zero, zero, negOne, zero] x +
    (24) * hpl [zero, zero, negOne, zero, zero] x +
    (24) * hpl [zero, zero, zero, negOne, zero] x

theorem continuousOn_i8Psi4s44S0 : ContinuousOn i8Psi4s44S0 (Ioc 0 1) := by
  unfold i8Psi4s44S0
  exact (((((((((((i13_cont_coef (p := fun x => x ^ 4 + 51 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -51 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -16 * x + 3 * x ^ 4 + 13 * x ^ 2 +
        32 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 16 * x ^ 2 + 22 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -30 * x ^ 2 - 24 * x ^ 3 - 8 * x -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -32 * x ^ 3 - 16 * x - 6 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x + 4 * x ^ 4 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x + 4 * x ^ 4 + 8 * x ^ 2 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne, zero])))

theorem i8Psi4s44_eq_S (x : ℝ) : i8Psi4s44 x = i8Psi4s44S0 x := by
  unfold i8Psi4s44 i8Psi4s44S0 i8Psi4s44N0 i8Psi4s44N1 i8Psi4s44N2 i8Psi4s44N3 i8Psi4s44N4
    i8Psi4s44W
  ring

theorem continuousOn_i8Psi4s44 : ContinuousOn i8Psi4s44 (Ioc 0 1) := by
  rw [show i8Psi4s44 = fun x => i8Psi4s44S0 x from funext i8Psi4s44_eq_S]
  exact continuousOn_i8Psi4s44S0

theorem i8Psi4s44_one : i8Psi4s44 1 = 52 + 33 * zeta3 + 45 * zeta5 - 8 / 3 * π ^ 2 -
    7 / 30 * π ^ 4 := by
  rw [i8Psi4s44_eq_S]
  unfold i8Psi4s44S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_zero_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s45` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s45S0 (x : ℝ) : ℝ :=
    (-80 * x ^ 3 - 2 * x ^ 4) / x ^ 2 +
    (4 * x ^ 4 + 80 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-50 * x ^ 3 - 44 * x ^ 2 - 6 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-36 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, zero] x +
    (10 * x ^ 4 + 24 * x + 40 * x ^ 3 + 54 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (4 * x ^ 4 + 36 * x ^ 2 + 40 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-24 * x ^ 2 + 2 * x ^ 4 + 20 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-48 * x ^ 3 - 24 * x ^ 2 - 8 * x ^ 4 + 16 * x) / x ^ 2 * hpl [negOne, negOne, zero, zero] x +
    (-24 * x ^ 3 - 12 * x ^ 2 - 4 * x ^ 4 + 8 * x) / x ^ 2 * hpl [negOne, zero, negOne, zero] x +
    (-24 * x ^ 3 - 16 * x ^ 2 - 4 * x ^ 4 + 8 * x) / x ^ 2 * hpl [zero, negOne, negOne, zero] x +
    (-16) * hpl [zero, negOne, zero, zero] x +
    (-8) * hpl [zero, zero, negOne, zero] x +
    (-48) * hpl [zero, negOne, negOne, zero, zero] x +
    (-24) * hpl [zero, negOne, zero, negOne, zero] x +
    (-24) * hpl [zero, zero, negOne, negOne, zero] x

theorem continuousOn_i8Psi4s45S0 : ContinuousOn i8Psi4s45S0 (Ioc 0 1) := by
  unfold i8Psi4s45S0
  exact (((((((((((((((i13_cont_coef (p := fun x => -80 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 80 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -50 * x ^ 3 - 44 * x ^ 2 - 6 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -36 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 10 * x ^ 4 + 24 * x + 40 * x ^ 3 +
        54 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 36 * x ^ 2 + 40 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 + 2 * x ^ 4 + 20 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -48 * x ^ 3 - 24 * x ^ 2 - 8 * x ^ 4 +
        16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 3 - 12 * x ^ 2 - 4 * x ^ 4 +
        8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 3 - 16 * x ^ 2 - 4 * x ^ 4 +
        8 * x) (by fun_prop)).mul
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

theorem i8Psi4s45_eq_S (x : ℝ) : i8Psi4s45 x = i8Psi4s45S0 x := by
  unfold i8Psi4s45 i8Psi4s45S0 i8Psi4s45N0 i8Psi4s45N1 i8Psi4s45N2 i8Psi4s45N3 i8Psi4s45N4
    i8Psi4s45W
  ring

theorem continuousOn_i8Psi4s45 : ContinuousOn i8Psi4s45 (Ioc 0 1) := by
  rw [show i8Psi4s45 = fun x => i8Psi4s45S0 x from funext i8Psi4s45_eq_S]
  exact continuousOn_i8Psi4s45S0

theorem i8Psi4s45_one : i8Psi4s45 1 = -82 + 79 * zeta3 - 79 / 360 * π ^ 4 + 25 / 3 * π ^ 2 +
    69 / 2 * zeta5 - 32 / 3 * Real.log 2 * π ^ 2 - 7 / 2 * π ^ 2 * zeta3 := by
  rw [i8Psi4s45_eq_S]
  unfold i8Psi4s45S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_negOne_negOne_zero_zero_at_one,
    hpl_negOne_zero_negOne_zero_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_negOne_negOne_zero_zero_at_one, hpl_zero_negOne_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s46` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s46S0 (x : ℝ) : ℝ :=
    (-28 * x ^ 3 + 12 * x - x ^ 4 / 2) / x ^ 2 +
    (x ^ 4 + 12 * x + 28 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-28 * x ^ 3 - 2 * x ^ 4 + 12 * x) / x ^ 2 * hpl [zero, zero] x +
    (4 * x ^ 4 + 12 * x + 28 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero] x +
    (-24 * x ^ 3 - 4 * x ^ 2 - 4 * x ^ 4 + 8 * x) / x ^ 2 * hpl [zero, zero, zero, zero] x +
    (-24) * hpl [zero, zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s46S0 : ContinuousOn i8Psi4s46S0 (Ioc 0 1) := by
  unfold i8Psi4s46S0
  exact ((((((i13_cont_coef (p := fun x => -28 * x ^ 3 + 12 * x - x ^ 4 / 2) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 12 * x + 28 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -28 * x ^ 3 - 2 * x ^ 4 + 12 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 12 * x + 28 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 3 - 4 * x ^ 2 - 4 * x ^ 4 + 8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, zero])))

theorem i8Psi4s46_eq_S (x : ℝ) : i8Psi4s46 x = i8Psi4s46S0 x := by
  unfold i8Psi4s46 i8Psi4s46S0 i8Psi4s46N0 i8Psi4s46N1 i8Psi4s46N2 i8Psi4s46N3 i8Psi4s46N4
    i8Psi4s46W
  ring

theorem continuousOn_i8Psi4s46 : ContinuousOn i8Psi4s46 (Ioc 0 1) := by
  rw [show i8Psi4s46 = fun x => i8Psi4s46S0 x from funext i8Psi4s46_eq_S]
  exact continuousOn_i8Psi4s46S0

theorem i8Psi4s46_one : i8Psi4s46 1 = -33 / 2 := by
  have h5 : hpl [zero, zero, zero, zero, zero] 1 = 0 := by
    rw [hpl_of_allZero (by decide)]
    simp
  rw [i8Psi4s46_eq_S]
  unfold i8Psi4s46S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_zero_zero_at_one, h5]
  norm_num

/-- Chunk 0 of `i8Psi4s47` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s47S0 (x : ℝ) : ℝ :=
    (x ^ 4 + 45 * x ^ 3) / x ^ 2 +
    (-45 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (4 * x ^ 4 + 45 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-27 * x ^ 2 - 20 * x ^ 3 - 12 * x - 5 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-30 * x ^ 3 - 3 * x ^ 4 + 12 * x ^ 2) / x ^ 2 * hpl [zero, zero, zero] x +
    (-12 * x + 6 * x ^ 4 + 18 * x ^ 2 + 36 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero, zero] x +
    (-4 * x + 2 * x ^ 4 + 8 * x ^ 2 + 12 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero, zero] x +
    (12) * hpl [zero, zero, zero, zero] x +
    (36) * hpl [zero, negOne, zero, zero, zero] x +
    (12) * hpl [zero, zero, negOne, zero, zero] x

theorem continuousOn_i8Psi4s47S0 : ContinuousOn i8Psi4s47S0 (Ioc 0 1) := by
  unfold i8Psi4s47S0
  exact ((((((((((i13_cont_coef (p := fun x => x ^ 4 + 45 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -45 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 45 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -27 * x ^ 2 - 20 * x ^ 3 - 12 * x -
        5 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -30 * x ^ 3 - 3 * x ^ 4 + 12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x + 6 * x ^ 4 + 18 * x ^ 2 +
        36 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x + 2 * x ^ 4 + 8 * x ^ 2 + 12 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, zero])))

theorem i8Psi4s47_eq_S (x : ℝ) : i8Psi4s47 x = i8Psi4s47S0 x := by
  unfold i8Psi4s47 i8Psi4s47S0 i8Psi4s47N0 i8Psi4s47N1 i8Psi4s47N2 i8Psi4s47N3 i8Psi4s47N4
    i8Psi4s47W
  ring

theorem continuousOn_i8Psi4s47 : ContinuousOn i8Psi4s47 (Ioc 0 1) := by
  rw [show i8Psi4s47 = fun x => i8Psi4s47S0 x from funext i8Psi4s47_eq_S]
  exact continuousOn_i8Psi4s47S0

theorem i8Psi4s47_one : i8Psi4s47 1 = 46 - 48 * zeta3 - 135 / 2 * zeta5 + 7 / 120 * π ^ 4 := by
  rw [i8Psi4s47_eq_S]
  unfold i8Psi4s47S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_negOne_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s48` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s48S0 (x : ℝ) : ℝ :=
    (-70 * x ^ 3 - 7 / 2 * x ^ 4) / x ^ 2 +
    (7 * x ^ 4 + 70 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-54 * x ^ 2 - 40 * x ^ 3 - 24 * x - 10 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-40 * x ^ 3 - 4 * x ^ 4 + 24 * x ^ 2) / x ^ 2 * hpl [zero, zero] x +
    (-16 * x + 8 * x ^ 4 + 24 * x ^ 2 + 48 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-8 * x + 4 * x ^ 4 + 16 * x ^ 2 + 24 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero] x +
    (16) * hpl [zero, zero, zero] x +
    (48) * hpl [zero, negOne, zero, zero] x +
    (24) * hpl [zero, zero, negOne, zero] x

theorem continuousOn_i8Psi4s48S0 : ContinuousOn i8Psi4s48S0 (Ioc 0 1) := by
  unfold i8Psi4s48S0
  exact (((((((((i13_cont_coef (p := fun x => -70 * x ^ 3 - 7 / 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 7 * x ^ 4 + 70 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -54 * x ^ 2 - 40 * x ^ 3 - 24 * x -
        10 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -40 * x ^ 3 - 4 * x ^ 4 + 24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -16 * x + 8 * x ^ 4 + 24 * x ^ 2 +
        48 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x + 4 * x ^ 4 + 16 * x ^ 2 +
        24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero])))

theorem i8Psi4s48_eq_S (x : ℝ) : i8Psi4s48 x = i8Psi4s48S0 x := by
  unfold i8Psi4s48 i8Psi4s48S0 i8Psi4s48N0 i8Psi4s48N1 i8Psi4s48N2 i8Psi4s48N3 i8Psi4s48N4
    i8Psi4s48W
  ring

theorem continuousOn_i8Psi4s48 : ContinuousOn i8Psi4s48 (Ioc 0 1) := by
  rw [show i8Psi4s48 = fun x => i8Psi4s48S0 x from funext i8Psi4s48_eq_S]
  exact continuousOn_i8Psi4s48S0

theorem i8Psi4s48_one : i8Psi4s48 1 = -147 / 2 - 6 * zeta3 + 7 / 10 * π ^ 4 + 32 / 3 * π ^ 2 := by
  rw [i8Psi4s48_eq_S]
  unfold i8Psi4s48S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s49` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s49S0 (x : ℝ) : ℝ :=
    (20 * x + 44 * x ^ 3 + 7 / 4 * x ^ 4) / x ^ 2 +
    (-44 * x ^ 3 + 20 * x - 7 / 2 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (7 * x ^ 4 + 20 * x + 44 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-36 * x ^ 3 - 8 * x ^ 2 - 6 * x ^ 4 + 12 * x) / x ^ 2 * hpl [zero, zero, zero] x +
    (-36) * hpl [zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s49S0 : ContinuousOn i8Psi4s49S0 (Ioc 0 1) := by
  unfold i8Psi4s49S0
  exact (((((i13_cont_coef (p := fun x => 20 * x + 44 * x ^ 3 + 7 / 4 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -44 * x ^ 3 + 20 * x - 7 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 7 * x ^ 4 + 20 * x + 44 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -36 * x ^ 3 - 8 * x ^ 2 - 6 * x ^ 4 +
        12 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero])))

theorem i8Psi4s49_eq_S (x : ℝ) : i8Psi4s49 x = i8Psi4s49S0 x := by
  unfold i8Psi4s49 i8Psi4s49S0 i8Psi4s49N0 i8Psi4s49N1 i8Psi4s49N2 i8Psi4s49N3 i8Psi4s49N4
    i8Psi4s49W
  ring

theorem continuousOn_i8Psi4s49 : ContinuousOn i8Psi4s49 (Ioc 0 1) := by
  rw [show i8Psi4s49 = fun x => i8Psi4s49S0 x from funext i8Psi4s49_eq_S]
  exact continuousOn_i8Psi4s49S0

theorem i8Psi4s49_one : i8Psi4s49 1 = 263 / 4 := by
  rw [i8Psi4s49_eq_S]
  unfold i8Psi4s49S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_zero_zero_at_one]
  norm_num

/-- Chunk 0 of `i8Psi4s50` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s50S0 (x : ℝ) : ℝ :=
    (66 * x - 239 / 16 * x ^ 4 - 119 / 2 * x ^ 3 - 4 * π ^ 2 * x ^ 3 - 7 / 3 * π ^ 2 * x -
      7 / 8 * π ^ 2 * x ^ 4 - π ^ 2 ^ 2 * x ^ 3 / 12 - π ^ 2 ^ 2 * x ^ 4 / 72 +
      x * π ^ 2 ^ 2 / 36) / x ^ 2 +
    (16 * x ^ 2 + 50 * x + 111 / 8 * x ^ 4 + 151 / 2 * x ^ 3 - π ^ 2 * x -
      π ^ 2 ^ 2 * x ^ 2 / 12 + 4 / 3 * π ^ 2 * x ^ 2 + 5 / 12 * π ^ 2 * x ^ 4 +
      8 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-48 * x ^ 3 - 28 * x - 131 / 2 * x ^ 2 - 21 / 2 * x ^ 4 - π ^ 2 * x ^ 2 - 2 * π ^ 2 * x ^ 3 -
      π ^ 2 * x ^ 4 / 3 + 2 / 3 * π ^ 2 * x) / x ^ 2 * hpl [negOne, zero] x +
    (-22 * x ^ 3 + 12 * x ^ 2 + 34 * x - 5 / 4 * x ^ 4 + π ^ 2 * x ^ 3 - π ^ 2 * x / 3 +
      π ^ 2 * x ^ 4 / 6 + 4 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, zero] x +
    (-24 * x + 10 * x ^ 4 + 30 * x ^ 2 + 64 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-12 * x + 5 * x ^ 4 + 16 * x ^ 2 + 32 * x ^ 3 -
      2 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-48 * x ^ 3 - 8 * x ^ 2 + 18 * x - 15 / 2 * x ^ 4 +
      π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, zero, zero] x +
    (-48 * x ^ 3 - 24 * x ^ 2 - 8 * x ^ 4 + 16 * x) / x ^ 2 * hpl [negOne, negOne, zero, zero] x +
    (-24 * x ^ 3 - 12 * x ^ 2 - 4 * x ^ 4 + 8 * x) / x ^ 2 * hpl [negOne, zero, negOne, zero] x +
    (-12 * x + 6 * x ^ 4 + 18 * x ^ 2 + 36 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero, zero] x +
    (-8 * x + 4 * x ^ 4 + 24 * x ^ 3 + 32 * x ^ 2) / x ^ 2 * hpl [zero, negOne, zero, zero] x +
    (-4 * x + 2 * x ^ 4 + 12 * x ^ 3 + 16 * x ^ 2) / x ^ 2 * hpl [zero, zero, negOne, zero] x +
    (-24 * x ^ 2 - 18 * x ^ 3 - 3 * x ^ 4 + 6 * x) / x ^ 2 * hpl [zero, zero, zero, zero] x +
    (-48) * hpl [zero, negOne, negOne, zero, zero] x +
    (-24) * hpl [zero, negOne, zero, negOne, zero] x +
    (36) * hpl [zero, negOne, zero, zero, zero] x +
    (24) * hpl [zero, zero, negOne, zero, zero] x +
    (12) * hpl [zero, zero, zero, negOne, zero] x +
    (-18) * hpl [zero, zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s50S0 : ContinuousOn i8Psi4s50S0 (Ioc 0 1) := by
  unfold i8Psi4s50S0
  exact (((((((((((((((((((i13_cont_coef (p := fun x => 66 * x - 239 / 16 * x ^ 4 -
    119 / 2 * x ^ 3 - 4 * π ^ 2 * x ^ 3 - 7 / 3 * π ^ 2 * x - 7 / 8 * π ^ 2 * x ^ 4 -
    π ^ 2 ^ 2 * x ^ 3 / 12 - π ^ 2 ^ 2 * x ^ 4 / 72 + x * π ^ 2 ^ 2 / 36) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 16 * x ^ 2 + 50 * x + 111 / 8 * x ^ 4 + 151 / 2 * x ^ 3 -
        π ^ 2 * x - π ^ 2 ^ 2 * x ^ 2 / 12 + 4 / 3 * π ^ 2 * x ^ 2 + 5 / 12 * π ^ 2 * x ^ 4 +
        8 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -48 * x ^ 3 - 28 * x - 131 / 2 * x ^ 2 - 21 / 2 * x ^ 4 -
        π ^ 2 * x ^ 2 - 2 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 3 +
        2 / 3 * π ^ 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -22 * x ^ 3 + 12 * x ^ 2 + 34 * x - 5 / 4 * x ^ 4 +
        π ^ 2 * x ^ 3 - π ^ 2 * x / 3 + π ^ 2 * x ^ 4 / 6 +
        4 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x + 10 * x ^ 4 + 30 * x ^ 2 +
        64 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x + 5 * x ^ 4 + 16 * x ^ 2 + 32 * x ^ 3 -
        2 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -48 * x ^ 3 - 8 * x ^ 2 + 18 * x - 15 / 2 * x ^ 4 +
        π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -48 * x ^ 3 - 24 * x ^ 2 - 8 * x ^ 4 +
        16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 3 - 12 * x ^ 2 - 4 * x ^ 4 +
        8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x + 6 * x ^ 4 + 18 * x ^ 2 +
        36 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x + 4 * x ^ 4 + 24 * x ^ 3 +
        32 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x + 2 * x ^ 4 + 12 * x ^ 3 +
        16 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 18 * x ^ 3 - 3 * x ^ 4 +
        6 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, zero])))

theorem i8Psi4s50_eq_S (x : ℝ) : i8Psi4s50 x = i8Psi4s50S0 x := by
  unfold i8Psi4s50 i8Psi4s50S0 i8Psi4s50N0 i8Psi4s50N1 i8Psi4s50N2 i8Psi4s50N3 i8Psi4s50N4
    i8Psi4s50W
  ring

theorem continuousOn_i8Psi4s50 : ContinuousOn i8Psi4s50 (Ioc 0 1) := by
  rw [show i8Psi4s50 = fun x => i8Psi4s50S0 x from funext i8Psi4s50_eq_S]
  exact continuousOn_i8Psi4s50S0

theorem i8Psi4s50_one : i8Psi4s50 1 = -135 / 16 + 24 * zeta5 - 3 / 2 * zeta3 + π ^ 4 / 3 +
    131 / 24 * π ^ 2 - 4 * π ^ 2 * zeta3 := by
  have h5 : hpl [zero, zero, zero, zero, zero] 1 = 0 := by
    rw [hpl_of_allZero (by decide)]
    simp
  rw [i8Psi4s50_eq_S]
  unfold i8Psi4s50S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_zero_zero_at_one, hpl_negOne_negOne_zero_zero_at_one,
    hpl_negOne_zero_negOne_zero_at_one, hpl_negOne_zero_zero_zero_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_zero_at_one, hpl_zero_negOne_negOne_zero_zero_at_one,
    hpl_zero_negOne_zero_negOne_zero_at_one, hpl_zero_negOne_zero_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_zero_at_one, hpl_zero_zero_zero_negOne_zero_at_one, h5]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s51` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s51S0 (x : ℝ) : ℝ :=
    (x ^ 4 - 4 * x ^ 3 + 4 * x) / x ^ 2 +
    (-2 * x ^ 4 + 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (4) * hpl [zero, zero] x

theorem continuousOn_i8Psi4s51S0 : ContinuousOn i8Psi4s51S0 (Ioc 0 1) := by
  unfold i8Psi4s51S0
  exact (((i13_cont_coef (p := fun x => x ^ 4 - 4 * x ^ 3 + 4 * x) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 4 + 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero])))

theorem i8Psi4s51_eq_S (x : ℝ) : i8Psi4s51 x = i8Psi4s51S0 x := by
  unfold i8Psi4s51 i8Psi4s51S0 i8Psi4s51N0 i8Psi4s51N1 i8Psi4s51N2 i8Psi4s51N3 i8Psi4s51N4
    i8Psi4s51W
  ring

theorem continuousOn_i8Psi4s51 : ContinuousOn i8Psi4s51 (Ioc 0 1) := by
  rw [show i8Psi4s51 = fun x => i8Psi4s51S0 x from funext i8Psi4s51_eq_S]
  exact continuousOn_i8Psi4s51S0

theorem i8Psi4s51_one : i8Psi4s51 1 = 1 := by
  rw [i8Psi4s51_eq_S]
  unfold i8Psi4s51S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one]
  norm_num

/-- Chunk 0 of `i8Psi4s52` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s52S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 - 3 / 2 * x - 3 / 2 * x ^ 3) / x ^ 2 +
    (-1 / 2 + x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [negOne] x +
    (x ^ 3 - x - x ^ 2 / 2 - x ^ 4 / 2) / x ^ 2 * hpl [zero] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [zero, negOne] x +
    (-1) * hpl [zero, zero] x +
    (-4) * hpl [zero, negOne, zero] x +
    (-4) * hpl [zero, zero, negOne] x

theorem continuousOn_i8Psi4s52S0 : ContinuousOn i8Psi4s52S0 (Ioc 0 1) := by
  unfold i8Psi4s52S0
  exact ((((((((i13_cont_coef (p := fun x => x ^ 4 / 2 - 3 / 2 * x -
    3 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - x - x ^ 2 / 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne])))

theorem i8Psi4s52_eq_S (x : ℝ) : i8Psi4s52 x = i8Psi4s52S0 x := by
  unfold i8Psi4s52 i8Psi4s52S0 i8Psi4s52N0 i8Psi4s52N1 i8Psi4s52N2 i8Psi4s52N3 i8Psi4s52N4
    i8Psi4s52W
  ring

theorem continuousOn_i8Psi4s52 : ContinuousOn i8Psi4s52 (Ioc 0 1) := by
  rw [show i8Psi4s52 = fun x => i8Psi4s52S0 x from funext i8Psi4s52_eq_S]
  exact continuousOn_i8Psi4s52S0

theorem i8Psi4s52_one : i8Psi4s52 1 = -5 / 2 + 3 * zeta3 := by
  rw [i8Psi4s52_eq_S]
  unfold i8Psi4s52S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s53` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s53S0 (x : ℝ) : ℝ :=
    (-7 / 2 * x ^ 3 + 3 / 8 * x ^ 4) / x ^ 2 +
    (-x ^ 4 / 2 + 3 / 2 * x + 3 / 2 * x ^ 3 + 7 / 2 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (-3 / 2 * x ^ 2 - x ^ 4 / 4 + 3 / 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (1 / 2 + x ^ 4 / 2 - x ^ 2) / x ^ 2 * hpl [negOne, negOne] x +
    (x + x ^ 4 / 2 - x ^ 3 - x ^ 2 / 2) / x ^ 2 * hpl [negOne, zero] x +
    (x + x ^ 2 / 2 + x ^ 4 / 2 - x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (-1) * hpl [zero, zero] x +
    (1 - x ^ 4) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (1 - x ^ 4) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (1 - x ^ 4) / x ^ 2 * hpl [zero, negOne, negOne] x +
    (1) * hpl [zero, negOne, zero] x +
    (1) * hpl [zero, zero, negOne] x +
    (4) * hpl [zero, negOne, negOne, zero] x +
    (4) * hpl [zero, negOne, zero, negOne] x +
    (4) * hpl [zero, zero, negOne, negOne] x

theorem continuousOn_i8Psi4s53S0 : ContinuousOn i8Psi4s53S0 (Ioc 0 1) := by
  unfold i8Psi4s53S0
  exact (((((((((((((((i13_cont_coef (p := fun x => -7 / 2 * x ^ 3 +
    3 / 8 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -x ^ 4 / 2 + 3 / 2 * x + 3 / 2 * x ^ 3 +
        7 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -3 / 2 * x ^ 2 - x ^ 4 / 4 + 3 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 1 / 2 + x ^ 4 / 2 - x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x + x ^ 4 / 2 - x ^ 3 - x ^ 2 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x + x ^ 2 / 2 + x ^ 4 / 2 - x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne])))

theorem i8Psi4s53_eq_S (x : ℝ) : i8Psi4s53 x = i8Psi4s53S0 x := by
  unfold i8Psi4s53 i8Psi4s53S0 i8Psi4s53N0 i8Psi4s53N1 i8Psi4s53N2 i8Psi4s53N3 i8Psi4s53N4
    i8Psi4s53W
  ring

theorem continuousOn_i8Psi4s53 : ContinuousOn i8Psi4s53 (Ioc 0 1) := by
  rw [show i8Psi4s53 = fun x => i8Psi4s53S0 x from funext i8Psi4s53_eq_S]
  exact continuousOn_i8Psi4s53S0

theorem i8Psi4s53_one : i8Psi4s53 1 = -25 / 8 - 8 * Li 4 (1 / 2) + 6 * Real.log 2 -
    3 / 4 * zeta3 - Real.log 2 ^ 4 / 3 + π ^ 2 / 12 + π ^ 4 / 12 - 7 * Real.log 2 * zeta3 +
    π ^ 2 * Real.log 2 ^ 2 / 3 := by
  rw [i8Psi4s53_eq_S]
  unfold i8Psi4s53S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_negOne_at_one, hpl_negOne_zero_at_one,
    hpl_zero_negOne_at_one, hpl_zero_zero_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_negOne_zero_negOne_at_one, hpl_zero_negOne_negOne_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_zero_negOne_at_one, hpl_zero_zero_negOne_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s54` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s54S0 (x : ℝ) : ℝ :=
    (x ^ 3 / 2 - 3 / 16 * x ^ 4 - x / 2) / x ^ 2 +
    (-1 / 4 + x ^ 4 / 4) / x ^ 2 * hpl [negOne] x +
    (-x / 4 - x ^ 2 / 4 - x ^ 3 / 4 + x ^ 4 / 8) / x ^ 2 * hpl [zero] x +
    (-1 / 4 + x ^ 2 / 2 - x ^ 4 / 4) / x ^ 2 * hpl [negOne, zero] x +
    (-1 / 2 - x ^ 4 / 2) / x ^ 2 * hpl [zero, negOne] x +
    (-1 / 4) * hpl [zero, zero] x +
    (-1 / 2 + x ^ 4 / 2) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [zero, zero, negOne] x +
    (-2) * hpl [zero, zero, negOne, zero] x +
    (-4) * hpl [zero, zero, zero, negOne] x

theorem continuousOn_i8Psi4s54S0 : ContinuousOn i8Psi4s54S0 (Ioc 0 1) := by
  unfold i8Psi4s54S0
  exact ((((((((((i13_cont_coef (p := fun x => x ^ 3 / 2 - 3 / 16 * x ^ 4 -
    x / 2) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -1 / 4 + x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x / 4 - x ^ 2 / 4 - x ^ 3 / 4 + x ^ 4 / 8) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -1 / 4 + x ^ 2 / 2 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne])))

theorem i8Psi4s54_eq_S (x : ℝ) : i8Psi4s54 x = i8Psi4s54S0 x := by
  unfold i8Psi4s54 i8Psi4s54S0 i8Psi4s54N0 i8Psi4s54N1 i8Psi4s54N2 i8Psi4s54N3 i8Psi4s54N4
    i8Psi4s54W
  ring

theorem continuousOn_i8Psi4s54 : ContinuousOn i8Psi4s54 (Ioc 0 1) := by
  rw [show i8Psi4s54 = fun x => i8Psi4s54S0 x from funext i8Psi4s54_eq_S]
  exact continuousOn_i8Psi4s54S0

theorem i8Psi4s54_one : i8Psi4s54 1 = -3 / 16 - π ^ 2 / 12 + 7 / 360 * π ^ 4 := by
  rw [i8Psi4s54_eq_S]
  unfold i8Psi4s54S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s55` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s55S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 - 45 / 4 * x ^ 3) / x ^ 2 +
    (7 * x ^ 3 - 3 / 4 * x ^ 4 + 31 / 4 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (-x ^ 4 / 4 + 7 / 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (x ^ 4 - 7 * x ^ 2 - 3 * x - 3 * x ^ 3) / x ^ 2 * hpl [negOne, negOne] x +
    (x ^ 4 / 2 - 3 * x ^ 3 - 7 / 2 * x ^ 2) / x ^ 2 * hpl [negOne, zero] x +
    (x ^ 4 / 2 - 3 * x ^ 3 + 3 * x ^ 2) / x ^ 2 * hpl [zero, negOne] x +
    (-1 - x ^ 4 + 2 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, negOne] x +
    (x ^ 2 - x ^ 4 - 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (x ^ 2 - x ^ 4 - 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (-x ^ 2 - x ^ 4 - 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [zero, negOne, negOne] x +
    (2) * hpl [zero, negOne, zero] x +
    (2) * hpl [zero, zero, negOne] x +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, negOne, zero] x +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, zero, negOne] x +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, negOne, negOne] x +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, negOne, negOne] x +
    (-2) * hpl [zero, negOne, negOne, zero] x +
    (-2) * hpl [zero, negOne, zero, negOne] x +
    (-2) * hpl [zero, zero, negOne, negOne] x +
    (-8) * hpl [zero, negOne, negOne, negOne, zero] x

theorem continuousOn_i8Psi4s55S0 : ContinuousOn i8Psi4s55S0 (Ioc 0 1) := by
  unfold i8Psi4s55S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 / 2 -
    45 / 4 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 7 * x ^ 3 - 3 / 4 * x ^ 4 + 31 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 / 4 + 7 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 7 * x ^ 2 - 3 * x - 3 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - 3 * x ^ 3 - 7 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - 3 * x ^ 3 + 3 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 4 + 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 - x ^ 4 - 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 - x ^ 4 - 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -x ^ 2 - x ^ 4 - 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, negOne, zero])))

/-- Chunk 1 of `i8Psi4s55` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s55S1 (x : ℝ) : ℝ :=
    (-8) * hpl [zero, negOne, negOne, zero, negOne] x +
    (-8) * hpl [zero, negOne, zero, negOne, negOne] x +
    (-8) * hpl [zero, zero, negOne, negOne, negOne] x

theorem continuousOn_i8Psi4s55S1 : ContinuousOn i8Psi4s55S1 (Ioc 0 1) := by
  unfold i8Psi4s55S1
  exact (((continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero, negOne])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne, negOne])))

theorem i8Psi4s55_eq_S (x : ℝ) : i8Psi4s55 x = i8Psi4s55S0 x + i8Psi4s55S1 x := by
  unfold i8Psi4s55 i8Psi4s55S0 i8Psi4s55S1 i8Psi4s55N0 i8Psi4s55N1 i8Psi4s55N2 i8Psi4s55N3
    i8Psi4s55N4 i8Psi4s55W
  ring

theorem continuousOn_i8Psi4s55 : ContinuousOn i8Psi4s55 (Ioc 0 1) := by
  rw [show i8Psi4s55 = fun x => i8Psi4s55S0 x + i8Psi4s55S1 x from funext i8Psi4s55_eq_S]
  exact (continuousOn_i8Psi4s55S0.add continuousOn_i8Psi4s55S1)

theorem i8Psi4s55_one : i8Psi4s55 1 = -43 / 4 - 6 * Real.log 2 ^ 2 + 4 * Li 4 (1 / 2) +
    14 * Real.log 2 + 16 * Li 5 (1 / 2) - 33 / 4 * zeta5 - 7 / 4 * zeta3 - π ^ 4 / 24 +
    Real.log 2 ^ 4 / 6 + 8 / 15 * Real.log 2 ^ 5 + 13 / 24 * π ^ 2 + 7 * zeta3 * Real.log 2 ^ 2 +
    16 * Real.log 2 * Li 4 (1 / 2) - 4 / 9 * π ^ 2 * Real.log 2 ^ 3 - 2 / 3 * π ^ 2 * zeta3 -
    π ^ 2 * Real.log 2 ^ 2 / 6 + 7 / 2 * Real.log 2 * zeta3 := by
  rw [i8Psi4s55_eq_S]
  unfold i8Psi4s55S0 i8Psi4s55S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_negOne_at_one, hpl_negOne_zero_at_one,
    hpl_zero_negOne_at_one, hpl_negOne_negOne_negOne_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_negOne_zero_negOne_at_one, hpl_zero_negOne_negOne_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_negOne_negOne_negOne_zero_at_one,
    hpl_negOne_negOne_zero_negOne_at_one, hpl_negOne_zero_negOne_negOne_at_one,
    hpl_zero_negOne_negOne_negOne_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_zero_negOne_at_one, hpl_zero_zero_negOne_negOne_at_one,
    hpl_zero_negOne_negOne_negOne_zero_at_one, hpl_zero_negOne_negOne_zero_negOne_at_one,
    hpl_zero_negOne_zero_negOne_negOne_at_one, hpl_zero_zero_negOne_negOne_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s56` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s56S0 (x : ℝ) : ℝ :=
    (-x ^ 4 / 4 + 33 / 8 * x ^ 3) / x ^ 2 +
    (-5 / 2 * x ^ 3 - 3 / 8 * x ^ 2 + 3 / 8 * x ^ 4 + 5 / 2 * x) / x ^ 2 * hpl [negOne] x +
    (-5 / 2 * x ^ 2 - 5 / 4 * x ^ 3 + x ^ 4 / 8) / x ^ 2 * hpl [zero] x +
    (x + x ^ 3 - x ^ 4 / 4 + 9 / 4 * x ^ 2) / x ^ 2 * hpl [negOne, zero] x +
    (-3 / 4 * x ^ 4 + 5 / 2 * x + 5 / 2 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (-1) * hpl [zero, zero] x +
    (1 / 2 + x ^ 4 / 2 - x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (x + x ^ 4 / 2 - x ^ 3) / x ^ 2 * hpl [zero, negOne, zero] x +
    (x ^ 4 + x ^ 2 / 2 - 2 * x ^ 3 + 2 * x) / x ^ 2 * hpl [zero, zero, negOne] x +
    (1 - x ^ 4) / x ^ 2 * hpl [negOne, zero, negOne, zero] x +
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero, negOne] x +
    (1 - x ^ 4) / x ^ 2 * hpl [zero, negOne, zero, negOne] x +
    (1) * hpl [zero, zero, negOne, zero] x +
    (2) * hpl [zero, zero, zero, negOne] x +
    (4) * hpl [zero, negOne, zero, negOne, zero] x +
    (8) * hpl [zero, negOne, zero, zero, negOne] x +
    (4) * hpl [zero, zero, negOne, zero, negOne] x

theorem continuousOn_i8Psi4s56S0 : ContinuousOn i8Psi4s56S0 (Ioc 0 1) := by
  unfold i8Psi4s56S0
  exact (((((((((((((((((i13_cont_coef (p := fun x => -x ^ 4 / 4 +
    33 / 8 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -5 / 2 * x ^ 3 - 3 / 8 * x ^ 2 + 3 / 8 * x ^ 4 +
        5 / 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -5 / 2 * x ^ 2 - 5 / 4 * x ^ 3 + x ^ 4 / 8) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x + x ^ 3 - x ^ 4 / 4 + 9 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -3 / 4 * x ^ 4 + 5 / 2 * x + 5 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 1 / 2 + x ^ 4 / 2 - x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => x + x ^ 4 / 2 - x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + x ^ 2 / 2 - 2 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, negOne])))

theorem i8Psi4s56_eq_S (x : ℝ) : i8Psi4s56 x = i8Psi4s56S0 x := by
  unfold i8Psi4s56 i8Psi4s56S0 i8Psi4s56N0 i8Psi4s56N1 i8Psi4s56N2 i8Psi4s56N3 i8Psi4s56N4
    i8Psi4s56W
  ring

theorem continuousOn_i8Psi4s56 : ContinuousOn i8Psi4s56 (Ioc 0 1) := by
  rw [show i8Psi4s56 = fun x => i8Psi4s56S0 x from funext i8Psi4s56_eq_S]
  exact continuousOn_i8Psi4s56S0

theorem i8Psi4s56_one : i8Psi4s56 1 = 31 / 8 - 41 / 8 * zeta5 - 7 / 720 * π ^ 4 + π ^ 2 / 48 +
    3 / 8 * zeta3 + 5 / 12 * π ^ 2 * zeta3 := by
  rw [i8Psi4s56_eq_S]
  unfold i8Psi4s56S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_zero_negOne_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_negOne_zero_negOne_zero_at_one,
    hpl_negOne_zero_zero_negOne_at_one, hpl_zero_negOne_zero_negOne_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_at_one,
    hpl_zero_negOne_zero_negOne_zero_at_one, hpl_zero_negOne_zero_zero_negOne_at_one,
    hpl_zero_zero_negOne_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s57` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s57S0 (x : ℝ) : ℝ :=
    (-x ^ 4 / 4 + 17 / 8 * x ^ 3) / x ^ 2 +
    (x - x ^ 3 - 3 / 8 * x ^ 2 + 3 / 8 * x ^ 4) / x ^ 2 * hpl [negOne] x +
    (-x ^ 2 - 3 / 4 * x ^ 3 + x ^ 4 / 8) / x ^ 2 * hpl [zero] x +
    (1 / 2 - x ^ 4 / 2) / x ^ 2 * hpl [negOne, negOne] x +
    (x / 2 + x ^ 3 / 2 - x ^ 4 / 4 + 5 / 4 * x ^ 2) / x ^ 2 * hpl [negOne, zero] x +
    (x / 2 + x ^ 2 / 2 + x ^ 3 / 2 - x ^ 4 / 4) / x ^ 2 * hpl [zero, negOne] x +
    (-1 / 2) * hpl [zero, zero] x +
    (1 / 2 + x ^ 4 / 2 - x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (1 / 2 + x ^ 4 / 2 - x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (1 + x ^ 4) / x ^ 2 * hpl [zero, negOne, negOne] x +
    (1 / 2) * hpl [zero, negOne, zero] x +
    (1 / 2) * hpl [zero, zero, negOne] x +
    (1 - x ^ 4) / x ^ 2 * hpl [zero, negOne, negOne, zero] x +
    (1 - x ^ 4) / x ^ 2 * hpl [zero, negOne, zero, negOne] x +
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne, negOne] x +
    (4) * hpl [zero, zero, negOne, negOne, zero] x +
    (4) * hpl [zero, zero, negOne, zero, negOne] x +
    (8) * hpl [zero, zero, zero, negOne, negOne] x

theorem continuousOn_i8Psi4s57S0 : ContinuousOn i8Psi4s57S0 (Ioc 0 1) := by
  unfold i8Psi4s57S0
  exact ((((((((((((((((((i13_cont_coef (p := fun x => -x ^ 4 / 4 +
    17 / 8 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x - x ^ 3 - 3 / 8 * x ^ 2 + 3 / 8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 2 - 3 / 4 * x ^ 3 + x ^ 4 / 8) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 1 / 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x / 2 + x ^ 3 / 2 - x ^ 4 / 4 +
        5 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x / 2 + x ^ 2 / 2 + x ^ 3 / 2 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 1 / 2 + x ^ 4 / 2 - x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 1 / 2 + x ^ 4 / 2 - x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne, negOne])))

theorem i8Psi4s57_eq_S (x : ℝ) : i8Psi4s57 x = i8Psi4s57S0 x := by
  unfold i8Psi4s57 i8Psi4s57S0 i8Psi4s57N0 i8Psi4s57N1 i8Psi4s57N2 i8Psi4s57N3 i8Psi4s57N4
    i8Psi4s57W
  ring

theorem continuousOn_i8Psi4s57 : ContinuousOn i8Psi4s57 (Ioc 0 1) := by
  rw [show i8Psi4s57 = fun x => i8Psi4s57S0 x from funext i8Psi4s57_eq_S]
  exact continuousOn_i8Psi4s57S0

theorem i8Psi4s57_one : i8Psi4s57 1 = 15 / 8 - zeta3 / 8 - π ^ 2 / 16 + 29 / 8 * zeta5 -
    π ^ 2 * zeta3 / 3 := by
  rw [i8Psi4s57_eq_S]
  unfold i8Psi4s57S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_negOne_at_one, hpl_negOne_zero_at_one,
    hpl_zero_negOne_at_one, hpl_zero_zero_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_negOne_zero_negOne_at_one, hpl_zero_negOne_negOne_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_zero_negOne_at_one, hpl_zero_zero_negOne_negOne_at_one,
    hpl_zero_zero_negOne_negOne_zero_at_one, hpl_zero_zero_negOne_zero_negOne_at_one,
    hpl_zero_zero_zero_negOne_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s58` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s58S0 (x : ℝ) : ℝ :=
    (-5 / 16 * x - 5 / 16 * x ^ 3 + x ^ 4 / 8) / x ^ 2 +
    (-3 / 16 - 3 / 16 * x ^ 4 + 3 / 8 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (-3 / 16 * x ^ 2 - x / 8 - x ^ 4 / 16 + x ^ 3 / 8) / x ^ 2 * hpl [zero] x +
    (-1 / 8 + x ^ 4 / 8) / x ^ 2 * hpl [negOne, zero] x +
    (-3 / 8 + 3 / 8 * x ^ 4) / x ^ 2 * hpl [zero, negOne] x +
    (-1 / 8) * hpl [zero, zero] x +
    (-1 / 4 - x ^ 4 / 4) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-3 / 4 - 3 / 4 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne] x +
    (-1 / 2 + x ^ 4 / 2) / x ^ 2 * hpl [zero, zero, negOne, zero] x +
    (-3 / 2 + 3 / 2 * x ^ 4) / x ^ 2 * hpl [zero, zero, zero, negOne] x +
    (-2) * hpl [zero, zero, zero, negOne, zero] x +
    (-6) * hpl [zero, zero, zero, zero, negOne] x

theorem continuousOn_i8Psi4s58S0 : ContinuousOn i8Psi4s58S0 (Ioc 0 1) := by
  unfold i8Psi4s58S0
  exact ((((((((((((i13_cont_coef (p := fun x => -5 / 16 * x - 5 / 16 * x ^ 3 +
    x ^ 4 / 8) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -3 / 16 - 3 / 16 * x ^ 4 + 3 / 8 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -3 / 16 * x ^ 2 - x / 8 - x ^ 4 / 16 +
        x ^ 3 / 8) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -1 / 8 + x ^ 4 / 8) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -3 / 8 + 3 / 8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 4 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -3 / 4 - 3 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -3 / 2 + 3 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, negOne])))

theorem i8Psi4s58_eq_S (x : ℝ) : i8Psi4s58 x = i8Psi4s58S0 x := by
  unfold i8Psi4s58 i8Psi4s58S0 i8Psi4s58N0 i8Psi4s58N1 i8Psi4s58N2 i8Psi4s58N3 i8Psi4s58N4
    i8Psi4s58W
  ring

theorem continuousOn_i8Psi4s58 : ContinuousOn i8Psi4s58 (Ioc 0 1) := by
  rw [show i8Psi4s58 = fun x => i8Psi4s58S0 x from funext i8Psi4s58_eq_S]
  exact continuousOn_i8Psi4s58S0

theorem i8Psi4s58_one : i8Psi4s58 1 = -1 / 2 - 3 / 8 * zeta3 + 15 / 8 * zeta5 := by
  rw [i8Psi4s58_eq_S]
  unfold i8Psi4s58S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_at_one,
    hpl_zero_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s59` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s59S0 (x : ℝ) : ℝ :=
    (-2 * x ^ 4 + 4 * x ^ 3) / x ^ 2 +
    (-8) * hpl [zero] x +
    (-4 * x ^ 2 + 4 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (8) * hpl [zero, one] x

theorem continuousOn_i8Psi4s59S0 : ContinuousOn i8Psi4s59S0 (Ioc 0 1) := by
  unfold i8Psi4s59S0
  exact ((((i13_cont_coef (p := fun x => -2 * x ^ 4 + 4 * x ^ 3) (by fun_prop)).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 2 + 4 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one])))

theorem i8Psi4s59_eq_S (x : ℝ) : i8Psi4s59 x = i8Psi4s59S0 x := by
  unfold i8Psi4s59 i8Psi4s59S0 i8Psi4s59N0 i8Psi4s59N1 i8Psi4s59N2 i8Psi4s59N3 i8Psi4s59N4
    i8Psi4s59W
  ring

theorem continuousOn_i8Psi4s59 : ContinuousOn i8Psi4s59 (Ioc 0 1) := by
  rw [show i8Psi4s59 = fun x => i8Psi4s59S0 x from funext i8Psi4s59_eq_S]
  exact continuousOn_i8Psi4s59S0

theorem i8Psi4s59_one : i8Psi4s59 1 = 2 + 4 / 3 * π ^ 2 := by
  rw [i8Psi4s59_eq_S]
  unfold i8Psi4s59S0
  rw [hpl_zero_at_one, hpl_zero_one_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s60` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s60S0 (x : ℝ) : ℝ :=
    (-x ^ 4) / x ^ 2 +
    (x ^ 4 - x ^ 2 - 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (4) * hpl [zero] x +
    (x ^ 3 - x ^ 2 - 2 * x) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [negOne, one] x +
    (2) * hpl [zero, negOne] x +
    (-2) * hpl [zero, one] x +
    (-2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (-8) * hpl [zero, negOne, one] x +
    (-8) * hpl [zero, one, negOne] x

theorem continuousOn_i8Psi4s60S0 : ContinuousOn i8Psi4s60S0 (Ioc 0 1) := by
  unfold i8Psi4s60S0
  exact ((((((((((i13_cont_coef (p := fun x => -x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 - x ^ 2 - 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - x ^ 2 - 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne])))

theorem i8Psi4s60_eq_S (x : ℝ) : i8Psi4s60 x = i8Psi4s60S0 x := by
  unfold i8Psi4s60 i8Psi4s60S0 i8Psi4s60N0 i8Psi4s60N1 i8Psi4s60N2 i8Psi4s60N3 i8Psi4s60N4
    i8Psi4s60W
  ring

theorem continuousOn_i8Psi4s60 : ContinuousOn i8Psi4s60 (Ioc 0 1) := by
  rw [show i8Psi4s60 = fun x => i8Psi4s60S0 x from funext i8Psi4s60_eq_S]
  exact continuousOn_i8Psi4s60S0

theorem i8Psi4s60_one : i8Psi4s60 1 = -1 - 5 * zeta3 - π ^ 2 / 6 := by
  rw [i8Psi4s60_eq_S]
  unfold i8Psi4s60S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one,
    hpl_zero_one_at_one, hpl_zero_negOne_one_at_one, hpl_zero_one_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s61` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s61S0 (x : ℝ) : ℝ :=
    (-3 / 4 * x ^ 4 + 7 / 2 * x ^ 3) / x ^ 2 +
    (x ^ 4 - x ^ 2) / x ^ 2 * hpl [negOne] x +
    (x ^ 3 / 2 - 5 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x ^ 2 - x ^ 4 - 2 * x ^ 3 + 2 * x) / x ^ 2 * hpl [negOne, negOne] x +
    (x ^ 4 - x ^ 2 - 2 * x ^ 3 + 2 * x) / x ^ 2 * hpl [negOne, one] x +
    (-4) * hpl [zero, negOne] x +
    (-2) * hpl [zero, one] x +
    (x ^ 2 - x ^ 3 + 2 * x) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, one] x +
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, one, negOne] x +
    (-2) * hpl [zero, negOne, negOne] x +
    (2) * hpl [zero, negOne, one] x +
    (2) * hpl [zero, one, negOne] x +
    (2 + 2 * x + 2 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, negOne] x) +
    (8) * hpl [zero, negOne, negOne, one] x +
    (8) * hpl [zero, negOne, one, negOne] x +
    (8) * hpl [zero, one, negOne, negOne] x

theorem continuousOn_i8Psi4s61S0 : ContinuousOn i8Psi4s61S0 (Ioc 0 1) := by
  unfold i8Psi4s61S0
  exact (((((((((((((((((i13_cont_coef (p := fun x => -3 / 4 * x ^ 4 +
    7 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 - x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 - 5 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 - x ^ 4 - 2 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - x ^ 2 - 2 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 - x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, one]))).add
      ((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x + 2 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, negOne])))

theorem i8Psi4s61_eq_S (x : ℝ) : i8Psi4s61 x = i8Psi4s61S0 x := by
  unfold i8Psi4s61 i8Psi4s61S0 i8Psi4s61N0 i8Psi4s61N1 i8Psi4s61N2 i8Psi4s61N3 i8Psi4s61N4
    i8Psi4s61W
  ring

theorem continuousOn_i8Psi4s61 : ContinuousOn i8Psi4s61 (Ioc 0 1) := by
  rw [show i8Psi4s61 = fun x => i8Psi4s61S0 x from funext i8Psi4s61_eq_S]
  exact continuousOn_i8Psi4s61S0

theorem i8Psi4s61_one : i8Psi4s61 1 = 11 / 4 + zeta3 - 2 / 3 * π ^ 2 + π ^ 4 / 60 := by
  rw [i8Psi4s61_eq_S]
  unfold i8Psi4s61S0
  rw [hpl_negOne_at_one, hpl_negOne_negOne_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one,
    hpl_zero_one_at_one, hpl_negOne_negOne_one_at_one, hpl_negOne_one_negOne_at_one,
    hpl_zero_negOne_negOne_at_one, hpl_zero_negOne_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_negOne_negOne_one_at_one, hpl_zero_negOne_one_negOne_at_one,
    hpl_zero_one_negOne_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s62` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s62S0 (x : ℝ) : ℝ :=
    (3 / 4 * x ^ 3 + 3 / 8 * x ^ 4) / x ^ 2 +
    (-5 / 2 * x ^ 2 - 3 / 2 * x - 3 / 2 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [negOne] x +
    (2) * hpl [zero] x +
    (-x / 2 - x ^ 3 / 4 + x ^ 2 / 4) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-1 / 2 + x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [negOne, one] x +
    (x ^ 3 + x ^ 2 / 2 + x ^ 4 / 2 - x) / x ^ 2 * hpl [zero, negOne] x +
    (-1 / 2) * hpl [zero, one] x +
    (-1 / 2 + x ^ 2 / 2 + x ^ 3 / 2 - x / 2) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (-1 + x ^ 4) / x ^ 2 * hpl [zero, negOne, one] x +
    (1) * hpl [zero, zero, negOne] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [zero, one, negOne] x +
    (-1 - x - x ^ 2 - x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (-4) * hpl [zero, zero, negOne, one] x +
    (-4) * hpl [zero, zero, one, negOne] x +
    (-4) * hpl [zero, one, zero, negOne] x

theorem continuousOn_i8Psi4s62S0 : ContinuousOn i8Psi4s62S0 (Ioc 0 1) := by
  unfold i8Psi4s62S0
  exact (((((((((((((((i13_cont_coef (p := fun x => 3 / 4 * x ^ 3 +
    3 / 8 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -5 / 2 * x ^ 2 - 3 / 2 * x - 3 / 2 * x ^ 3 -
        x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x / 2 - x ^ 3 / 4 + x ^ 2 / 4) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + x ^ 2 / 2 + x ^ 4 / 2 - x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 2 / 2 + x ^ 3 / 2 - x / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 - x - x ^ 2 - x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne])))

theorem i8Psi4s62_eq_S (x : ℝ) : i8Psi4s62 x = i8Psi4s62S0 x := by
  unfold i8Psi4s62 i8Psi4s62S0 i8Psi4s62N0 i8Psi4s62N1 i8Psi4s62N2 i8Psi4s62N3 i8Psi4s62N4
    i8Psi4s62W
  ring

theorem continuousOn_i8Psi4s62 : ContinuousOn i8Psi4s62 (Ioc 0 1) := by
  rw [show i8Psi4s62 = fun x => i8Psi4s62S0 x from funext i8Psi4s62_eq_S]
  exact continuousOn_i8Psi4s62S0

theorem i8Psi4s62_one : i8Psi4s62 1 = 9 / 8 - 6 * Real.log 2 + 8 * Li 4 (1 / 2) -
    11 / 90 * π ^ 4 + Real.log 2 ^ 4 / 3 + 3 / 4 * zeta3 + 7 * Real.log 2 * zeta3 -
    π ^ 2 * Real.log 2 ^ 2 / 3 := by
  rw [i8Psi4s62_eq_S]
  unfold i8Psi4s62S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one,
    hpl_zero_one_at_one, hpl_zero_negOne_one_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_one_negOne_at_one, hpl_zero_zero_negOne_one_at_one, hpl_zero_zero_one_negOne_at_one,
    hpl_zero_one_zero_negOne_at_one]
  norm_num
  ring

end QED.ThreeLoopD
