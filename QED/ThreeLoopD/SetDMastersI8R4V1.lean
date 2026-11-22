/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4V0

/-!
# Set (d), master `I₈`: continuity and values at `1` of the sub-pieces 16 to 41 of `Ψ₄`

Each sub-piece `Ψ₄⁽ⁿ⁾` is continuous on `(0, 1]` (the words beginning with `1` carry a factor
`1 - ξ`), and its value at `ξ = 1` follows from the values of the harmonic polylogarithms at `1`.

## Main results

* `QED.ThreeLoopD.continuousOn_i8Psi4s16`, `QED.ThreeLoopD.i8Psi4s16_one` and their
  companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- Chunk 0 of `i8Psi4s16` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s16S0 (x : ℝ) : ℝ :=
    (-113 / 8 * x ^ 3 - 15 / 8 * x - x ^ 4 / 4) / x ^ 2 +
    (-1 / 8 - 4 * x + 4 * x ^ 3 + x ^ 4 / 8) / x ^ 2 * hpl [negOne] x +
    (-7 / 4 * x + 3 / 8 * x ^ 4 + 31 / 8 * x ^ 2 + 41 / 4 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-1 / 4 - 4 * x - 4 * x ^ 3 - 15 / 2 * x ^ 2 - x ^ 4 / 4) / x ^ 2 * hpl [negOne, zero] x +
    (-1 / 4 - 4 * x - 4 * x ^ 3 - x ^ 4 / 4) / x ^ 2 * hpl [zero, negOne] x +
    (-13 / 2 * x ^ 3 - 3 / 2 * x - x ^ 4 / 2 + 15 / 4 * x ^ 2) / x ^ 2 * hpl [zero, zero] x +
    (-1 / 2 + x ^ 4 / 2 - 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-1 / 2 + x ^ 4 / 2 - 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-1 / 2 + x ^ 4 / 2 - 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [zero, zero, negOne] x +
    (x ^ 4 / 2 - x + 3 * x ^ 3 + 7 / 2 * x ^ 2) / x ^ 2 * hpl [zero, zero, zero] x +
    (-1 - x ^ 4 - 6 * x ^ 2 - 4 * x - 4 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero, zero] x +
    (-1 - x ^ 4 - 4 * x - 4 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero, zero] x +
    (-1 - x ^ 4 - 4 * x - 4 * x ^ 3) / x ^ 2 * hpl [zero, zero, negOne, zero] x +
    (-1 - x ^ 4 - 4 * x - 4 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero, negOne] x +
    (3) * hpl [zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s16S0 : ContinuousOn i8Psi4s16S0 (Ioc 0 1) := by
  unfold i8Psi4s16S0
  exact (((((((((((((((i13_cont_coef (p := fun x => -113 / 8 * x ^ 3 - 15 / 8 * x -
    x ^ 4 / 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -1 / 8 - 4 * x + 4 * x ^ 3 + x ^ 4 / 8) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -7 / 4 * x + 3 / 8 * x ^ 4 + 31 / 8 * x ^ 2 +
        41 / 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -1 / 4 - 4 * x - 4 * x ^ 3 - 15 / 2 * x ^ 2 -
        x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 4 - 4 * x - 4 * x ^ 3 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -13 / 2 * x ^ 3 - 3 / 2 * x - x ^ 4 / 2 +
        15 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 4 / 2 - 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 4 / 2 - 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 4 / 2 - 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - x + 3 * x ^ 3 + 7 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 4 - 6 * x ^ 2 - 4 * x - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 4 - 4 * x - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 4 - 4 * x - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 4 - 4 * x - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero])))

theorem i8Psi4s16_eq_S (x : ℝ) : i8Psi4s16 x = i8Psi4s16S0 x := by
  unfold i8Psi4s16 i8Psi4s16S0 i8Psi4s16N0 i8Psi4s16N1 i8Psi4s16N2 i8Psi4s16N3 i8Psi4s16N4
    i8Psi4s16W
  ring

theorem continuousOn_i8Psi4s16 : ContinuousOn i8Psi4s16 (Ioc 0 1) := by
  rw [show i8Psi4s16 = fun x => i8Psi4s16S0 x from funext i8Psi4s16_eq_S]
  exact continuousOn_i8Psi4s16S0

theorem i8Psi4s16_one : i8Psi4s16 1 = -65 / 4 + 5 / 8 * π ^ 2 + 7 / 120 * π ^ 4 := by
  rw [i8Psi4s16_eq_S]
  unfold i8Psi4s16S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one, hpl_negOne_zero_zero_zero_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_negOne_at_one, hpl_zero_zero_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s17` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s17S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 + 85 / 4 * x ^ 3) / x ^ 2 +
    (-6 * x ^ 3 + 2 * x - 15 / 4 * x ^ 2 - x ^ 4 / 4) / x ^ 2 * hpl [negOne] x +
    (-2 * x ^ 2 - 31 / 2 * x ^ 3 - 3 / 4 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (x ^ 4 / 2 + 2 * x + 6 * x ^ 3 + 15 / 2 * x ^ 2) / x ^ 2 * hpl [negOne, zero] x +
    (x ^ 4 / 2 + 2 * x + 6 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (x ^ 4 - 2 * x ^ 2 + 10 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-12 * x ^ 3 - 6 * x ^ 2 - 2 * x ^ 4 + 4 * x) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-x ^ 4 - 6 * x ^ 3 + 2 * x) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-x ^ 4 - 6 * x ^ 3 + 2 * x) / x ^ 2 * hpl [zero, zero, negOne] x +
    (-4) * hpl [zero, zero, zero] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
      24 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero, zero] x +
    (2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne, zero] x +
    (2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * hpl [negOne, zero, zero, negOne] x +
    (-12) * hpl [zero, negOne, zero, zero] x +
    (-6) * hpl [zero, zero, negOne, zero] x +
    (-6) * hpl [zero, zero, zero, negOne] x

theorem continuousOn_i8Psi4s17S0 : ContinuousOn i8Psi4s17S0 (Ioc 0 1) := by
  unfold i8Psi4s17S0
  exact ((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 / 2 + 85 / 4 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -6 * x ^ 3 + 2 * x - 15 / 4 * x ^ 2 -
        x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 2 - 31 / 2 * x ^ 3 - 3 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 2 * x + 6 * x ^ 3 +
        15 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 2 * x + 6 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 2 * x ^ 2 + 10 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 6 * x ^ 2 - 2 * x ^ 4 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 6 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 6 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 +
        12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 +
        12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne])))

theorem i8Psi4s17_eq_S (x : ℝ) : i8Psi4s17 x = i8Psi4s17S0 x := by
  unfold i8Psi4s17 i8Psi4s17S0 i8Psi4s17N0 i8Psi4s17N1 i8Psi4s17N2 i8Psi4s17N3 i8Psi4s17N4
    i8Psi4s17W
  ring

theorem continuousOn_i8Psi4s17 : ContinuousOn i8Psi4s17 (Ioc 0 1) := by
  rw [show i8Psi4s17 = fun x => i8Psi4s17S0 x from funext i8Psi4s17_eq_S]
  exact continuousOn_i8Psi4s17S0

theorem i8Psi4s17_one : i8Psi4s17 1 = 87 / 4 - 8 * Real.log 2 - 33 / 4 * zeta3 - 7 / 30 * π ^ 4 -
    5 / 8 * π ^ 2 + 24 * Real.log 2 * zeta3 := by
  rw [i8Psi4s17_eq_S]
  unfold i8Psi4s17S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one, hpl_negOne_negOne_zero_zero_at_one,
    hpl_negOne_zero_negOne_zero_at_one, hpl_negOne_zero_zero_negOne_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s18` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s18S0 (x : ℝ) : ℝ :=
    (-31 * x ^ 3 - 3 / 2 * x ^ 4) / x ^ 2 +
    (x ^ 4 + 4 * x + 12 * x ^ 3 + 15 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (-4 * x ^ 2 + 2 * x ^ 4 + 20 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-24 * x ^ 3 - 12 * x ^ 2 - 4 * x ^ 4 + 8 * x) / x ^ 2 * hpl [negOne, zero] x +
    (-12 * x ^ 3 - 2 * x ^ 4 + 4 * x) / x ^ 2 * hpl [zero, negOne] x +
    (-8) * hpl [zero, zero] x +
    (8 + 8 * x ^ 4 + 32 * x + 32 * x ^ 3 + 48 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (-24) * hpl [zero, negOne, zero] x +
    (-12) * hpl [zero, zero, negOne] x

theorem continuousOn_i8Psi4s18S0 : ContinuousOn i8Psi4s18S0 (Ioc 0 1) := by
  unfold i8Psi4s18S0
  exact ((((((((((i13_cont_coef (p := fun x => -31 * x ^ 3 - 3 / 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 4 * x + 12 * x ^ 3 + 15 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 2 + 2 * x ^ 4 + 20 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 3 - 12 * x ^ 2 - 4 * x ^ 4 +
        8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 2 * x ^ 4 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 8 + 8 * x ^ 4 + 32 * x + 32 * x ^ 3 +
        48 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne])))

theorem i8Psi4s18_eq_S (x : ℝ) : i8Psi4s18 x = i8Psi4s18S0 x := by
  unfold i8Psi4s18 i8Psi4s18S0 i8Psi4s18N0 i8Psi4s18N1 i8Psi4s18N2 i8Psi4s18N3 i8Psi4s18N4
    i8Psi4s18W
  ring

theorem continuousOn_i8Psi4s18 : ContinuousOn i8Psi4s18 (Ioc 0 1) := by
  rw [show i8Psi4s18 = fun x => i8Psi4s18S0 x from funext i8Psi4s18_eq_S]
  exact continuousOn_i8Psi4s18S0

theorem i8Psi4s18_one : i8Psi4s18 1 = -65 / 2 + 27 * zeta3 + 32 * Real.log 2 + 11 / 6 * π ^ 2 -
    16 / 3 * Real.log 2 * π ^ 2 := by
  rw [i8Psi4s18_eq_S]
  unfold i8Psi4s18S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_negOne_zero_at_one, hpl_negOne_zero_negOne_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s19` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s19S0 (x : ℝ) : ℝ :=
    (-7 / 2 * x + 3 / 4 * x ^ 4 + 41 / 2 * x ^ 3) / x ^ 2 +
    (-1 / 2 - 15 * x ^ 2 - 8 * x - 8 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [negOne] x +
    (-x ^ 4 - 13 * x ^ 3 - 3 * x + 15 / 2 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (-1 + x ^ 4 - 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (-1 + x ^ 4 - 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (x ^ 4 - 2 * x + 6 * x ^ 3 + 7 * x ^ 2) / x ^ 2 * hpl [zero, zero] x +
    (-2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne] x +
    (6) * hpl [zero, zero, zero] x

theorem continuousOn_i8Psi4s19S0 : ContinuousOn i8Psi4s19S0 (Ioc 0 1) := by
  unfold i8Psi4s19S0
  exact ((((((((((i13_cont_coef (p := fun x => -7 / 2 * x + 3 / 4 * x ^ 4 +
    41 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -1 / 2 - 15 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 13 * x ^ 3 - 3 * x +
        15 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4 - 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4 - 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 2 * x + 6 * x ^ 3 + 7 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero])))

theorem i8Psi4s19_eq_S (x : ℝ) : i8Psi4s19 x = i8Psi4s19S0 x := by
  unfold i8Psi4s19 i8Psi4s19S0 i8Psi4s19N0 i8Psi4s19N1 i8Psi4s19N2 i8Psi4s19N3 i8Psi4s19N4
    i8Psi4s19W
  ring

theorem continuousOn_i8Psi4s19 : ContinuousOn i8Psi4s19 (Ioc 0 1) := by
  rw [show i8Psi4s19 = fun x => i8Psi4s19S0 x from funext i8Psi4s19_eq_S]
  exact continuousOn_i8Psi4s19S0

theorem i8Psi4s19_one : i8Psi4s19 1 = 71 / 4 - 32 * Real.log 2 - 9 * zeta3 := by
  rw [i8Psi4s19_eq_S]
  unfold i8Psi4s19S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s20` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s20S0 (x : ℝ) : ℝ :=
    (-37 * x ^ 3 + 50 * x - 111 / 8 * x ^ 4 - π ^ 2 * x - 5 / 3 * π ^ 2 * x ^ 3 -
      5 / 12 * π ^ 2 * x ^ 4) / x ^ 2 +
    (16 * x ^ 2 + 34 * x + 53 * x ^ 3 + 47 / 4 * x ^ 4 + π ^ 2 * x ^ 3 - π ^ 2 * x / 3 +
      π ^ 2 * x ^ 4 / 6 + 2 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (-27 * x ^ 2 - 20 * x ^ 3 - 12 * x - 5 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-22 * x ^ 3 - 4 * x ^ 2 + 18 * x - 5 / 2 * x ^ 4 +
      π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, zero] x +
    (-8 * x + 4 * x ^ 4 + 12 * x ^ 2 + 24 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-4 * x + 2 * x ^ 4 + 8 * x ^ 2 + 12 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-20 * x ^ 2 - 18 * x ^ 3 - 3 * x ^ 4 + 6 * x) / x ^ 2 * hpl [zero, zero, zero] x +
    (24) * hpl [zero, negOne, zero, zero] x +
    (12) * hpl [zero, zero, negOne, zero] x +
    (-18) * hpl [zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s20S0 : ContinuousOn i8Psi4s20S0 (Ioc 0 1) := by
  unfold i8Psi4s20S0
  exact ((((((((((i13_cont_coef (p := fun x => -37 * x ^ 3 + 50 * x - 111 / 8 * x ^ 4 -
    π ^ 2 * x - 5 / 3 * π ^ 2 * x ^ 3 - 5 / 12 * π ^ 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 16 * x ^ 2 + 34 * x + 53 * x ^ 3 + 47 / 4 * x ^ 4 +
        π ^ 2 * x ^ 3 - π ^ 2 * x / 3 + π ^ 2 * x ^ 4 / 6 +
        2 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -27 * x ^ 2 - 20 * x ^ 3 - 12 * x -
        5 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -22 * x ^ 3 - 4 * x ^ 2 + 18 * x - 5 / 2 * x ^ 4 +
        π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x + 4 * x ^ 4 + 12 * x ^ 2 +
        24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x + 2 * x ^ 4 + 8 * x ^ 2 + 12 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -20 * x ^ 2 - 18 * x ^ 3 - 3 * x ^ 4 +
        6 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero])))

theorem i8Psi4s20_eq_S (x : ℝ) : i8Psi4s20 x = i8Psi4s20S0 x := by
  unfold i8Psi4s20 i8Psi4s20S0 i8Psi4s20N0 i8Psi4s20N1 i8Psi4s20N2 i8Psi4s20N3 i8Psi4s20N4
    i8Psi4s20W
  ring

theorem continuousOn_i8Psi4s20 : ContinuousOn i8Psi4s20 (Ioc 0 1) := by
  rw [show i8Psi4s20 = fun x => i8Psi4s20S0 x from funext i8Psi4s20_eq_S]
  exact continuousOn_i8Psi4s20S0

theorem i8Psi4s20_one : i8Psi4s20 1 = -7 / 8 - 3 * zeta3 + 7 / 20 * π ^ 4 + 9 / 4 * π ^ 2 := by
  rw [i8Psi4s20_eq_S]
  unfold i8Psi4s20S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s21` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s21S0 (x : ℝ) : ℝ :=
    (-11 * x ^ 4 - 1735 / 8 * x ^ 3 - 289 / 8 * x - 41 / 12 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 4 +
      7 / 12 * π ^ 2 * x) / x ^ 2 +
    (-111 / 8 - 87 * x + 87 * x ^ 3 + 5 / 12 * π ^ 2 + 111 / 8 * x ^ 4 + 5 / 12 * π ^ 2 * x ^ 4 +
      8 / 3 * π ^ 2 * x + 8 / 3 * π ^ 2 * x ^ 3 + 9 / 2 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (-89 / 4 * x + 65 / 8 * x ^ 4 + 575 / 4 * x ^ 3 + 585 / 8 * x ^ 2 - 9 / 4 * π ^ 2 * x ^ 2 +
      π ^ 2 * x / 6 + π ^ 2 * x ^ 4 / 12 + 7 / 6 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-47 / 4 - 128 * x ^ 3 - 80 * x - 363 / 2 * x ^ 2 - 59 / 4 * x ^ 4 + π ^ 2 / 6 -
      4 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 6 +
      4 / 3 * π ^ 2 * x) / x ^ 2 * hpl [negOne, zero] x +
    (-47 / 4 - 87 * x - 87 * x ^ 3 - 32 * x ^ 2 - 47 / 4 * x ^ 4 + π ^ 2 / 6 -
      4 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 6 +
      4 / 3 * π ^ 2 * x) / x ^ 2 * hpl [zero, negOne] x +
    (-61 / 2 * x ^ 3 - 21 / 2 * x - 3 / 2 * x ^ 4 + 273 / 4 * x ^ 2 -
      7 / 6 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, zero] x +
    (10 + 10 * x ^ 4 + 64 * x + 64 * x ^ 3 + 108 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (5 + 5 * x ^ 4 + 32 * x + 32 * x ^ 3 + 54 * x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (-15 / 2 - 56 * x + 3 * x ^ 2 + 56 * x ^ 3 +
      9 / 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-15 / 2 - 58 * x - 54 * x ^ 2 + 42 * x ^ 3 + 7 / 2 * x ^ 4 -
      2 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-15 / 2 - 60 * x - 27 * x ^ 2 + 28 * x ^ 3 + 5 / 2 * x ^ 4 -
      2 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, zero, negOne] x +
    (-21 * x ^ 3 - 3 * x - 3 / 2 * x ^ 4 + 97 / 2 * x ^ 2) / x ^ 2 * hpl [zero, zero, zero] x +
    (8 - 64 * x ^ 3 - 8 * x ^ 4 + 64 * x) / x ^ 2 * hpl [negOne, negOne, zero, zero] x +
    (6 - 48 * x ^ 3 - 6 * x ^ 4 + 48 * x) / x ^ 2 * hpl [negOne, zero, negOne, zero] x +
    (4 - 32 * x ^ 3 - 4 * x ^ 4 + 32 * x) / x ^ 2 * hpl [negOne, zero, zero, negOne] x +
    (-3 - 24 * x + 3 * x ^ 4 + 24 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero, zero] x +
    (4 - 32 * x ^ 3 - 4 * x ^ 4 + 32 * x) / x ^ 2 * hpl [zero, negOne, negOne, zero] x +
    (2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) / x ^ 2 * hpl [zero, negOne, zero, negOne] x +
    (-3 - 24 * x - 8 * x ^ 2 + 3 * x ^ 4 + 24 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero, zero] x +
    (-3 - 24 * x + 3 * x ^ 4 + 6 * x ^ 2 + 24 * x ^ 3) / x ^ 2 * hpl [zero, zero, negOne, zero] x

theorem continuousOn_i8Psi4s21S0 : ContinuousOn i8Psi4s21S0 (Ioc 0 1) := by
  unfold i8Psi4s21S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -11 * x ^ 4 - 1735 / 8 * x ^ 3 -
    289 / 8 * x - 41 / 12 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 4 +
    7 / 12 * π ^ 2 * x) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -111 / 8 - 87 * x + 87 * x ^ 3 + 5 / 12 * π ^ 2 +
        111 / 8 * x ^ 4 + 5 / 12 * π ^ 2 * x ^ 4 + 8 / 3 * π ^ 2 * x + 8 / 3 * π ^ 2 * x ^ 3 +
        9 / 2 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -89 / 4 * x + 65 / 8 * x ^ 4 + 575 / 4 * x ^ 3 +
        585 / 8 * x ^ 2 - 9 / 4 * π ^ 2 * x ^ 2 + π ^ 2 * x / 6 + π ^ 2 * x ^ 4 / 12 +
        7 / 6 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -47 / 4 - 128 * x ^ 3 - 80 * x - 363 / 2 * x ^ 2 -
        59 / 4 * x ^ 4 + π ^ 2 / 6 - 4 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 6 +
        4 / 3 * π ^ 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -47 / 4 - 87 * x - 87 * x ^ 3 - 32 * x ^ 2 - 47 / 4 * x ^ 4 +
        π ^ 2 / 6 - 4 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 6 +
        4 / 3 * π ^ 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -61 / 2 * x ^ 3 - 21 / 2 * x - 3 / 2 * x ^ 4 +
        273 / 4 * x ^ 2 - 7 / 6 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 10 + 10 * x ^ 4 + 64 * x + 64 * x ^ 3 +
        108 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 5 + 5 * x ^ 4 + 32 * x + 32 * x ^ 3 +
        54 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -15 / 2 - 56 * x + 3 * x ^ 2 + 56 * x ^ 3 +
        9 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -15 / 2 - 58 * x - 54 * x ^ 2 + 42 * x ^ 3 + 7 / 2 * x ^ 4 -
        2 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -15 / 2 - 60 * x - 27 * x ^ 2 + 28 * x ^ 3 + 5 / 2 * x ^ 4 -
        2 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -21 * x ^ 3 - 3 * x - 3 / 2 * x ^ 4 +
        97 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 8 - 64 * x ^ 3 - 8 * x ^ 4 + 64 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 6 - 48 * x ^ 3 - 6 * x ^ 4 + 48 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 4 - 32 * x ^ 3 - 4 * x ^ 4 + 32 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -3 - 24 * x + 3 * x ^ 4 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 4 - 32 * x ^ 3 - 4 * x ^ 4 + 32 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -3 - 24 * x - 8 * x ^ 2 + 3 * x ^ 4 +
        24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -3 - 24 * x + 3 * x ^ 4 + 6 * x ^ 2 +
        24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero])))

/-- Chunk 1 of `i8Psi4s21` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s21S1 (x : ℝ) : ℝ :=
    (-3 - 24 * x + 3 * x ^ 4 + 20 * x ^ 2 + 24 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero, negOne] x +
    (21) * hpl [zero, zero, zero, zero] x +
    (-96) * hpl [zero, negOne, negOne, zero, zero] x +
    (-72) * hpl [zero, negOne, zero, negOne, zero] x +
    (-48) * hpl [zero, negOne, zero, zero, negOne] x +
    (36) * hpl [zero, negOne, zero, zero, zero] x +
    (-48) * hpl [zero, zero, negOne, negOne, zero] x +
    (-24) * hpl [zero, zero, negOne, zero, negOne] x +
    (36) * hpl [zero, zero, negOne, zero, zero] x +
    (36) * hpl [zero, zero, zero, negOne, zero] x +
    (36) * hpl [zero, zero, zero, zero, negOne] x

theorem continuousOn_i8Psi4s21S1 : ContinuousOn i8Psi4s21S1 (Ioc 0 1) := by
  unfold i8Psi4s21S1
  exact ((((((((((((i13_cont_coef (p := fun x => -3 - 24 * x + 3 * x ^ 4 + 20 * x ^ 2 +
    24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, negOne])))

theorem i8Psi4s21_eq_S (x : ℝ) : i8Psi4s21 x = i8Psi4s21S0 x + i8Psi4s21S1 x := by
  unfold i8Psi4s21 i8Psi4s21S0 i8Psi4s21S1 i8Psi4s21N0 i8Psi4s21N1 i8Psi4s21N2 i8Psi4s21N3
    i8Psi4s21N4 i8Psi4s21W i8Psi4s21N1c0 i8Psi4s21N1c1 i8Psi4s21N3c0 i8Psi4s21N3c1 i8Psi4s21N4c0
    i8Psi4s21N4c1
  ring

theorem continuousOn_i8Psi4s21 : ContinuousOn i8Psi4s21 (Ioc 0 1) := by
  rw [show i8Psi4s21 = fun x => i8Psi4s21S0 x + i8Psi4s21S1 x from funext i8Psi4s21_eq_S]
  exact (continuousOn_i8Psi4s21S0.add continuousOn_i8Psi4s21S1)

theorem i8Psi4s21_one : i8Psi4s21 1 = -264 + 63 * zeta3 + 66 * zeta5 - 77 / 360 * π ^ 4 +
    299 / 24 * π ^ 2 - 8 * π ^ 2 * zeta3 := by
  rw [i8Psi4s21_eq_S]
  unfold i8Psi4s21S0 i8Psi4s21S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_negOne_zero_at_one, hpl_negOne_zero_negOne_at_one,
    hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_zero_zero_at_one, hpl_negOne_negOne_zero_zero_at_one,
    hpl_negOne_zero_negOne_zero_at_one, hpl_negOne_zero_zero_negOne_at_one,
    hpl_negOne_zero_zero_zero_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_zero_negOne_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_at_one,
    hpl_zero_zero_zero_zero_at_one, hpl_zero_negOne_negOne_zero_zero_at_one,
    hpl_zero_negOne_zero_negOne_zero_at_one, hpl_zero_negOne_zero_zero_negOne_at_one,
    hpl_zero_negOne_zero_zero_zero_at_one, hpl_zero_zero_negOne_negOne_zero_at_one,
    hpl_zero_zero_negOne_zero_negOne_at_one, hpl_zero_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s22` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s22S0 (x : ℝ) : ℝ :=
    (-16 * x ^ 4 + 32 * x + 32 * x ^ 3 - 8 * x * zeta3 - 8 * zeta3 * x ^ 3 - 4 * zeta3 * x ^ 4 -
      4 / 3 * π ^ 2 * x - 4 / 3 * π ^ 2 * x ^ 3 - 2 / 3 * π ^ 2 * x ^ 4 - x * π ^ 2 ^ 2 / 20 -
      π ^ 2 ^ 2 * x ^ 3 / 20 - π ^ 2 ^ 2 * x ^ 4 / 40) / x ^ 2 +
    (32 + 8 * zeta3 + π ^ 2 ^ 2 / 20 + 4 / 3 * π ^ 2) * hpl [zero] x

theorem continuousOn_i8Psi4s22S0 : ContinuousOn i8Psi4s22S0 (Ioc 0 1) := by
  unfold i8Psi4s22S0
  exact ((i13_cont_coef (p := fun x => -16 * x ^ 4 + 32 * x + 32 * x ^ 3 - 8 * x * zeta3 -
    8 * zeta3 * x ^ 3 - 4 * zeta3 * x ^ 4 - 4 / 3 * π ^ 2 * x - 4 / 3 * π ^ 2 * x ^ 3 -
    2 / 3 * π ^ 2 * x ^ 4 - x * π ^ 2 ^ 2 / 20 - π ^ 2 ^ 2 * x ^ 3 / 20 -
    π ^ 2 ^ 2 * x ^ 4 / 40) (by fun_prop)).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [])))

theorem i8Psi4s22_eq_S (x : ℝ) : i8Psi4s22 x = i8Psi4s22S0 x := by
  unfold i8Psi4s22 i8Psi4s22S0 i8Psi4s22N0 i8Psi4s22N1 i8Psi4s22N2 i8Psi4s22N3 i8Psi4s22N4
    i8Psi4s22W
  ring

theorem continuousOn_i8Psi4s22 : ContinuousOn i8Psi4s22 (Ioc 0 1) := by
  rw [show i8Psi4s22 = fun x => i8Psi4s22S0 x from funext i8Psi4s22_eq_S]
  exact continuousOn_i8Psi4s22S0

theorem i8Psi4s22_one : i8Psi4s22 1 = 48 - 20 * zeta3 - 10 / 3 * π ^ 2 - π ^ 4 / 8 := by
  rw [i8Psi4s22_eq_S]
  unfold i8Psi4s22S0
  rw [hpl_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s23` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s23S0 (x : ℝ) : ℝ :=
    (-16 * x ^ 3 - 4 * x ^ 4 + 16 * x + zeta3 * x ^ 4 - 4 * x * zeta3 + 4 * zeta3 * x ^ 3 -
      2 / 3 * π ^ 2 * x + π ^ 2 * x ^ 4 / 6 + 2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 +
    (8 * x ^ 4 + 16 * x + 16 * x ^ 3 - 4 * x * zeta3 - 4 * zeta3 * x ^ 3 - 2 * zeta3 * x ^ 4 -
      2 / 3 * π ^ 2 * x - 2 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 3) / x ^ 2 * hpl [zero] x +
    (-16 + 4 * zeta3 + 2 / 3 * π ^ 2) * hpl [zero, zero] x

theorem continuousOn_i8Psi4s23S0 : ContinuousOn i8Psi4s23S0 (Ioc 0 1) := by
  unfold i8Psi4s23S0
  exact (((i13_cont_coef (p := fun x => -16 * x ^ 3 - 4 * x ^ 4 + 16 * x + zeta3 * x ^ 4 -
    4 * x * zeta3 + 4 * zeta3 * x ^ 3 - 2 / 3 * π ^ 2 * x + π ^ 2 * x ^ 4 / 6 +
    2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 8 * x ^ 4 + 16 * x + 16 * x ^ 3 - 4 * x * zeta3 -
        4 * zeta3 * x ^ 3 - 2 * zeta3 * x ^ 4 - 2 / 3 * π ^ 2 * x - 2 / 3 * π ^ 2 * x ^ 3 -
        π ^ 2 * x ^ 4 / 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero])))

theorem i8Psi4s23_eq_S (x : ℝ) : i8Psi4s23 x = i8Psi4s23S0 x := by
  unfold i8Psi4s23 i8Psi4s23S0 i8Psi4s23N0 i8Psi4s23N1 i8Psi4s23N2 i8Psi4s23N3 i8Psi4s23N4
    i8Psi4s23W
  ring

theorem continuousOn_i8Psi4s23 : ContinuousOn i8Psi4s23 (Ioc 0 1) := by
  rw [show i8Psi4s23 = fun x => i8Psi4s23S0 x from funext i8Psi4s23_eq_S]
  exact continuousOn_i8Psi4s23S0

theorem i8Psi4s23_one : i8Psi4s23 1 = -4 + zeta3 + π ^ 2 / 6 := by
  rw [i8Psi4s23_eq_S]
  unfold i8Psi4s23S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s24` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s24S0 (x : ℝ) : ℝ :=
    (-4 * zeta3 * x ^ 3 - 2 * zeta3 * x ^ 4 - 2 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 3) / x ^ 2 +
    (2 * π ^ 2 * x ^ 2 + 4 * zeta3 * x ^ 4 + 8 * x * zeta3 + 8 * zeta3 * x ^ 3 +
      12 * zeta3 * x ^ 2 + 2 / 3 * π ^ 2 * x ^ 4 + 4 / 3 * π ^ 2 * x +
      4 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (-8 * zeta3 - 4 / 3 * π ^ 2) * hpl [zero] x +
    (-8 * zeta3 - 4 / 3 * π ^ 2) * hpl [zero, negOne] x

theorem continuousOn_i8Psi4s24S0 : ContinuousOn i8Psi4s24S0 (Ioc 0 1) := by
  unfold i8Psi4s24S0
  exact ((((i13_cont_coef (p := fun x => -4 * zeta3 * x ^ 3 - 2 * zeta3 * x ^ 4 -
    2 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 2 * π ^ 2 * x ^ 2 + 4 * zeta3 * x ^ 4 + 8 * x * zeta3 +
        8 * zeta3 * x ^ 3 + 12 * zeta3 * x ^ 2 + 2 / 3 * π ^ 2 * x ^ 4 + 4 / 3 * π ^ 2 * x +
        4 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne])))

theorem i8Psi4s24_eq_S (x : ℝ) : i8Psi4s24 x = i8Psi4s24S0 x := by
  unfold i8Psi4s24 i8Psi4s24S0 i8Psi4s24N0 i8Psi4s24N1 i8Psi4s24N2 i8Psi4s24N3 i8Psi4s24N4
    i8Psi4s24W
  ring

theorem continuousOn_i8Psi4s24 : ContinuousOn i8Psi4s24 (Ioc 0 1) := by
  rw [show i8Psi4s24 = fun x => i8Psi4s24S0 x from funext i8Psi4s24_eq_S]
  exact continuousOn_i8Psi4s24S0

theorem i8Psi4s24_one : i8Psi4s24 1 = -π ^ 2 - 6 * zeta3 - π ^ 4 / 9 + 32 * Real.log 2 * zeta3 -
    2 / 3 * π ^ 2 * zeta3 + 16 / 3 * Real.log 2 * π ^ 2 := by
  rw [i8Psi4s24_eq_S]
  unfold i8Psi4s24S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s25` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s25S0 (x : ℝ) : ℝ :=
    (x ^ 4 + 8 * x + 8 * x ^ 3 - π ^ 2 * x / 3 - π ^ 2 * x ^ 3 / 3 - π ^ 2 * x ^ 4 / 24) / x ^ 2 +
    (-8 * x ^ 3 - 2 * x ^ 4 + 8 * x - π ^ 2 * x / 3 + π ^ 2 * x ^ 3 / 3 +
      π ^ 2 * x ^ 4 / 12) / x ^ 2 * hpl [zero] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 3 - π ^ 2 * x / 3 - π ^ 2 * x ^ 3 / 3 -
      π ^ 2 * x ^ 4 / 6) / x ^ 2 * hpl [zero, zero] x +
    (-8 + π ^ 2 / 3) * hpl [zero, zero, zero] x

theorem continuousOn_i8Psi4s25S0 : ContinuousOn i8Psi4s25S0 (Ioc 0 1) := by
  unfold i8Psi4s25S0
  exact ((((i13_cont_coef (p := fun x => x ^ 4 + 8 * x + 8 * x ^ 3 - π ^ 2 * x / 3 -
    π ^ 2 * x ^ 3 / 3 - π ^ 2 * x ^ 4 / 24) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 3 - 2 * x ^ 4 + 8 * x - π ^ 2 * x / 3 +
        π ^ 2 * x ^ 3 / 3 + π ^ 2 * x ^ 4 / 12) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 3 - π ^ 2 * x / 3 -
        π ^ 2 * x ^ 3 / 3 - π ^ 2 * x ^ 4 / 6) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero])))

theorem i8Psi4s25_eq_S (x : ℝ) : i8Psi4s25 x = i8Psi4s25S0 x := by
  unfold i8Psi4s25 i8Psi4s25S0 i8Psi4s25N0 i8Psi4s25N1 i8Psi4s25N2 i8Psi4s25N3 i8Psi4s25N4
    i8Psi4s25W
  ring

theorem continuousOn_i8Psi4s25 : ContinuousOn i8Psi4s25 (Ioc 0 1) := by
  rw [show i8Psi4s25 = fun x => i8Psi4s25S0 x from funext i8Psi4s25_eq_S]
  exact continuousOn_i8Psi4s25S0

theorem i8Psi4s25_one : i8Psi4s25 1 = 17 - 17 / 24 * π ^ 2 := by
  rw [i8Psi4s25_eq_S]
  unfold i8Psi4s25S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s26` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s26S0 (x : ℝ) : ℝ :=
    (-8 * x ^ 3 - 2 * x ^ 4 + π ^ 2 * x ^ 3 / 3 + π ^ 2 * x ^ 4 / 12) / x ^ 2 +
    (4 * x ^ 4 + 8 * x ^ 3 - π ^ 2 * x ^ 3 / 3 - π ^ 2 * x ^ 4 / 6) / x ^ 2 * hpl [zero] x +
    (-24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 8 * x ^ 4 + π ^ 2 * x ^ 2 + π ^ 2 * x ^ 4 / 3 +
      2 / 3 * π ^ 2 * x + 2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (16 - 2 / 3 * π ^ 2) * hpl [zero, zero] x +
    (16 - 2 / 3 * π ^ 2) * hpl [zero, negOne, zero] x

theorem continuousOn_i8Psi4s26S0 : ContinuousOn i8Psi4s26S0 (Ioc 0 1) := by
  unfold i8Psi4s26S0
  exact (((((i13_cont_coef (p := fun x => -8 * x ^ 3 - 2 * x ^ 4 + π ^ 2 * x ^ 3 / 3 +
    π ^ 2 * x ^ 4 / 12) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x ^ 3 - π ^ 2 * x ^ 3 / 3 -
        π ^ 2 * x ^ 4 / 6) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 8 * x ^ 4 +
        π ^ 2 * x ^ 2 + π ^ 2 * x ^ 4 / 3 + 2 / 3 * π ^ 2 * x +
        2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero])))

theorem i8Psi4s26_eq_S (x : ℝ) : i8Psi4s26 x = i8Psi4s26S0 x := by
  unfold i8Psi4s26 i8Psi4s26S0 i8Psi4s26N0 i8Psi4s26N1 i8Psi4s26N2 i8Psi4s26N3 i8Psi4s26N4
    i8Psi4s26W
  ring

theorem continuousOn_i8Psi4s26 : ContinuousOn i8Psi4s26 (Ioc 0 1) := by
  rw [show i8Psi4s26 = fun x => i8Psi4s26S0 x from funext i8Psi4s26_eq_S]
  exact continuousOn_i8Psi4s26S0

theorem i8Psi4s26_one : i8Psi4s26 1 = -10 - 24 * zeta3 - 2 / 9 * π ^ 4 + 23 / 4 * π ^ 2 +
    π ^ 2 * zeta3 := by
  rw [i8Psi4s26_eq_S]
  unfold i8Psi4s26S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one, hpl_zero_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s27` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s27S0 (x : ℝ) : ℝ :=
    (-π ^ 2 * x ^ 3 / 3 - π ^ 2 * x ^ 4 / 6) / x ^ 2 +
    (π ^ 2 * x ^ 2 / 3 + π ^ 2 * x ^ 4 / 3 + 2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (-2 * π ^ 2 * x ^ 2 - 4 / 3 * π ^ 2 * x - 4 / 3 * π ^ 2 * x ^ 3 -
      2 / 3 * π ^ 2 * x ^ 4) / x ^ 2 * hpl [negOne, negOne] x +
    (4 / 3 * π ^ 2) * hpl [zero, negOne] x +
    (4 / 3 * π ^ 2) * hpl [zero, negOne, negOne] x

theorem continuousOn_i8Psi4s27S0 : ContinuousOn i8Psi4s27S0 (Ioc 0 1) := by
  unfold i8Psi4s27S0
  exact (((((i13_cont_coef (p := fun x => -π ^ 2 * x ^ 3 / 3 - π ^ 2 * x ^ 4 / 6) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => π ^ 2 * x ^ 2 / 3 + π ^ 2 * x ^ 4 / 3 +
        2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -2 * π ^ 2 * x ^ 2 - 4 / 3 * π ^ 2 * x -
        4 / 3 * π ^ 2 * x ^ 3 - 2 / 3 * π ^ 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne])))

theorem i8Psi4s27_eq_S (x : ℝ) : i8Psi4s27 x = i8Psi4s27S0 x := by
  unfold i8Psi4s27 i8Psi4s27S0 i8Psi4s27N0 i8Psi4s27N1 i8Psi4s27N2 i8Psi4s27N3 i8Psi4s27N4
    i8Psi4s27W
  ring

theorem continuousOn_i8Psi4s27 : ContinuousOn i8Psi4s27 (Ioc 0 1) := by
  rw [show i8Psi4s27 = fun x => i8Psi4s27S0 x from funext i8Psi4s27_eq_S]
  exact continuousOn_i8Psi4s27S0

theorem i8Psi4s27_one : i8Psi4s27 1 = -π ^ 2 / 2 + π ^ 4 / 9 - 8 / 3 * π ^ 2 * Real.log 2 ^ 2 +
    π ^ 2 * zeta3 / 6 + 4 / 3 * Real.log 2 * π ^ 2 := by
  rw [i8Psi4s27_eq_S]
  unfold i8Psi4s27S0
  rw [hpl_negOne_at_one, hpl_negOne_negOne_at_one, hpl_zero_negOne_at_one,
    hpl_zero_negOne_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s28` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s28S0 (x : ℝ) : ℝ :=
    (π ^ 2 * x ^ 3 / 2 + π ^ 2 * x ^ 4 / 12) / x ^ 2 +
    (-2 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 6 + π ^ 2 * x ^ 2 / 6 +
      2 / 3 * π ^ 2 * x) / x ^ 2 * hpl [negOne] x +
    (-2 / 3 * π ^ 2) * hpl [zero] x +
    (π ^ 2 * x ^ 4 / 3 + 2 / 3 * π ^ 2 * x + 2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (-2 / 3 * π ^ 2) * hpl [zero, zero, negOne] x

theorem continuousOn_i8Psi4s28S0 : ContinuousOn i8Psi4s28S0 (Ioc 0 1) := by
  unfold i8Psi4s28S0
  exact (((((i13_cont_coef (p := fun x => π ^ 2 * x ^ 3 / 2 + π ^ 2 * x ^ 4 / 12) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -2 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 6 +
        π ^ 2 * x ^ 2 / 6 + 2 / 3 * π ^ 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => π ^ 2 * x ^ 4 / 3 + 2 / 3 * π ^ 2 * x +
        2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne])))

theorem i8Psi4s28_eq_S (x : ℝ) : i8Psi4s28 x = i8Psi4s28S0 x := by
  unfold i8Psi4s28 i8Psi4s28S0 i8Psi4s28N0 i8Psi4s28N1 i8Psi4s28N2 i8Psi4s28N3 i8Psi4s28N4
    i8Psi4s28W
  ring

theorem continuousOn_i8Psi4s28 : ContinuousOn i8Psi4s28 (Ioc 0 1) := by
  rw [show i8Psi4s28 = fun x => i8Psi4s28S0 x from funext i8Psi4s28_eq_S]
  exact continuousOn_i8Psi4s28S0

theorem i8Psi4s28_one : i8Psi4s28 1 = 5 / 36 * π ^ 4 + 7 / 12 * π ^ 2 - π ^ 2 * zeta3 / 2 := by
  rw [i8Psi4s28_eq_S]
  unfold i8Psi4s28S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_zero_negOne_at_one, hpl_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s29` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s29S0 (x : ℝ) : ℝ :=
    (-7 / 2 * x ^ 3 - x ^ 4 / 8) / x ^ 2 +
    (x ^ 4 / 4 + 7 / 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-4 * x - 4 * x ^ 3 - 15 / 2 * x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [negOne, zero] x +
    (4) * hpl [zero, zero] x +
    (x ^ 4 - 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-4 * x - 4 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne, zero] x +
    (4) * hpl [zero, zero, zero, negOne, zero] x

theorem continuousOn_i8Psi4s29S0 : ContinuousOn i8Psi4s29S0 (Ioc 0 1) := by
  unfold i8Psi4s29S0
  exact (((((((i13_cont_coef (p := fun x => -7 / 2 * x ^ 3 - x ^ 4 / 8) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 4 + 7 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -4 * x - 4 * x ^ 3 - 15 / 2 * x ^ 2 -
        x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x - 4 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne, zero])))

theorem i8Psi4s29_eq_S (x : ℝ) : i8Psi4s29 x = i8Psi4s29S0 x := by
  unfold i8Psi4s29 i8Psi4s29S0 i8Psi4s29N0 i8Psi4s29N1 i8Psi4s29N2 i8Psi4s29N3 i8Psi4s29N4
    i8Psi4s29W
  ring

theorem continuousOn_i8Psi4s29 : ContinuousOn i8Psi4s29 (Ioc 0 1) := by
  rw [show i8Psi4s29 = fun x => i8Psi4s29S0 x from funext i8Psi4s29_eq_S]
  exact continuousOn_i8Psi4s29S0

theorem i8Psi4s29_one : i8Psi4s29 1 = -29 / 8 - 15 * zeta5 - 3 / 2 * zeta3 + 4 / 3 * π ^ 2 +
    7 / 24 * π ^ 4 := by
  rw [i8Psi4s29_eq_S]
  unfold i8Psi4s29S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s30` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s30S0 (x : ℝ) : ℝ :=
    (3 * x ^ 3 + x ^ 4 / 4) / x ^ 2 +
    (-3 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero] x +
    (x ^ 4 + 3 * x ^ 2 + 4 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (-4 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne, zero] x +
    (-8) * hpl [zero, zero, negOne, zero] x +
    (-8) * hpl [zero, negOne, zero, negOne, zero] x

theorem continuousOn_i8Psi4s30S0 : ContinuousOn i8Psi4s30S0 (Ioc 0 1) := by
  unfold i8Psi4s30S0
  exact (((((((i13_cont_coef (p := fun x => 3 * x ^ 3 + x ^ 4 / 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -3 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 3 * x ^ 2 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 3 + 12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne, zero])))

theorem i8Psi4s30_eq_S (x : ℝ) : i8Psi4s30 x = i8Psi4s30S0 x := by
  unfold i8Psi4s30 i8Psi4s30S0 i8Psi4s30N0 i8Psi4s30N1 i8Psi4s30N2 i8Psi4s30N3 i8Psi4s30N4
    i8Psi4s30W
  ring

theorem continuousOn_i8Psi4s30 : ContinuousOn i8Psi4s30 (Ioc 0 1) := by
  rw [show i8Psi4s30 = fun x => i8Psi4s30S0 x from funext i8Psi4s30_eq_S]
  exact continuousOn_i8Psi4s30S0

theorem i8Psi4s30_one : i8Psi4s30 1 = 13 / 4 + 9 * zeta3 + 46 * zeta5 + 128 * Li 4 (1 / 2) -
    89 / 90 * π ^ 4 - 2 / 3 * π ^ 2 + 16 / 3 * Real.log 2 ^ 4 + 64 * Real.log 2 * zeta3 -
    16 / 3 * π ^ 2 * Real.log 2 ^ 2 - 11 / 3 * π ^ 2 * zeta3 := by
  rw [i8Psi4s30_eq_S]
  unfold i8Psi4s30S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_negOne_zero_negOne_zero_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_negOne_zero_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s31` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s31S0 (x : ℝ) : ℝ :=
    (-2 * x ^ 3 - x ^ 4 / 2) / x ^ 2 +
    (x ^ 4 + 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-4 * x ^ 3 - 2 * x ^ 2 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (4 * x ^ 2 + 4 * x ^ 4 + 8 * x ^ 3) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (-24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 8 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, negOne, zero] x +
    (16) * hpl [zero, negOne, negOne, zero] x +
    (16) * hpl [zero, negOne, negOne, negOne, zero] x

theorem continuousOn_i8Psi4s31S0 : ContinuousOn i8Psi4s31S0 (Ioc 0 1) := by
  unfold i8Psi4s31S0
  exact (((((((i13_cont_coef (p := fun x => -2 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 3 - 2 * x ^ 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 2 + 4 * x ^ 4 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, negOne, zero])))

theorem i8Psi4s31_eq_S (x : ℝ) : i8Psi4s31 x = i8Psi4s31S0 x := by
  unfold i8Psi4s31 i8Psi4s31S0 i8Psi4s31N0 i8Psi4s31N1 i8Psi4s31N2 i8Psi4s31N3 i8Psi4s31N4
    i8Psi4s31W
  ring

theorem continuousOn_i8Psi4s31 : ContinuousOn i8Psi4s31 (Ioc 0 1) := by
  rw [show i8Psi4s31 = fun x => i8Psi4s31S0 x from funext i8Psi4s31_eq_S]
  exact continuousOn_i8Psi4s31S0

theorem i8Psi4s31_one : i8Psi4s31 1 = -5 / 2 - 64 * Li 4 (1 / 2) + 2 * zeta3 - 59 / 2 * zeta5 -
    8 / 3 * Real.log 2 ^ 4 + 2 / 3 * π ^ 2 + 59 / 90 * π ^ 4 - 64 * Real.log 2 * zeta3 -
    4 / 3 * Real.log 2 * π ^ 2 + 5 / 2 * π ^ 2 * zeta3 + 16 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s31_eq_S]
  unfold i8Psi4s31S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_negOne_negOne_negOne_zero_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_negOne_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s32` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s32S0 (x : ℝ) : ℝ :=
    (5 * x ^ 3 + x ^ 4 / 4) / x ^ 2 +
    (-5 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero] x +
    (x ^ 4 + 5 * x ^ 2 + 6 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (-8 * x ^ 3 - 2 * x ^ 4 + 2 * x ^ 2 + 8 * x) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (-8) * hpl [zero, negOne, zero] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, negOne, negOne, zero] x +
    (-8) * hpl [zero, zero, negOne, negOne, zero] x

theorem continuousOn_i8Psi4s32S0 : ContinuousOn i8Psi4s32S0 (Ioc 0 1) := by
  unfold i8Psi4s32S0
  exact (((((((i13_cont_coef (p := fun x => 5 * x ^ 3 + x ^ 4 / 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -5 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 5 * x ^ 2 + 6 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 3 - 2 * x ^ 4 + 2 * x ^ 2 + 8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne, zero])))

theorem i8Psi4s32_eq_S (x : ℝ) : i8Psi4s32 x = i8Psi4s32S0 x := by
  unfold i8Psi4s32 i8Psi4s32S0 i8Psi4s32N0 i8Psi4s32N1 i8Psi4s32N2 i8Psi4s32N3 i8Psi4s32N4
    i8Psi4s32W
  ring

theorem continuousOn_i8Psi4s32 : ContinuousOn i8Psi4s32 (Ioc 0 1) := by
  rw [show i8Psi4s32 = fun x => i8Psi4s32S0 x from funext i8Psi4s32_eq_S]
  exact continuousOn_i8Psi4s32S0

theorem i8Psi4s32_one : i8Psi4s32 1 = 21 / 4 - π ^ 2 + 12 * zeta3 - 23 / 2 * zeta5 -
    5 / 72 * π ^ 4 + 7 / 6 * π ^ 2 * zeta3 := by
  rw [i8Psi4s32_eq_S]
  unfold i8Psi4s32S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_zero_negOne_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s33` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s33S0 (x : ℝ) : ℝ :=
    (2 * x + 2 * x ^ 3 + x ^ 4 / 16) / x ^ 2 +
    (-2 * x ^ 3 + 2 * x - x ^ 4 / 8) / x ^ 2 * hpl [zero] x +
    (2 * x + 2 * x ^ 3 + x ^ 4 / 4) / x ^ 2 * hpl [zero, zero] x +
    (-2 * x ^ 3 + 2 * x - x ^ 4 / 2) / x ^ 2 * hpl [zero, zero, zero] x +
    (x ^ 4 + 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero, zero] x +
    (-2) * hpl [zero, zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s33S0 : ContinuousOn i8Psi4s33S0 (Ioc 0 1) := by
  unfold i8Psi4s33S0
  exact ((((((i13_cont_coef (p := fun x => 2 * x + 2 * x ^ 3 + x ^ 4 / 16) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 3 + 2 * x - x ^ 4 / 8) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 2 * x + 2 * x ^ 3 + x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 3 + 2 * x - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, zero])))

theorem i8Psi4s33_eq_S (x : ℝ) : i8Psi4s33 x = i8Psi4s33S0 x := by
  unfold i8Psi4s33 i8Psi4s33S0 i8Psi4s33N0 i8Psi4s33N1 i8Psi4s33N2 i8Psi4s33N3 i8Psi4s33N4
    i8Psi4s33W
  ring

theorem continuousOn_i8Psi4s33 : ContinuousOn i8Psi4s33 (Ioc 0 1) := by
  rw [show i8Psi4s33 = fun x => i8Psi4s33S0 x from funext i8Psi4s33_eq_S]
  exact continuousOn_i8Psi4s33S0

theorem i8Psi4s33_one : i8Psi4s33 1 = 65 / 16 := by
  have h5 : hpl [zero, zero, zero, zero, zero] 1 = 0 := by
    rw [hpl_of_allZero (by decide)]
    simp
  rw [i8Psi4s33_eq_S]
  unfold i8Psi4s33S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_zero_zero_at_one, h5]
  norm_num

/-- Chunk 0 of `i8Psi4s34` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s34S0 (x : ℝ) : ℝ :=
    (-2 * x ^ 3 - x ^ 4 / 8) / x ^ 2 +
    (2 * x ^ 3 + x ^ 4 / 4) / x ^ 2 * hpl [zero] x +
    (-2 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero, zero] x +
    (x ^ 4 + 2 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero] x +
    (-6 * x ^ 2 - 4 * x - 4 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero, zero] x +
    (4) * hpl [zero, zero, zero, zero] x +
    (4) * hpl [zero, negOne, zero, zero, zero] x

theorem continuousOn_i8Psi4s34S0 : ContinuousOn i8Psi4s34S0 (Ioc 0 1) := by
  unfold i8Psi4s34S0
  exact (((((((i13_cont_coef (p := fun x => -2 * x ^ 3 - x ^ 4 / 8) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 3 + x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -6 * x ^ 2 - 4 * x - 4 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero, zero])))

theorem i8Psi4s34_eq_S (x : ℝ) : i8Psi4s34 x = i8Psi4s34S0 x := by
  unfold i8Psi4s34 i8Psi4s34S0 i8Psi4s34N0 i8Psi4s34N1 i8Psi4s34N2 i8Psi4s34N3 i8Psi4s34N4
    i8Psi4s34W
  ring

theorem continuousOn_i8Psi4s34 : ContinuousOn i8Psi4s34 (Ioc 0 1) := by
  rw [show i8Psi4s34 = fun x => i8Psi4s34S0 x from funext i8Psi4s34_eq_S]
  exact continuousOn_i8Psi4s34S0

theorem i8Psi4s34_one : i8Psi4s34 1 = -17 / 8 - 15 * zeta5 + 7 / 45 * π ^ 4 := by
  rw [i8Psi4s34_eq_S]
  unfold i8Psi4s34S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_negOne_zero_zero_zero_at_one, hpl_zero_zero_zero_zero_at_one,
    hpl_zero_negOne_zero_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s35` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s35S0 (x : ℝ) : ℝ :=
    (-3 * x ^ 3 - x ^ 4 / 8) / x ^ 2 +
    (3 * x ^ 3 + x ^ 4 / 4) / x ^ 2 * hpl [zero] x +
    (-3 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero, zero] x +
    (x ^ 4 - x ^ 2 - 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero] x +
    (4) * hpl [zero, zero, zero] x +
    (-4 * x - 4 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero, zero] x +
    (4) * hpl [zero, zero, negOne, zero, zero] x

theorem continuousOn_i8Psi4s35S0 : ContinuousOn i8Psi4s35S0 (Ioc 0 1) := by
  unfold i8Psi4s35S0
  exact (((((((i13_cont_coef (p := fun x => -3 * x ^ 3 - x ^ 4 / 8) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 3 * x ^ 3 + x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -3 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - x ^ 2 - 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x - 4 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, zero])))

theorem i8Psi4s35_eq_S (x : ℝ) : i8Psi4s35 x = i8Psi4s35S0 x := by
  unfold i8Psi4s35 i8Psi4s35S0 i8Psi4s35N0 i8Psi4s35N1 i8Psi4s35N2 i8Psi4s35N3 i8Psi4s35N4
    i8Psi4s35W
  ring

theorem continuousOn_i8Psi4s35 : ContinuousOn i8Psi4s35 (Ioc 0 1) := by
  rw [show i8Psi4s35 = fun x => i8Psi4s35S0 x from funext i8Psi4s35_eq_S]
  exact continuousOn_i8Psi4s35S0

theorem i8Psi4s35_one : i8Psi4s35 1 = -25 / 8 - 7 / 24 * π ^ 4 + 45 / 2 * zeta5 := by
  rw [i8Psi4s35_eq_S]
  unfold i8Psi4s35S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_zero_negOne_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s36` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s36S0 (x : ℝ) : ℝ :=
    (2 * x ^ 3 + x ^ 4 / 4) / x ^ 2 +
    (-2 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero] x +
    (x ^ 4 + 2 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-4 * x ^ 3 - 2 * x ^ 2 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero, zero] x +
    (-8) * hpl [zero, negOne, zero, zero] x +
    (-8) * hpl [zero, negOne, negOne, zero, zero] x

theorem continuousOn_i8Psi4s36S0 : ContinuousOn i8Psi4s36S0 (Ioc 0 1) := by
  unfold i8Psi4s36S0
  exact (((((((i13_cont_coef (p := fun x => 2 * x ^ 3 + x ^ 4 / 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 3 - 2 * x ^ 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 3 + 12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero, zero])))

theorem i8Psi4s36_eq_S (x : ℝ) : i8Psi4s36 x = i8Psi4s36S0 x := by
  unfold i8Psi4s36 i8Psi4s36S0 i8Psi4s36N0 i8Psi4s36N1 i8Psi4s36N2 i8Psi4s36N3 i8Psi4s36N4
    i8Psi4s36W
  ring

theorem continuousOn_i8Psi4s36 : ContinuousOn i8Psi4s36 (Ioc 0 1) := by
  rw [show i8Psi4s36 = fun x => i8Psi4s36S0 x from funext i8Psi4s36_eq_S]
  exact continuousOn_i8Psi4s36S0

theorem i8Psi4s36_one : i8Psi4s36 1 = 9 / 4 - 64 * Li 4 (1 / 2) - 6 * zeta3 - 23 / 2 * zeta5 -
    8 / 3 * Real.log 2 ^ 4 + 13 / 30 * π ^ 4 - 32 * Real.log 2 * zeta3 + 2 / 3 * π ^ 2 * zeta3 +
    8 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s36_eq_S]
  unfold i8Psi4s36S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one,
    hpl_negOne_negOne_zero_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_negOne_negOne_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s37` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s37S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 + 6 * x ^ 3) / x ^ 2 +
    (-x ^ 4 - 6 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-8 * x - 2 * x ^ 2 + 2 * x ^ 4 + 8 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (8) * hpl [zero, zero] x +
    (-8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero] x +
    (8) * hpl [zero, zero, negOne, zero] x

theorem continuousOn_i8Psi4s37S0 : ContinuousOn i8Psi4s37S0 (Ioc 0 1) := by
  unfold i8Psi4s37S0
  exact ((((((i13_cont_coef (p := fun x => x ^ 4 / 2 + 6 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 6 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -8 * x - 2 * x ^ 2 + 2 * x ^ 4 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero])))

theorem i8Psi4s37_eq_S (x : ℝ) : i8Psi4s37 x = i8Psi4s37S0 x := by
  unfold i8Psi4s37 i8Psi4s37S0 i8Psi4s37N0 i8Psi4s37N1 i8Psi4s37N2 i8Psi4s37N3 i8Psi4s37N4
    i8Psi4s37W
  ring

theorem continuousOn_i8Psi4s37 : ContinuousOn i8Psi4s37 (Ioc 0 1) := by
  rw [show i8Psi4s37 = fun x => i8Psi4s37S0 x from funext i8Psi4s37_eq_S]
  exact continuousOn_i8Psi4s37S0

theorem i8Psi4s37_one : i8Psi4s37 1 = 13 / 2 + 30 * zeta3 - 7 / 30 * π ^ 4 := by
  rw [i8Psi4s37_eq_S]
  unfold i8Psi4s37S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s38` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s38S0 (x : ℝ) : ℝ :=
    (-x ^ 4 - 4 * x ^ 3) / x ^ 2 +
    (2 * x ^ 4 + 4 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-8 * x ^ 3 - 4 * x ^ 2 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (8 * x ^ 4 + 16 * x + 16 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (-16) * hpl [zero, negOne, zero] x +
    (-16) * hpl [zero, negOne, negOne, zero] x

theorem continuousOn_i8Psi4s38S0 : ContinuousOn i8Psi4s38S0 (Ioc 0 1) := by
  unfold i8Psi4s38S0
  exact ((((((i13_cont_coef (p := fun x => -x ^ 4 - 4 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -8 * x ^ 3 - 4 * x ^ 2 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 8 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero])))

theorem i8Psi4s38_eq_S (x : ℝ) : i8Psi4s38 x = i8Psi4s38S0 x := by
  unfold i8Psi4s38 i8Psi4s38S0 i8Psi4s38N0 i8Psi4s38N1 i8Psi4s38N2 i8Psi4s38N3 i8Psi4s38N4
    i8Psi4s38W
  ring

theorem continuousOn_i8Psi4s38 : ContinuousOn i8Psi4s38 (Ioc 0 1) := by
  rw [show i8Psi4s38 = fun x => i8Psi4s38S0 x from funext i8Psi4s38_eq_S]
  exact continuousOn_i8Psi4s38S0

theorem i8Psi4s38_one : i8Psi4s38 1 = -5 + 32 * zeta3 + π ^ 4 / 18 + 4 / 3 * π ^ 2 -
    16 / 3 * Real.log 2 * π ^ 2 := by
  rw [i8Psi4s38_eq_S]
  unfold i8Psi4s38S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_negOne_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s39` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s39S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 + 4 * x ^ 3) / x ^ 2 +
    (-x ^ 4 - 4 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (2 * x ^ 4 + 4 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (-12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (8) * hpl [zero, zero, zero] x +
    (8) * hpl [zero, negOne, zero, zero] x

theorem continuousOn_i8Psi4s39S0 : ContinuousOn i8Psi4s39S0 (Ioc 0 1) := by
  unfold i8Psi4s39S0
  exact ((((((i13_cont_coef (p := fun x => x ^ 4 / 2 + 4 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero])))

theorem i8Psi4s39_eq_S (x : ℝ) : i8Psi4s39 x = i8Psi4s39S0 x := by
  unfold i8Psi4s39 i8Psi4s39S0 i8Psi4s39N0 i8Psi4s39N1 i8Psi4s39N2 i8Psi4s39N3 i8Psi4s39N4
    i8Psi4s39W
  ring

theorem continuousOn_i8Psi4s39 : ContinuousOn i8Psi4s39 (Ioc 0 1) := by
  rw [show i8Psi4s39 = fun x => i8Psi4s39S0 x from funext i8Psi4s39_eq_S]
  exact continuousOn_i8Psi4s39S0

theorem i8Psi4s39_one : i8Psi4s39 1 = 9 / 2 - 24 * zeta3 + 7 / 30 * π ^ 4 := by
  rw [i8Psi4s39_eq_S]
  unfold i8Psi4s39S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_negOne_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s40` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s40S0 (x : ℝ) : ℝ :=
    (-4 * x ^ 3 + 4 * x - x ^ 4 / 4) / x ^ 2 +
    (x ^ 4 / 2 + 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-x ^ 4 - 4 * x ^ 3 + 4 * x) / x ^ 2 * hpl [zero, zero] x +
    (2 * x ^ 4 + 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero] x +
    (-4) * hpl [zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s40S0 : ContinuousOn i8Psi4s40S0 (Ioc 0 1) := by
  unfold i8Psi4s40S0
  exact (((((i13_cont_coef (p := fun x => -4 * x ^ 3 + 4 * x - x ^ 4 / 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 4 * x ^ 3 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero])))

theorem i8Psi4s40_eq_S (x : ℝ) : i8Psi4s40 x = i8Psi4s40S0 x := by
  unfold i8Psi4s40 i8Psi4s40S0 i8Psi4s40N0 i8Psi4s40N1 i8Psi4s40N2 i8Psi4s40N3 i8Psi4s40N4
    i8Psi4s40W
  ring

theorem continuousOn_i8Psi4s40 : ContinuousOn i8Psi4s40 (Ioc 0 1) := by
  rw [show i8Psi4s40 = fun x => i8Psi4s40S0 x from funext i8Psi4s40_eq_S]
  exact continuousOn_i8Psi4s40S0

theorem i8Psi4s40_one : i8Psi4s40 1 = -1 / 4 := by
  rw [i8Psi4s40_eq_S]
  unfold i8Psi4s40S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_zero_zero_at_one]
  norm_num

/-- Chunk 0 of `i8Psi4s41` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s41S0 (x : ℝ) : ℝ :=
    (-20 * x ^ 4 + 16 * x ^ 3 + 48 * x - 20 * zeta3 * x ^ 3 - 12 * x * zeta3 - 5 * zeta3 * x ^ 4 -
      2 * π ^ 2 * x - 10 / 3 * π ^ 2 * x ^ 3 - 5 / 6 * π ^ 2 * x ^ 4) / x ^ 2 +
    (8 * x ^ 4 + 16 * x + 16 * x ^ 3 + 32 * x ^ 2 - 4 * x * zeta3 + 2 * π ^ 2 * x ^ 3 +
      2 * zeta3 * x ^ 4 + 8 * zeta3 * x ^ 2 + 12 * zeta3 * x ^ 3 - 2 / 3 * π ^ 2 * x +
      π ^ 2 * x ^ 4 / 3 + 4 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (-16 + 2 * π ^ 2 + 12 * zeta3) * hpl [zero, zero] x

theorem continuousOn_i8Psi4s41S0 : ContinuousOn i8Psi4s41S0 (Ioc 0 1) := by
  unfold i8Psi4s41S0
  exact (((i13_cont_coef (p := fun x => -20 * x ^ 4 + 16 * x ^ 3 + 48 * x - 20 * zeta3 * x ^ 3 -
    12 * x * zeta3 - 5 * zeta3 * x ^ 4 - 2 * π ^ 2 * x - 10 / 3 * π ^ 2 * x ^ 3 -
    5 / 6 * π ^ 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 8 * x ^ 4 + 16 * x + 16 * x ^ 3 + 32 * x ^ 2 -
        4 * x * zeta3 + 2 * π ^ 2 * x ^ 3 + 2 * zeta3 * x ^ 4 + 8 * zeta3 * x ^ 2 +
        12 * zeta3 * x ^ 3 - 2 / 3 * π ^ 2 * x + π ^ 2 * x ^ 4 / 3 +
        4 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero])))

theorem i8Psi4s41_eq_S (x : ℝ) : i8Psi4s41 x = i8Psi4s41S0 x := by
  unfold i8Psi4s41 i8Psi4s41S0 i8Psi4s41N0 i8Psi4s41N1 i8Psi4s41N2 i8Psi4s41N3 i8Psi4s41N4
    i8Psi4s41W
  ring

theorem continuousOn_i8Psi4s41 : ContinuousOn i8Psi4s41 (Ioc 0 1) := by
  rw [show i8Psi4s41 = fun x => i8Psi4s41S0 x from funext i8Psi4s41_eq_S]
  exact continuousOn_i8Psi4s41S0

theorem i8Psi4s41_one : i8Psi4s41 1 = 44 - 37 * zeta3 - 37 / 6 * π ^ 2 := by
  rw [i8Psi4s41_eq_S]
  unfold i8Psi4s41S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one]
  norm_num
  ring

end QED.ThreeLoopD
