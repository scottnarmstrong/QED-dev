/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P49

/-!
# Set (d), master `I₈`: continuity and values at `1` of the sub-pieces 0 to 15 of `Ψ₄`

Each sub-piece `Ψ₄⁽ⁿ⁾` is continuous on `(0, 1]` (the words beginning with `1` carry a factor
`1 - ξ`), and its value at `ξ = 1` follows from the values of the harmonic polylogarithms at `1`.

## Main results

* `QED.ThreeLoopD.continuousOn_i8Psi4s0`, `QED.ThreeLoopD.i8Psi4s0_one` and their
  companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- Chunk 0 of `i8Psi4s0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s0S0 (x : ℝ) : ℝ :=
    (-171 / 32 * x ^ 4 + 85 / 16 * x + 255 / 16 * x ^ 3) / x ^ 2 +
    (-43 / 16 - 21 / 4 * x ^ 3 + 21 / 4 * x + 43 / 16 * x ^ 4) / x ^ 2 * hpl [negOne] x +
    (1 / 16) * hpl [zero] x +
    (11 / 4 - 5 * x + 5 * x ^ 3 - 11 / 4 * x ^ 4) / x ^ 2 * hpl [negOne, negOne] x +
    (-11 / 8 - 5 / 2 * x ^ 3 - x ^ 2 / 4 + 5 / 2 * x +
      11 / 8 * x ^ 4) / x ^ 2 * hpl [zero, negOne] x +
    (-3 - 4 * x ^ 3 + 3 * x ^ 4 + 4 * x) / x ^ 2 * hpl [negOne, negOne, negOne] x +
    (3 / 2 - 2 * x + 2 * x ^ 3 - 3 / 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (3 / 2 + x ^ 2 - 2 * x + 2 * x ^ 3 - 3 / 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, negOne] x +
    (-3 / 4 + x - x ^ 3 - x ^ 2 / 2 + 3 / 4 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne] x +
    (4 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, negOne, negOne] x +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, zero, negOne] x +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, negOne, negOne] x +
    (1 - x ^ 4) / x ^ 2 * hpl [negOne, zero, zero, negOne] x +
    (-2 - 4 * x ^ 2 + 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, negOne, negOne] x +
    (1 - x ^ 4 + 2 * x ^ 2) / x ^ 2 * hpl [zero, negOne, zero, negOne] x +
    (1 - x ^ 4 + 2 * x ^ 2) / x ^ 2 * hpl [zero, zero, negOne, negOne] x +
    (-1 / 2 + x ^ 4 / 2 - x ^ 2) / x ^ 2 * hpl [zero, zero, zero, negOne] x +
    (16) * hpl [zero, negOne, negOne, negOne, negOne] x +
    (-8) * hpl [zero, negOne, negOne, zero, negOne] x +
    (-8) * hpl [zero, negOne, zero, negOne, negOne] x

theorem continuousOn_i8Psi4s0S0 : ContinuousOn i8Psi4s0S0 (Ioc 0 1) := by
  unfold i8Psi4s0S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -171 / 32 * x ^ 4 + 85 / 16 * x +
    255 / 16 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -43 / 16 - 21 / 4 * x ^ 3 + 21 / 4 * x +
        43 / 16 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 11 / 4 - 5 * x + 5 * x ^ 3 - 11 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -11 / 8 - 5 / 2 * x ^ 3 - x ^ 2 / 4 + 5 / 2 * x +
        11 / 8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -3 - 4 * x ^ 3 + 3 * x ^ 4 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => 3 / 2 - 2 * x + 2 * x ^ 3 - 3 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 3 / 2 + x ^ 2 - 2 * x + 2 * x ^ 3 -
        3 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => -3 / 4 + x - x ^ 3 - x ^ 2 / 2 +
        3 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 4 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -2 - 4 * x ^ 2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4 + 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4 + 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 4 / 2 - x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne, negOne])))

/-- Chunk 1 of `i8Psi4s0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s0S1 (x : ℝ) : ℝ :=
    (4) * hpl [zero, negOne, zero, zero, negOne] x +
    (-8) * hpl [zero, zero, negOne, negOne, negOne] x +
    (4) * hpl [zero, zero, negOne, zero, negOne] x +
    (4) * hpl [zero, zero, zero, negOne, negOne] x +
    (-2) * hpl [zero, zero, zero, zero, negOne] x

theorem continuousOn_i8Psi4s0S1 : ContinuousOn i8Psi4s0S1 (Ioc 0 1) := by
  unfold i8Psi4s0S1
  exact (((((continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero, negOne])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, negOne])))

theorem i8Psi4s0_eq_S (x : ℝ) : i8Psi4s0 x = i8Psi4s0S0 x + i8Psi4s0S1 x := by
  unfold i8Psi4s0 i8Psi4s0S0 i8Psi4s0S1 i8Psi4s0N0 i8Psi4s0N1 i8Psi4s0N2 i8Psi4s0N3 i8Psi4s0N4
    i8Psi4s0W
  ring

theorem continuousOn_i8Psi4s0 : ContinuousOn i8Psi4s0 (Ioc 0 1) := by
  rw [show i8Psi4s0 = fun x => i8Psi4s0S0 x + i8Psi4s0S1 x from funext i8Psi4s0_eq_S]
  exact (continuousOn_i8Psi4s0S0.add continuousOn_i8Psi4s0S1)

theorem i8Psi4s0_one : i8Psi4s0 1 = 509 / 32 - zeta5 - zeta3 / 4 - π ^ 2 / 48 - π ^ 4 / 180 := by
  rw [i8Psi4s0_eq_S]
  unfold i8Psi4s0S0 i8Psi4s0S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_negOne_at_one, hpl_zero_negOne_at_one,
    hpl_negOne_negOne_negOne_at_one, hpl_negOne_zero_negOne_at_one, hpl_zero_negOne_negOne_at_one,
    hpl_zero_zero_negOne_at_one, hpl_negOne_negOne_negOne_negOne_at_one,
    hpl_negOne_negOne_zero_negOne_at_one, hpl_negOne_zero_negOne_negOne_at_one,
    hpl_negOne_zero_zero_negOne_at_one, hpl_zero_negOne_negOne_negOne_at_one,
    hpl_zero_negOne_zero_negOne_at_one, hpl_zero_zero_negOne_negOne_at_one,
    hpl_zero_zero_zero_negOne_at_one, hpl_zero_negOne_negOne_negOne_negOne_at_one,
    hpl_zero_negOne_negOne_zero_negOne_at_one, hpl_zero_negOne_zero_negOne_negOne_at_one,
    hpl_zero_negOne_zero_zero_negOne_at_one, hpl_zero_zero_negOne_negOne_negOne_at_one,
    hpl_zero_zero_negOne_zero_negOne_at_one, hpl_zero_zero_zero_negOne_negOne_at_one,
    hpl_zero_zero_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s1S0 (x : ℝ) : ℝ :=
    (-115 / 8 * x ^ 4 - 7 / 8 * x ^ 3 + 111 / 8 * x) / x ^ 2 +
    (-59 / 8 - 8 * x + 8 * x ^ 3 + 59 / 8 * x ^ 4) / x ^ 2 * hpl [negOne] x +
    (21 / 4 * x + 43 / 8 * x ^ 4 + 65 / 4 * x ^ 3 + 133 / 8 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (8 - 10 * x ^ 3 - 8 * x ^ 4 + 10 * x) / x ^ 2 * hpl [negOne, negOne] x +
    (-11 / 4 - 11 * x - 11 * x ^ 3 - 33 / 2 * x ^ 2 -
      11 / 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-27 / 4 - 18 * x ^ 2 - 16 * x - 6 * x ^ 3 + 5 / 4 * x ^ 4) / x ^ 2 * hpl [zero, negOne] x +
    (1 / 4) * hpl [zero, zero] x +
    (-10 - 16 * x + 10 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [negOne, negOne, negOne] x +
    (3 + 3 * x ^ 4 + 12 * x + 12 * x ^ 3 + 18 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (8 - 2 * x ^ 4 + 4 * x ^ 3 + 18 * x ^ 2 + 20 * x) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (8 - 2 * x ^ 4 + 4 * x ^ 3 + 20 * x + 22 * x ^ 2) / x ^ 2 * hpl [zero, negOne, negOne] x +
    (-3 / 2 - 9 * x ^ 2 - 6 * x - 6 * x ^ 3 - 3 / 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-11 / 2 - 20 * x ^ 2 - 16 * x - 8 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero, zero, negOne] x +
    (-4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
      4 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, negOne, zero] x +
    (-4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
      4 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, zero, negOne] x +
    (-4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
      4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, negOne, negOne] x +
    (2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne, zero] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
      24 * x ^ 2) / x ^ 2 * hpl [negOne, zero, zero, negOne] x +
    (-4 - 32 * x ^ 2 - 16 * x - 16 * x ^ 3 -
      4 * x ^ 4) / x ^ 2 * hpl [zero, negOne, negOne, negOne] x +
    (2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * hpl [zero, negOne, negOne, zero] x

theorem continuousOn_i8Psi4s1S0 : ContinuousOn i8Psi4s1S0 (Ioc 0 1) := by
  unfold i8Psi4s1S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -115 / 8 * x ^ 4 - 7 / 8 * x ^ 3 +
    111 / 8 * x) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -59 / 8 - 8 * x + 8 * x ^ 3 +
        59 / 8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 21 / 4 * x + 43 / 8 * x ^ 4 + 65 / 4 * x ^ 3 +
        133 / 8 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 8 - 10 * x ^ 3 - 8 * x ^ 4 + 10 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -11 / 4 - 11 * x - 11 * x ^ 3 - 33 / 2 * x ^ 2 -
        11 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -27 / 4 - 18 * x ^ 2 - 16 * x - 6 * x ^ 3 +
        5 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -10 - 16 * x + 10 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => 3 + 3 * x ^ 4 + 12 * x + 12 * x ^ 3 +
        18 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 8 - 2 * x ^ 4 + 4 * x ^ 3 + 18 * x ^ 2 +
        20 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 8 - 2 * x ^ 4 + 4 * x ^ 3 + 20 * x +
        22 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => -3 / 2 - 9 * x ^ 2 - 6 * x - 6 * x ^ 3 -
        3 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -11 / 2 - 20 * x ^ 2 - 16 * x - 8 * x ^ 3 -
        x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 +
        12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -4 - 32 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 +
        12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero])))

/-- Chunk 1 of `i8Psi4s1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s1S1 (x : ℝ) : ℝ :=
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
      28 * x ^ 2) / x ^ 2 * hpl [zero, negOne, zero, negOne] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
      28 * x ^ 2) / x ^ 2 * hpl [zero, zero, negOne, negOne] x +
    (-1 - x ^ 4 - 6 * x ^ 2 - 4 * x - 4 * x ^ 3) / x ^ 2 * hpl [zero, zero, negOne, zero] x +
    (-3 - 20 * x ^ 2 - 12 * x - 12 * x ^ 3 - 3 * x ^ 4) / x ^ 2 * hpl [zero, zero, zero, negOne] x

theorem continuousOn_i8Psi4s1S1 : ContinuousOn i8Psi4s1S1 (Ioc 0 1) := by
  unfold i8Psi4s1S1
  exact (((((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
    28 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne])).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        28 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 4 - 6 * x ^ 2 - 4 * x - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -3 - 20 * x ^ 2 - 12 * x - 12 * x ^ 3 -
        3 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne])))

theorem i8Psi4s1_eq_S (x : ℝ) : i8Psi4s1 x = i8Psi4s1S0 x + i8Psi4s1S1 x := by
  unfold i8Psi4s1 i8Psi4s1S0 i8Psi4s1S1 i8Psi4s1N0 i8Psi4s1N1 i8Psi4s1N2 i8Psi4s1N3 i8Psi4s1N4
    i8Psi4s1W i8Psi4s1N0c0 i8Psi4s1N0c1 i8Psi4s1N1c0 i8Psi4s1N1c1 i8Psi4s1N3c0 i8Psi4s1N3c1
    i8Psi4s1N4c0 i8Psi4s1N4c1
  ring

theorem continuousOn_i8Psi4s1 : ContinuousOn i8Psi4s1 (Ioc 0 1) := by
  rw [show i8Psi4s1 = fun x => i8Psi4s1S0 x + i8Psi4s1S1 x from funext i8Psi4s1_eq_S]
  exact (continuousOn_i8Psi4s1S0.add continuousOn_i8Psi4s1S1)

theorem i8Psi4s1_one : i8Psi4s1 1 = -11 / 8 - zeta3 - π ^ 2 / 8 - π ^ 4 / 90 := by
  rw [i8Psi4s1_eq_S]
  unfold i8Psi4s1S0 i8Psi4s1S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_negOne_at_one, hpl_negOne_zero_at_one,
    hpl_zero_negOne_at_one, hpl_zero_zero_at_one, hpl_negOne_negOne_negOne_at_one,
    hpl_negOne_negOne_zero_at_one, hpl_negOne_zero_negOne_at_one, hpl_zero_negOne_negOne_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one, hpl_negOne_negOne_negOne_zero_at_one,
    hpl_negOne_negOne_zero_negOne_at_one, hpl_negOne_zero_negOne_negOne_at_one,
    hpl_negOne_zero_negOne_zero_at_one, hpl_negOne_zero_zero_negOne_at_one,
    hpl_zero_negOne_negOne_negOne_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_zero_negOne_at_one, hpl_zero_zero_negOne_negOne_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s2` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s2S0 (x : ℝ) : ℝ :=
    (8 * x ^ 3 + 28 * x - 21 / 2 * x ^ 4 - 2 / 3 * π ^ 2 * x - 2 / 3 * π ^ 2 * x ^ 3 -
      π ^ 2 * x ^ 4 / 3) / x ^ 2 +
    (5 * x ^ 4 + 8 * x ^ 3 + 12 * x + 16 * x ^ 2 + 2 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (-12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (2 * x ^ 4 + 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (8) * hpl [zero, negOne, zero] x +
    (-4) * hpl [zero, zero, zero] x

theorem continuousOn_i8Psi4s2S0 : ContinuousOn i8Psi4s2S0 (Ioc 0 1) := by
  unfold i8Psi4s2S0
  exact ((((((i13_cont_coef (p := fun x => 8 * x ^ 3 + 28 * x - 21 / 2 * x ^ 4 -
    2 / 3 * π ^ 2 * x - 2 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 5 * x ^ 4 + 8 * x ^ 3 + 12 * x + 16 * x ^ 2 +
        2 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 4 + 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero])))

theorem i8Psi4s2_eq_S (x : ℝ) : i8Psi4s2 x = i8Psi4s2S0 x := by
  unfold i8Psi4s2 i8Psi4s2S0 i8Psi4s2N0 i8Psi4s2N1 i8Psi4s2N2 i8Psi4s2N3 i8Psi4s2N4 i8Psi4s2W
  ring

theorem continuousOn_i8Psi4s2 : ContinuousOn i8Psi4s2 (Ioc 0 1) := by
  rw [show i8Psi4s2 = fun x => i8Psi4s2S0 x from funext i8Psi4s2_eq_S]
  exact continuousOn_i8Psi4s2S0

theorem i8Psi4s2_one : i8Psi4s2 1 = 51 / 2 + π ^ 2 - 12 * zeta3 := by
  rw [i8Psi4s2_eq_S]
  unfold i8Psi4s2S0
  rw [hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s3` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s3S0 (x : ℝ) : ℝ :=
    (-57 / 4 * x ^ 3 - 35 / 4 * x - 27 / 8 * x ^ 4 - π ^ 2 * x ^ 3 / 2 - π ^ 2 * x ^ 4 / 12 +
      π ^ 2 * x / 6) / x ^ 2 +
    (-21 / 4 - 10 * x + 10 * x ^ 3 + π ^ 2 / 6 + 21 / 4 * x ^ 4 + π ^ 2 * x ^ 2 +
      π ^ 2 * x ^ 4 / 6 + 2 / 3 * π ^ 2 * x + 2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (-7 / 2 * x + 3 / 2 * x ^ 4 + 19 / 2 * x ^ 3 + 19 / 4 * x ^ 2 -
      π ^ 2 * x ^ 2 / 2) / x ^ 2 * hpl [zero] x +
    (-5 / 2 - 18 * x ^ 2 - 16 * x ^ 3 - 8 * x - 7 / 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-5 / 2 - 16 * x ^ 2 - 10 * x - 10 * x ^ 3 - 5 / 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne] x +
    (x ^ 4 / 2 - x + 3 * x ^ 3 + 11 / 2 * x ^ 2) / x ^ 2 * hpl [zero, zero] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (-1 - x ^ 4 - 6 * x ^ 2 - 4 * x - 4 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-1 - x ^ 4 - 12 * x ^ 2 - 4 * x - 4 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-1 - x ^ 4 - 6 * x ^ 2 - 4 * x - 4 * x ^ 3) / x ^ 2 * hpl [zero, zero, negOne] x +
    (3) * hpl [zero, zero, zero] x

theorem continuousOn_i8Psi4s3S0 : ContinuousOn i8Psi4s3S0 (Ioc 0 1) := by
  unfold i8Psi4s3S0
  exact ((((((((((((i13_cont_coef (p := fun x => -57 / 4 * x ^ 3 - 35 / 4 * x - 27 / 8 * x ^ 4 -
    π ^ 2 * x ^ 3 / 2 - π ^ 2 * x ^ 4 / 12 + π ^ 2 * x / 6) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -21 / 4 - 10 * x + 10 * x ^ 3 + π ^ 2 / 6 + 21 / 4 * x ^ 4 +
        π ^ 2 * x ^ 2 + π ^ 2 * x ^ 4 / 6 + 2 / 3 * π ^ 2 * x +
        2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -7 / 2 * x + 3 / 2 * x ^ 4 + 19 / 2 * x ^ 3 +
        19 / 4 * x ^ 2 - π ^ 2 * x ^ 2 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -5 / 2 - 18 * x ^ 2 - 16 * x ^ 3 - 8 * x -
        7 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -5 / 2 - 16 * x ^ 2 - 10 * x - 10 * x ^ 3 -
        5 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - x + 3 * x ^ 3 + 11 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 +
        12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 4 - 6 * x ^ 2 - 4 * x - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 4 - 12 * x ^ 2 - 4 * x - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 4 - 6 * x ^ 2 - 4 * x - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero])))

theorem i8Psi4s3_eq_S (x : ℝ) : i8Psi4s3 x = i8Psi4s3S0 x := by
  unfold i8Psi4s3 i8Psi4s3S0 i8Psi4s3N0 i8Psi4s3N1 i8Psi4s3N2 i8Psi4s3N3 i8Psi4s3N4 i8Psi4s3W
  ring

theorem continuousOn_i8Psi4s3 : ContinuousOn i8Psi4s3 (Ioc 0 1) := by
  rw [show i8Psi4s3 = fun x => i8Psi4s3S0 x from funext i8Psi4s3_eq_S]
  exact continuousOn_i8Psi4s3S0

theorem i8Psi4s3_one : i8Psi4s3 1 = -211 / 8 + 9 * zeta3 + π ^ 2 / 6 := by
  rw [i8Psi4s3_eq_S]
  unfold i8Psi4s3S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_negOne_zero_at_one, hpl_negOne_zero_negOne_at_one,
    hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s4` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s4S0 (x : ℝ) : ℝ :=
    (-43 / 8 * x + 17 / 8 * x ^ 4 + 273 / 8 * x ^ 3 + π ^ 2 * x / 12 + π ^ 2 * x ^ 4 / 24 +
      7 / 12 * π ^ 2 * x ^ 3) / x ^ 2 +
    (-27 / 8 - 23 * x - 23 * x ^ 3 - 157 / 4 * x ^ 2 - 27 / 8 * x ^ 4 + π ^ 2 / 12 -
      2 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 12 + 2 / 3 * π ^ 2 * x) / x ^ 2 * hpl [negOne] x +
    (-2 * x - 29 / 2 * x ^ 3 - 7 / 8 * x ^ 4 + 157 / 8 * x ^ 2 -
      7 / 12 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (-3 / 2 - 12 * x + 2 * x ^ 4 + 20 * x ^ 3 + 15 / 2 * x ^ 2) / x ^ 2 * hpl [negOne, zero] x +
    (-27 / 4 - 23 * x + 23 * x ^ 3 + π ^ 2 / 6 + 27 / 4 * x ^ 4 + π ^ 2 * x ^ 4 / 6 +
      2 / 3 * π ^ 2 * x + 2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (-7 / 2 * x ^ 3 - x / 2 - x ^ 4 / 4 + 21 / 2 * x ^ 2) / x ^ 2 * hpl [zero, zero] x +
    (2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (1 - x ^ 4 - 8 * x ^ 3 + 8 * x) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (-1 / 2 + x ^ 4 / 2 - 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-3 - 14 * x - 14 * x ^ 2 - 6 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-11 / 2 - 24 * x - 23 * x ^ 2 - 16 * x ^ 3 -
      9 / 2 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne] x +
    (7 / 2) * hpl [zero, zero, zero] x +
    (2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne, zero] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
      24 * x ^ 2) / x ^ 2 * hpl [negOne, zero, zero, negOne] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3) / x ^ 2 * hpl [zero, negOne, negOne, zero] x +
    (2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero, negOne] x +
    (-1 - x ^ 4 - 4 * x - 4 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero, zero] x +
    (-2 - 8 * x - 8 * x ^ 3 - 6 * x ^ 2 - 2 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne, zero] x +
    (-3 - 12 * x - 12 * x ^ 2 - 12 * x ^ 3 - 3 * x ^ 4) / x ^ 2 * hpl [zero, zero, zero, negOne] x

theorem continuousOn_i8Psi4s4S0 : ContinuousOn i8Psi4s4S0 (Ioc 0 1) := by
  unfold i8Psi4s4S0
  exact (((((((((((((((((((i13_cont_coef (p := fun x => -43 / 8 * x + 17 / 8 * x ^ 4 +
    273 / 8 * x ^ 3 + π ^ 2 * x / 12 + π ^ 2 * x ^ 4 / 24 +
    7 / 12 * π ^ 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -27 / 8 - 23 * x - 23 * x ^ 3 - 157 / 4 * x ^ 2 -
        27 / 8 * x ^ 4 + π ^ 2 / 12 - 2 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 12 +
        2 / 3 * π ^ 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -2 * x - 29 / 2 * x ^ 3 - 7 / 8 * x ^ 4 + 157 / 8 * x ^ 2 -
        7 / 12 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -3 / 2 - 12 * x + 2 * x ^ 4 + 20 * x ^ 3 +
        15 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -27 / 4 - 23 * x + 23 * x ^ 3 + π ^ 2 / 6 + 27 / 4 * x ^ 4 +
        π ^ 2 * x ^ 4 / 6 + 2 / 3 * π ^ 2 * x + 2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -7 / 2 * x ^ 3 - x / 2 - x ^ 4 / 4 +
        21 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4 - 8 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 4 / 2 - 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -3 - 14 * x - 14 * x ^ 2 - 6 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -11 / 2 - 24 * x - 23 * x ^ 2 - 16 * x ^ 3 -
        9 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 +
        12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 4 - 4 * x - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 8 * x - 8 * x ^ 3 - 6 * x ^ 2 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -3 - 12 * x - 12 * x ^ 2 - 12 * x ^ 3 -
        3 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne])))

theorem i8Psi4s4_eq_S (x : ℝ) : i8Psi4s4 x = i8Psi4s4S0 x := by
  unfold i8Psi4s4 i8Psi4s4S0 i8Psi4s4N0 i8Psi4s4N1 i8Psi4s4N2 i8Psi4s4N3 i8Psi4s4N4 i8Psi4s4W
  ring

theorem continuousOn_i8Psi4s4 : ContinuousOn i8Psi4s4 (Ioc 0 1) := by
  rw [show i8Psi4s4 = fun x => i8Psi4s4S0 x from funext i8Psi4s4_eq_S]
  exact continuousOn_i8Psi4s4S0

theorem i8Psi4s4_one : i8Psi4s4 1 = 247 / 8 - 92 * Real.log 2 + 2 * Real.log 2 ^ 4 +
    48 * Li 4 (1 / 2) - 29 / 60 * π ^ 4 - 5 / 8 * π ^ 2 + 15 / 4 * zeta3 -
    2 * π ^ 2 * Real.log 2 ^ 2 + 42 * Real.log 2 * zeta3 := by
  rw [i8Psi4s4_eq_S]
  unfold i8Psi4s4S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_negOne_zero_at_one, hpl_negOne_zero_negOne_at_one,
    hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_zero_zero_at_one, hpl_negOne_zero_negOne_zero_at_one,
    hpl_negOne_zero_zero_negOne_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_zero_negOne_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s5` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s5S0 (x : ℝ) : ℝ :=
    (-167 / 4 * x ^ 3 - 17 / 4 * x ^ 4 - 5 / 6 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 12) / x ^ 2 +
    (27 / 4 * x ^ 4 + 35 / 2 * x + 57 / 2 * x ^ 3 + 157 / 4 * x ^ 2 + π ^ 2 * x ^ 3 +
      π ^ 2 * x ^ 2 / 2 - π ^ 2 * x / 3 + π ^ 2 * x ^ 4 / 6) / x ^ 2 * hpl [negOne] x +
    (20 * x ^ 3 - 35 / 2 * x ^ 2 + 7 / 4 * x ^ 4 + π ^ 2 * x ^ 2 / 3) / x ^ 2 * hpl [zero] x +
    (21 / 2 - 20 * x ^ 3 + 20 * x - 21 / 2 * x ^ 4 - π ^ 2 / 3 - 2 * π ^ 2 * x ^ 2 -
      4 / 3 * π ^ 2 * x - 4 / 3 * π ^ 2 * x ^ 3 -
      π ^ 2 * x ^ 4 / 3) / x ^ 2 * hpl [negOne, negOne] x +
    (-29 * x ^ 3 - 18 * x ^ 2 - 4 * x ^ 4 + 7 * x) / x ^ 2 * hpl [negOne, zero] x +
    (-19 * x ^ 3 - 3 * x ^ 4 + 7 * x - 19 / 2 * x ^ 2 +
      π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, negOne] x +
    (x ^ 4 / 2 - 7 * x ^ 2 + 5 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (5 + 9 * x ^ 4 + 12 * x + 42 * x ^ 2 + 44 * x ^ 3) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (5 + 7 * x ^ 4 + 16 * x + 32 * x ^ 3 + 36 * x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (-x ^ 4 - 6 * x ^ 3 - 3 * x ^ 2 + 2 * x) / x ^ 2 * hpl [negOne, zero, zero] x +
    (5 + 5 * x ^ 4 + 20 * x + 20 * x ^ 3 + 32 * x ^ 2) / x ^ 2 * hpl [zero, negOne, negOne] x +
    (-x ^ 4 - 7 * x ^ 2 - 6 * x ^ 3 + 2 * x) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-x ^ 4 - 11 * x ^ 2 - 6 * x ^ 3 + 2 * x) / x ^ 2 * hpl [zero, zero, negOne] x +
    (-2) * hpl [zero, zero, zero] x +
    (-12 - 72 * x ^ 2 - 48 * x - 48 * x ^ 3 -
      12 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, negOne, zero] x +
    (-8 - 48 * x ^ 2 - 32 * x - 32 * x ^ 3 -
      8 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, zero, negOne] x +
    (2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero, zero] x +
    (-4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
      4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, negOne, negOne] x +
    (2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne, zero] x +
    (2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * hpl [negOne, zero, zero, negOne] x

theorem continuousOn_i8Psi4s5S0 : ContinuousOn i8Psi4s5S0 (Ioc 0 1) := by
  unfold i8Psi4s5S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -167 / 4 * x ^ 3 - 17 / 4 * x ^ 4 -
    5 / 6 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 12) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 27 / 4 * x ^ 4 + 35 / 2 * x + 57 / 2 * x ^ 3 +
        157 / 4 * x ^ 2 + π ^ 2 * x ^ 3 + π ^ 2 * x ^ 2 / 2 - π ^ 2 * x / 3 +
        π ^ 2 * x ^ 4 / 6) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 20 * x ^ 3 - 35 / 2 * x ^ 2 + 7 / 4 * x ^ 4 +
        π ^ 2 * x ^ 2 / 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 21 / 2 - 20 * x ^ 3 + 20 * x - 21 / 2 * x ^ 4 - π ^ 2 / 3 -
        2 * π ^ 2 * x ^ 2 - 4 / 3 * π ^ 2 * x - 4 / 3 * π ^ 2 * x ^ 3 -
        π ^ 2 * x ^ 4 / 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -29 * x ^ 3 - 18 * x ^ 2 - 4 * x ^ 4 +
        7 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -19 * x ^ 3 - 3 * x ^ 4 + 7 * x - 19 / 2 * x ^ 2 +
        π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - 7 * x ^ 2 + 5 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 5 + 9 * x ^ 4 + 12 * x + 42 * x ^ 2 +
        44 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 5 + 7 * x ^ 4 + 16 * x + 32 * x ^ 3 +
        36 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 6 * x ^ 3 - 3 * x ^ 2 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 5 + 5 * x ^ 4 + 20 * x + 20 * x ^ 3 +
        32 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 7 * x ^ 2 - 6 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 11 * x ^ 2 - 6 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -12 - 72 * x ^ 2 - 48 * x - 48 * x ^ 3 -
        12 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -8 - 48 * x ^ 2 - 32 * x - 32 * x ^ 3 -
        8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 +
        12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 +
        12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 +
        12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, negOne])))

/-- Chunk 1 of `i8Psi4s5` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s5S1 (x : ℝ) : ℝ :=
    (2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 + 36 * x ^ 2) / x ^ 2 * hpl [zero, negOne, negOne, zero] x +
    (2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * hpl [zero, negOne, zero, negOne] x +
    (-6) * hpl [zero, negOne, zero, zero] x +
    (2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * hpl [zero, zero, negOne, negOne] x +
    (-6) * hpl [zero, zero, negOne, zero] x +
    (-6) * hpl [zero, zero, zero, negOne] x

theorem continuousOn_i8Psi4s5S1 : ContinuousOn i8Psi4s5S1 (Ioc 0 1) := by
  unfold i8Psi4s5S1
  exact (((((((i13_cont_coef (p := fun x => 2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 +
    36 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero])).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 +
        12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne])))

theorem i8Psi4s5_eq_S (x : ℝ) : i8Psi4s5 x = i8Psi4s5S0 x + i8Psi4s5S1 x := by
  unfold i8Psi4s5 i8Psi4s5S0 i8Psi4s5S1 i8Psi4s5N0 i8Psi4s5N1 i8Psi4s5N2 i8Psi4s5N3 i8Psi4s5N4
    i8Psi4s5W i8Psi4s5N2c0 i8Psi4s5N2c1 i8Psi4s5N3c0 i8Psi4s5N3c1 i8Psi4s5N4c0 i8Psi4s5N4c1
  ring

theorem continuousOn_i8Psi4s5 : ContinuousOn i8Psi4s5 (Ioc 0 1) := by
  rw [show i8Psi4s5 = fun x => i8Psi4s5S0 x + i8Psi4s5S1 x from funext i8Psi4s5_eq_S]
  exact (continuousOn_i8Psi4s5S0.add continuousOn_i8Psi4s5S1)

theorem i8Psi4s5_one : i8Psi4s5 1 = -46 - 48 * Li 4 (1 / 2) - 2 * Real.log 2 ^ 4 +
    92 * Real.log 2 + zeta3 / 4 + 17 / 24 * π ^ 2 + 29 / 60 * π ^ 4 - 42 * Real.log 2 * zeta3 +
    2 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s5_eq_S]
  unfold i8Psi4s5S0 i8Psi4s5S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_negOne_at_one, hpl_negOne_zero_at_one,
    hpl_zero_negOne_at_one, hpl_zero_zero_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_negOne_zero_negOne_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_negOne_negOne_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one,
    hpl_negOne_negOne_negOne_zero_at_one, hpl_negOne_negOne_zero_negOne_at_one,
    hpl_negOne_negOne_zero_zero_at_one, hpl_negOne_zero_negOne_negOne_at_one,
    hpl_negOne_zero_negOne_zero_at_one, hpl_negOne_zero_zero_negOne_at_one,
    hpl_zero_negOne_negOne_zero_at_one, hpl_zero_negOne_zero_negOne_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_zero_negOne_negOne_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s6` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s6S0 (x : ℝ) : ℝ :=
    (-12 * x ^ 3 + 20 * x - 13 / 2 * x ^ 4) / x ^ 2 +
    (5 * x ^ 4 + 8 * x ^ 2 + 12 * x + 20 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-12 * x ^ 3 - 8 * x ^ 2 - 2 * x ^ 4 + 4 * x) / x ^ 2 * hpl [zero, zero] x +
    (-12) * hpl [zero, zero, zero] x

theorem continuousOn_i8Psi4s6S0 : ContinuousOn i8Psi4s6S0 (Ioc 0 1) := by
  unfold i8Psi4s6S0
  exact ((((i13_cont_coef (p := fun x => -12 * x ^ 3 + 20 * x - 13 / 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 5 * x ^ 4 + 8 * x ^ 2 + 12 * x + 20 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -12 * x ^ 3 - 8 * x ^ 2 - 2 * x ^ 4 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero])))

theorem i8Psi4s6_eq_S (x : ℝ) : i8Psi4s6 x = i8Psi4s6S0 x := by
  unfold i8Psi4s6 i8Psi4s6S0 i8Psi4s6N0 i8Psi4s6N1 i8Psi4s6N2 i8Psi4s6N3 i8Psi4s6N4 i8Psi4s6W
  ring

theorem continuousOn_i8Psi4s6 : ContinuousOn i8Psi4s6 (Ioc 0 1) := by
  rw [show i8Psi4s6 = fun x => i8Psi4s6S0 x from funext i8Psi4s6_eq_S]
  exact continuousOn_i8Psi4s6S0

theorem i8Psi4s6_one : i8Psi4s6 1 = 3 / 2 := by
  rw [i8Psi4s6_eq_S]
  unfold i8Psi4s6S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one]
  norm_num

/-- Chunk 0 of `i8Psi4s7` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s7S0 (x : ℝ) : ℝ :=
    (-133 / 4 * x ^ 3 - 27 / 4 * x - 19 / 8 * x ^ 4) / x ^ 2 +
    (-13 / 4 - 16 * x + 16 * x ^ 3 + 13 / 4 * x ^ 4) / x ^ 2 * hpl [negOne] x +
    (-7 / 2 * x + 3 / 2 * x ^ 4 + 41 / 2 * x ^ 3 + 51 / 4 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (-5 / 2 - 27 * x ^ 2 - 16 * x - 16 * x ^ 3 - 5 / 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-5 / 2 - 16 * x - 16 * x ^ 3 - 8 * x ^ 2 - 5 / 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne] x +
    (-x - 7 * x ^ 3 - x ^ 4 / 2 + 27 / 2 * x ^ 2) / x ^ 2 * hpl [zero, zero] x +
    (-1 + x ^ 4 - 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-1 + x ^ 4 - 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-1 + x ^ 4 - 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, zero, negOne] x +
    (7) * hpl [zero, zero, zero] x +
    (12) * hpl [zero, negOne, zero, zero] x +
    (12) * hpl [zero, zero, negOne, zero] x +
    (12) * hpl [zero, zero, zero, negOne] x

theorem continuousOn_i8Psi4s7S0 : ContinuousOn i8Psi4s7S0 (Ioc 0 1) := by
  unfold i8Psi4s7S0
  exact (((((((((((((i13_cont_coef (p := fun x => -133 / 4 * x ^ 3 - 27 / 4 * x -
    19 / 8 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -13 / 4 - 16 * x + 16 * x ^ 3 +
        13 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -7 / 2 * x + 3 / 2 * x ^ 4 + 41 / 2 * x ^ 3 +
        51 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -5 / 2 - 27 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        5 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -5 / 2 - 16 * x - 16 * x ^ 3 - 8 * x ^ 2 -
        5 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -x - 7 * x ^ 3 - x ^ 4 / 2 + 27 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4 - 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4 - 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4 - 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne])))

theorem i8Psi4s7_eq_S (x : ℝ) : i8Psi4s7 x = i8Psi4s7S0 x := by
  unfold i8Psi4s7 i8Psi4s7S0 i8Psi4s7N0 i8Psi4s7N1 i8Psi4s7N2 i8Psi4s7N3 i8Psi4s7N4 i8Psi4s7W
  ring

theorem continuousOn_i8Psi4s7 : ContinuousOn i8Psi4s7 (Ioc 0 1) := by
  rw [show i8Psi4s7 = fun x => i8Psi4s7S0 x from funext i8Psi4s7_eq_S]
  exact continuousOn_i8Psi4s7S0

theorem i8Psi4s7_one : i8Psi4s7 1 = -339 / 8 + 7 / 60 * π ^ 4 + 19 / 12 * π ^ 2 := by
  rw [i8Psi4s7_eq_S]
  unfold i8Psi4s7S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s8` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s8S0 (x : ℝ) : ℝ :=
    (-451 / 4 * x ^ 3 - 13 / 4 * x ^ 4) / x ^ 2 +
    (19 / 4 * x ^ 4 + 27 / 2 * x + 133 / 2 * x ^ 3 + 301 / 4 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (51 * x ^ 3 - 27 / 2 * x ^ 2 + 7 / 4 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (13 / 2 - 32 * x ^ 3 + 32 * x - 13 / 2 * x ^ 4) / x ^ 2 * hpl [negOne, negOne] x +
    (-41 * x ^ 3 - 31 * x ^ 2 - 3 * x ^ 4 + 7 * x) / x ^ 2 * hpl [negOne, zero] x +
    (-41 * x ^ 3 - 3 * x ^ 4 + 7 * x - 51 / 2 * x ^ 2) / x ^ 2 * hpl [zero, negOne] x +
    (-13 * x ^ 3 - 7 * x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [zero, zero] x +
    (5 + 5 * x ^ 4 + 32 * x + 32 * x ^ 3 + 54 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (5 + 5 * x ^ 4 + 32 * x + 32 * x ^ 3 + 54 * x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (x ^ 4 + 2 * x + 14 * x ^ 3 + 15 * x ^ 2) / x ^ 2 * hpl [negOne, zero, zero] x +
    (5 + 5 * x ^ 4 + 16 * x ^ 2 + 32 * x + 32 * x ^ 3) / x ^ 2 * hpl [zero, negOne, negOne] x +
    (x ^ 4 - 27 * x ^ 2 + 2 * x + 14 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero] x +
    (x ^ 4 - 27 * x ^ 2 + 2 * x + 14 * x ^ 3) / x ^ 2 * hpl [zero, zero, negOne] x +
    (-2) * hpl [zero, zero, zero] x +
    (2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) / x ^ 2 * hpl [negOne, negOne, zero, zero] x +
    (2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) / x ^ 2 * hpl [negOne, zero, negOne, zero] x +
    (2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) / x ^ 2 * hpl [negOne, zero, zero, negOne] x +
    (2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) / x ^ 2 * hpl [zero, negOne, negOne, zero] x +
    (2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) / x ^ 2 * hpl [zero, negOne, zero, negOne] x +
    (-14) * hpl [zero, negOne, zero, zero] x

theorem continuousOn_i8Psi4s8S0 : ContinuousOn i8Psi4s8S0 (Ioc 0 1) := by
  unfold i8Psi4s8S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -451 / 4 * x ^ 3 -
    13 / 4 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 19 / 4 * x ^ 4 + 27 / 2 * x + 133 / 2 * x ^ 3 +
        301 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 51 * x ^ 3 - 27 / 2 * x ^ 2 + 7 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 13 / 2 - 32 * x ^ 3 + 32 * x -
        13 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -41 * x ^ 3 - 31 * x ^ 2 - 3 * x ^ 4 +
        7 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -41 * x ^ 3 - 3 * x ^ 4 + 7 * x -
        51 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -13 * x ^ 3 - 7 * x ^ 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 5 + 5 * x ^ 4 + 32 * x + 32 * x ^ 3 +
        54 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 5 + 5 * x ^ 4 + 32 * x + 32 * x ^ 3 +
        54 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 2 * x + 14 * x ^ 3 + 15 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 5 + 5 * x ^ 4 + 16 * x ^ 2 + 32 * x +
        32 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 27 * x ^ 2 + 2 * x + 14 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 27 * x ^ 2 + 2 * x + 14 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero])))

/-- Chunk 1 of `i8Psi4s8` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s8S1 (x : ℝ) : ℝ :=
    (2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) / x ^ 2 * hpl [zero, zero, negOne, negOne] x +
    (-14) * hpl [zero, zero, negOne, zero] x +
    (-14) * hpl [zero, zero, zero, negOne] x +
    (-24) * hpl [zero, negOne, negOne, zero, zero] x +
    (-24) * hpl [zero, negOne, zero, negOne, zero] x +
    (-24) * hpl [zero, negOne, zero, zero, negOne] x +
    (-24) * hpl [zero, zero, negOne, negOne, zero] x +
    (-24) * hpl [zero, zero, negOne, zero, negOne] x +
    (-24) * hpl [zero, zero, zero, negOne, negOne] x

theorem continuousOn_i8Psi4s8S1 : ContinuousOn i8Psi4s8S1 (Ioc 0 1) := by
  unfold i8Psi4s8S1
  exact ((((((((((i13_cont_coef (p := fun x => 2 - 16 * x ^ 3 - 2 * x ^ 4 +
    16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne, negOne])))

theorem i8Psi4s8_eq_S (x : ℝ) : i8Psi4s8 x = i8Psi4s8S0 x + i8Psi4s8S1 x := by
  unfold i8Psi4s8 i8Psi4s8S0 i8Psi4s8S1 i8Psi4s8N0 i8Psi4s8N1 i8Psi4s8N2 i8Psi4s8N3 i8Psi4s8N4
    i8Psi4s8W
  ring

theorem continuousOn_i8Psi4s8 : ContinuousOn i8Psi4s8 (Ioc 0 1) := by
  rw [show i8Psi4s8 = fun x => i8Psi4s8S0 x + i8Psi4s8S1 x from funext i8Psi4s8_eq_S]
  exact (continuousOn_i8Psi4s8S0.add continuousOn_i8Psi4s8S1)

theorem i8Psi4s8_one : i8Psi4s8 1 = -116 + 160 * Real.log 2 - 49 / 360 * π ^ 4 +
    11 / 24 * π ^ 2 + 87 / 4 * zeta5 + 107 / 4 * zeta3 - 2 * π ^ 2 * zeta3 := by
  rw [i8Psi4s8_eq_S]
  unfold i8Psi4s8S0 i8Psi4s8S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_negOne_at_one, hpl_negOne_zero_at_one,
    hpl_zero_negOne_at_one, hpl_zero_zero_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_negOne_zero_negOne_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_negOne_negOne_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one,
    hpl_negOne_negOne_zero_zero_at_one, hpl_negOne_zero_negOne_zero_at_one,
    hpl_negOne_zero_zero_negOne_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_zero_negOne_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_negOne_negOne_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_negOne_at_one, hpl_zero_negOne_negOne_zero_zero_at_one,
    hpl_zero_negOne_zero_negOne_zero_at_one, hpl_zero_negOne_zero_zero_negOne_at_one,
    hpl_zero_zero_negOne_negOne_zero_at_one, hpl_zero_zero_negOne_zero_negOne_at_one,
    hpl_zero_zero_zero_negOne_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s9` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s9S0 (x : ℝ) : ℝ :=
    (-35 / 8 * x + 13 / 8 * x ^ 4 + 541 / 8 * x ^ 3) / x ^ 2 +
    (-19 / 8 - 40 * x - 40 * x ^ 3 - 301 / 4 * x ^ 2 - 19 / 8 * x ^ 4) / x ^ 2 * hpl [negOne] x +
    (-30 * x ^ 3 - 2 * x - 7 / 8 * x ^ 4 + 301 / 8 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (-3 / 2 - 24 * x + 24 * x ^ 3 + 3 / 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-19 / 4 - 40 * x + 40 * x ^ 3 + 19 / 4 * x ^ 4) / x ^ 2 * hpl [zero, negOne] x +
    (-x / 2 + x ^ 4 / 4 + 15 / 2 * x ^ 3 + 45 / 2 * x ^ 2) / x ^ 2 * hpl [zero, zero] x +
    (-1 / 2 - 15 * x ^ 2 - 8 * x - 8 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-3 - 24 * x - 24 * x ^ 3 - 3 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-11 / 2 - 40 * x - 40 * x ^ 3 - 8 * x ^ 2 -
      11 / 2 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne] x +
    (15 / 2) * hpl [zero, zero, zero] x +
    (-1 + x ^ 4 - 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero, zero] x +
    (-2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) / x ^ 2 * hpl [zero, zero, negOne, zero] x +
    (-3 - 24 * x + 3 * x ^ 4 + 24 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero, negOne] x +
    (12) * hpl [zero, zero, negOne, zero, zero] x +
    (24) * hpl [zero, zero, zero, negOne, zero] x +
    (36) * hpl [zero, zero, zero, zero, negOne] x

theorem continuousOn_i8Psi4s9S0 : ContinuousOn i8Psi4s9S0 (Ioc 0 1) := by
  unfold i8Psi4s9S0
  exact ((((((((((((((((i13_cont_coef (p := fun x => -35 / 8 * x + 13 / 8 * x ^ 4 +
    541 / 8 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -19 / 8 - 40 * x - 40 * x ^ 3 - 301 / 4 * x ^ 2 -
        19 / 8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -30 * x ^ 3 - 2 * x - 7 / 8 * x ^ 4 +
        301 / 8 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -3 / 2 - 24 * x + 24 * x ^ 3 +
        3 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -19 / 4 - 40 * x + 40 * x ^ 3 +
        19 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -x / 2 + x ^ 4 / 4 + 15 / 2 * x ^ 3 +
        45 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 - 15 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -3 - 24 * x - 24 * x ^ 3 - 3 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -11 / 2 - 40 * x - 40 * x ^ 3 - 8 * x ^ 2 -
        11 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4 - 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -3 - 24 * x + 3 * x ^ 4 + 24 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, negOne])))

theorem i8Psi4s9_eq_S (x : ℝ) : i8Psi4s9 x = i8Psi4s9S0 x := by
  unfold i8Psi4s9 i8Psi4s9S0 i8Psi4s9N0 i8Psi4s9N1 i8Psi4s9N2 i8Psi4s9N3 i8Psi4s9N4 i8Psi4s9W
  ring

theorem continuousOn_i8Psi4s9 : ContinuousOn i8Psi4s9 (Ioc 0 1) := by
  rw [show i8Psi4s9 = fun x => i8Psi4s9S0 x from funext i8Psi4s9_eq_S]
  exact continuousOn_i8Psi4s9S0

theorem i8Psi4s9_one : i8Psi4s9 1 = 519 / 8 - 160 * Real.log 2 - 69 / 4 * zeta3 +
    45 / 4 * zeta5 := by
  rw [i8Psi4s9_eq_S]
  unfold i8Psi4s9S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_at_one,
    hpl_zero_zero_negOne_zero_zero_at_one, hpl_zero_zero_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s10` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s10S0 (x : ℝ) : ℝ :=
    (9 * x ^ 3 + 30 * x - 85 / 8 * x ^ 4 - π ^ 2 * x - 4 * x * zeta3 - 4 * zeta3 * x ^ 3 -
      2 * zeta3 * x ^ 4 - 5 / 12 * π ^ 2 * x ^ 4 - 2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 +
    (π ^ 2 * x ^ 2 + π ^ 2 * x ^ 4 / 3 + 2 / 3 * π ^ 2 * x +
      2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (7 * x ^ 3 + 14 * x + 16 * x ^ 2 + 21 / 4 * x ^ 4 + 4 * zeta3 * x ^ 2 - π ^ 2 * x / 3 -
      π ^ 2 * x ^ 3 / 3 - π ^ 2 * x ^ 4 / 6) / x ^ 2 * hpl [zero] x +
    (-15 * x ^ 2 - 12 * x - 8 * x ^ 3 - 5 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-2 / 3 * π ^ 2) * hpl [zero, negOne] x +
    (4 * x ^ 2 + 4 * x ^ 3 + 6 * x + 5 / 2 * x ^ 4 +
      π ^ 2 * x ^ 2 / 3) / x ^ 2 * hpl [zero, zero] x +
    (4 * x ^ 4 + 8 * x + 8 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (-6 * x ^ 2 - 4 * x - 4 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-4 * x - 4 * x ^ 3 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero] x +
    (x ^ 4 + 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [zero, zero, zero] x +
    (-8) * hpl [zero, negOne, negOne, zero] x +
    (4) * hpl [zero, negOne, zero, zero] x +
    (4) * hpl [zero, zero, negOne, zero] x +
    (-2) * hpl [zero, zero, zero, zero] x

theorem continuousOn_i8Psi4s10S0 : ContinuousOn i8Psi4s10S0 (Ioc 0 1) := by
  unfold i8Psi4s10S0
  exact ((((((((((((((i13_cont_coef (p := fun x => 9 * x ^ 3 + 30 * x - 85 / 8 * x ^ 4 -
    π ^ 2 * x - 4 * x * zeta3 - 4 * zeta3 * x ^ 3 - 2 * zeta3 * x ^ 4 - 5 / 12 * π ^ 2 * x ^ 4 -
    2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => π ^ 2 * x ^ 2 + π ^ 2 * x ^ 4 / 3 + 2 / 3 * π ^ 2 * x +
        2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 7 * x ^ 3 + 14 * x + 16 * x ^ 2 + 21 / 4 * x ^ 4 +
        4 * zeta3 * x ^ 2 - π ^ 2 * x / 3 - π ^ 2 * x ^ 3 / 3 -
        π ^ 2 * x ^ 4 / 6) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -15 * x ^ 2 - 12 * x - 8 * x ^ 3 -
        5 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 2 + 4 * x ^ 3 + 6 * x + 5 / 2 * x ^ 4 +
        π ^ 2 * x ^ 2 / 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 4 * x ^ 4 + 8 * x + 8 * x ^ 3 + 12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -6 * x ^ 2 - 4 * x - 4 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x - 4 * x ^ 3 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero])))

theorem i8Psi4s10_eq_S (x : ℝ) : i8Psi4s10 x = i8Psi4s10S0 x := by
  unfold i8Psi4s10 i8Psi4s10S0 i8Psi4s10N0 i8Psi4s10N1 i8Psi4s10N2 i8Psi4s10N3 i8Psi4s10N4
    i8Psi4s10W
  ring

theorem continuousOn_i8Psi4s10 : ContinuousOn i8Psi4s10 (Ioc 0 1) := by
  rw [show i8Psi4s10 = fun x => i8Psi4s10S0 x from funext i8Psi4s10_eq_S]
  exact continuousOn_i8Psi4s10S0

theorem i8Psi4s10_one : i8Psi4s10 1 = 227 / 8 - 3 * zeta3 - π ^ 4 / 36 + 5 / 4 * π ^ 2 := by
  rw [i8Psi4s10_eq_S]
  unfold i8Psi4s10S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_negOne_zero_at_one, hpl_negOne_zero_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_zero_zero_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s11` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s11S0 (x : ℝ) : ℝ :=
    (-8 * x - 4 * x ^ 4 + 8 * x ^ 3 - π ^ 2 * x ^ 3 - zeta3 * x ^ 4 - 6 * zeta3 * x ^ 3 +
      2 * x * zeta3 - π ^ 2 * x ^ 4 / 6 + π ^ 2 * x / 3) / x ^ 2 +
    (-8 + 2 * zeta3 + 8 * x ^ 4 + π ^ 2 / 3 + 2 * π ^ 2 * x ^ 2 + 2 * zeta3 * x ^ 4 +
      8 * x * zeta3 + 8 * zeta3 * x ^ 3 + 12 * zeta3 * x ^ 2 + π ^ 2 * x ^ 4 / 3 +
      4 / 3 * π ^ 2 * x + 4 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (-8 - π ^ 2 - 6 * zeta3) * hpl [zero] x +
    (-32) * hpl [zero, negOne] x

theorem continuousOn_i8Psi4s11S0 : ContinuousOn i8Psi4s11S0 (Ioc 0 1) := by
  unfold i8Psi4s11S0
  exact ((((i13_cont_coef (p := fun x => -8 * x - 4 * x ^ 4 + 8 * x ^ 3 - π ^ 2 * x ^ 3 -
    zeta3 * x ^ 4 - 6 * zeta3 * x ^ 3 + 2 * x * zeta3 - π ^ 2 * x ^ 4 / 6 +
    π ^ 2 * x / 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -8 + 2 * zeta3 + 8 * x ^ 4 + π ^ 2 / 3 + 2 * π ^ 2 * x ^ 2 +
        2 * zeta3 * x ^ 4 + 8 * x * zeta3 + 8 * zeta3 * x ^ 3 + 12 * zeta3 * x ^ 2 +
        π ^ 2 * x ^ 4 / 3 + 4 / 3 * π ^ 2 * x + 4 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne])))

theorem i8Psi4s11_eq_S (x : ℝ) : i8Psi4s11 x = i8Psi4s11S0 x := by
  unfold i8Psi4s11 i8Psi4s11S0 i8Psi4s11N0 i8Psi4s11N1 i8Psi4s11N2 i8Psi4s11N3 i8Psi4s11N4
    i8Psi4s11W
  ring

theorem continuousOn_i8Psi4s11 : ContinuousOn i8Psi4s11 (Ioc 0 1) := by
  rw [show i8Psi4s11 = fun x => i8Psi4s11S0 x from funext i8Psi4s11_eq_S]
  exact continuousOn_i8Psi4s11S0

theorem i8Psi4s11_one : i8Psi4s11 1 = -4 - 5 * zeta3 - 7 / 2 * π ^ 2 + 32 * Real.log 2 * zeta3 +
    16 / 3 * Real.log 2 * π ^ 2 := by
  rw [i8Psi4s11_eq_S]
  unfold i8Psi4s11S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s12` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s12S0 (x : ℝ) : ℝ :=
    (-26 * x ^ 3 - 6 * x - 2 * x ^ 4 + π ^ 2 * x / 4 + π ^ 2 * x ^ 4 / 12 +
      13 / 12 * π ^ 2 * x ^ 3) / x ^ 2 +
    (-2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3 + π ^ 2 / 12 - 2 / 3 * π ^ 2 * x ^ 3 -
      π ^ 2 * x ^ 4 / 12 + 2 / 3 * π ^ 2 * x) / x ^ 2 * hpl [negOne] x +
    (-4 * x + 2 * x ^ 4 + 12 * x ^ 3 + 14 * x ^ 2 - 7 / 12 * π ^ 2 * x ^ 2 - π ^ 2 * x ^ 3 / 2 -
      π ^ 2 * x ^ 4 / 12 + π ^ 2 * x / 6) / x ^ 2 * hpl [zero] x +
    (-4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4 + π ^ 2 / 6 + π ^ 2 * x ^ 2 +
      π ^ 2 * x ^ 4 / 6 + 2 / 3 * π ^ 2 * x +
      2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (-4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4 + π ^ 2 / 6 + π ^ 2 * x ^ 4 / 6 + 2 / 3 * π ^ 2 * x +
      2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (12 - π ^ 2 / 2) * hpl [zero, zero] x

theorem continuousOn_i8Psi4s12S0 : ContinuousOn i8Psi4s12S0 (Ioc 0 1) := by
  unfold i8Psi4s12S0
  exact ((((((i13_cont_coef (p := fun x => -26 * x ^ 3 - 6 * x - 2 * x ^ 4 + π ^ 2 * x / 4 +
    π ^ 2 * x ^ 4 / 12 + 13 / 12 * π ^ 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -2 - 16 * x + 2 * x ^ 4 + 16 * x ^ 3 + π ^ 2 / 12 -
        2 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 12 + 2 / 3 * π ^ 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -4 * x + 2 * x ^ 4 + 12 * x ^ 3 + 14 * x ^ 2 -
        7 / 12 * π ^ 2 * x ^ 2 - π ^ 2 * x ^ 3 / 2 - π ^ 2 * x ^ 4 / 12 +
        π ^ 2 * x / 6) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4 +
        π ^ 2 / 6 + π ^ 2 * x ^ 2 + π ^ 2 * x ^ 4 / 6 + 2 / 3 * π ^ 2 * x +
        2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4 + π ^ 2 / 6 +
        π ^ 2 * x ^ 4 / 6 + 2 / 3 * π ^ 2 * x + 2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero])))

theorem i8Psi4s12_eq_S (x : ℝ) : i8Psi4s12 x = i8Psi4s12S0 x := by
  unfold i8Psi4s12 i8Psi4s12S0 i8Psi4s12N0 i8Psi4s12N1 i8Psi4s12N2 i8Psi4s12N3 i8Psi4s12N4
    i8Psi4s12W
  ring

theorem continuousOn_i8Psi4s12 : ContinuousOn i8Psi4s12 (Ioc 0 1) := by
  rw [show i8Psi4s12 = fun x => i8Psi4s12S0 x from funext i8Psi4s12_eq_S]
  exact continuousOn_i8Psi4s12S0

theorem i8Psi4s12_one : i8Psi4s12 1 = -34 - π ^ 4 / 12 + 41 / 12 * π ^ 2 := by
  rw [i8Psi4s12_eq_S]
  unfold i8Psi4s12S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s13` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s13S0 (x : ℝ) : ℝ :=
    (-5 / 3 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 4 / 6) / x ^ 2 +
    (π ^ 2 * x ^ 2 + 2 * π ^ 2 * x ^ 3 - 2 / 3 * π ^ 2 * x +
      π ^ 2 * x ^ 4 / 3) / x ^ 2 * hpl [negOne] x +
    (2 / 3 * π ^ 2) * hpl [zero] x +
    (-2 / 3 * π ^ 2 - 4 * π ^ 2 * x ^ 2 - 8 / 3 * π ^ 2 * x - 8 / 3 * π ^ 2 * x ^ 3 -
      2 / 3 * π ^ 2 * x ^ 4) / x ^ 2 * hpl [negOne, negOne] x +
    (2 * π ^ 2) * hpl [zero, negOne] x

theorem continuousOn_i8Psi4s13S0 : ContinuousOn i8Psi4s13S0 (Ioc 0 1) := by
  unfold i8Psi4s13S0
  exact (((((i13_cont_coef (p := fun x => -5 / 3 * π ^ 2 * x ^ 3 -
    π ^ 2 * x ^ 4 / 6) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => π ^ 2 * x ^ 2 + 2 * π ^ 2 * x ^ 3 - 2 / 3 * π ^ 2 * x +
        π ^ 2 * x ^ 4 / 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -2 / 3 * π ^ 2 - 4 * π ^ 2 * x ^ 2 - 8 / 3 * π ^ 2 * x -
        8 / 3 * π ^ 2 * x ^ 3 - 2 / 3 * π ^ 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne])))

theorem i8Psi4s13_eq_S (x : ℝ) : i8Psi4s13 x = i8Psi4s13S0 x := by
  unfold i8Psi4s13 i8Psi4s13S0 i8Psi4s13N0 i8Psi4s13N1 i8Psi4s13N2 i8Psi4s13N3 i8Psi4s13N4
    i8Psi4s13W
  ring

theorem continuousOn_i8Psi4s13 : ContinuousOn i8Psi4s13 (Ioc 0 1) := by
  rw [show i8Psi4s13 = fun x => i8Psi4s13S0 x from funext i8Psi4s13_eq_S]
  exact continuousOn_i8Psi4s13S0

theorem i8Psi4s13_one : i8Psi4s13 1 = -11 / 6 * π ^ 2 + π ^ 4 / 6 -
    16 / 3 * π ^ 2 * Real.log 2 ^ 2 + 8 / 3 * Real.log 2 * π ^ 2 := by
  rw [i8Psi4s13_eq_S]
  unfold i8Psi4s13S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_negOne_at_one, hpl_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s14` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s14S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 + 101 / 4 * x ^ 3) / x ^ 2 +
    (x - 7 * x ^ 3 - 23 / 4 * x ^ 2 - x ^ 4 / 4) / x ^ 2 * hpl [negOne] x +
    (-x ^ 2 - 37 / 2 * x ^ 3 - 3 / 4 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (4 * x + 20 * x ^ 3 + 3 / 2 * x ^ 4 + 45 / 2 * x ^ 2) / x ^ 2 * hpl [negOne, zero] x +
    (x + x ^ 4 / 2 + 7 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (-4) * hpl [zero, zero] x +
    (2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (1 - x ^ 4 - 8 * x ^ 3 + 8 * x) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (-x ^ 4 - 14 * x ^ 2 - 6 * x ^ 3 + 2 * x) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-7) * hpl [zero, zero, negOne] x +
    (2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne, zero] x +
    (4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3) / x ^ 2 * hpl [zero, negOne, negOne, zero] x +
    (2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3) / x ^ 2 * hpl [zero, negOne, zero, negOne] x +
    (-6) * hpl [zero, zero, negOne, zero] x

theorem continuousOn_i8Psi4s14S0 : ContinuousOn i8Psi4s14S0 (Ioc 0 1) := by
  unfold i8Psi4s14S0
  exact ((((((((((((((i13_cont_coef (p := fun x => x ^ 4 / 2 + 101 / 4 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x - 7 * x ^ 3 - 23 / 4 * x ^ 2 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 2 - 37 / 2 * x ^ 3 - 3 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 4 * x + 20 * x ^ 3 + 3 / 2 * x ^ 4 +
        45 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x + x ^ 4 / 2 + 7 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 2 - 16 * x ^ 3 - 2 * x ^ 4 + 16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4 - 8 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 14 * x ^ 2 - 6 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3 +
        12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 4 + 4 * x ^ 4 + 16 * x + 16 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x ^ 4 + 8 * x + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero])))

theorem i8Psi4s14_eq_S (x : ℝ) : i8Psi4s14 x = i8Psi4s14S0 x := by
  unfold i8Psi4s14 i8Psi4s14S0 i8Psi4s14N0 i8Psi4s14N1 i8Psi4s14N2 i8Psi4s14N3 i8Psi4s14N4
    i8Psi4s14W
  ring

theorem continuousOn_i8Psi4s14 : ContinuousOn i8Psi4s14 (Ioc 0 1) := by
  rw [show i8Psi4s14 = fun x => i8Psi4s14S0 x from funext i8Psi4s14_eq_S]
  exact continuousOn_i8Psi4s14S0

theorem i8Psi4s14_one : i8Psi4s14 1 = 103 / 4 - 12 * Real.log 2 + 2 * Real.log 2 ^ 4 +
    48 * Li 4 (1 / 2) - 79 / 24 * π ^ 2 - 17 / 60 * π ^ 4 + 93 / 4 * zeta3 -
    6 * Real.log 2 * zeta3 - 2 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s14_eq_S]
  unfold i8Psi4s14S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_negOne_zero_at_one, hpl_negOne_zero_negOne_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one, hpl_negOne_zero_negOne_zero_at_one,
    hpl_zero_negOne_negOne_zero_at_one, hpl_zero_negOne_zero_negOne_at_one,
    hpl_zero_zero_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s15` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s15S0 (x : ℝ) : ℝ :=
    (-x ^ 4 - 73 / 2 * x ^ 3) / x ^ 2 +
    (x ^ 4 / 2 + 10 * x ^ 3 + 19 / 2 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (27 * x ^ 3 + 3 / 2 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (-30 * x ^ 3 - 27 * x ^ 2 - 3 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-x ^ 4 - 10 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (-12 * x + 6 * x ^ 4 + 18 * x ^ 2 + 36 * x ^ 3) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (-4 * x + 2 * x ^ 4 + 6 * x ^ 2 + 12 * x ^ 3) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (12) * hpl [zero, negOne, zero] x +
    (4) * hpl [zero, zero, negOne] x +
    (-12 - 72 * x ^ 2 - 48 * x - 48 * x ^ 3 -
      12 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, negOne, zero] x +
    (-4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
      4 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, zero, negOne] x +
    (36) * hpl [zero, negOne, negOne, zero] x +
    (12) * hpl [zero, negOne, zero, negOne] x

theorem continuousOn_i8Psi4s15S0 : ContinuousOn i8Psi4s15S0 (Ioc 0 1) := by
  unfold i8Psi4s15S0
  exact (((((((((((((i13_cont_coef (p := fun x => -x ^ 4 - 73 / 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 10 * x ^ 3 + 19 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 27 * x ^ 3 + 3 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -30 * x ^ 3 - 27 * x ^ 2 - 3 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 10 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -12 * x + 6 * x ^ 4 + 18 * x ^ 2 +
        36 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -4 * x + 2 * x ^ 4 + 6 * x ^ 2 + 12 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -12 - 72 * x ^ 2 - 48 * x - 48 * x ^ 3 -
        12 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -4 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 -
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne])))

theorem i8Psi4s15_eq_S (x : ℝ) : i8Psi4s15 x = i8Psi4s15S0 x := by
  unfold i8Psi4s15 i8Psi4s15S0 i8Psi4s15N0 i8Psi4s15N1 i8Psi4s15N2 i8Psi4s15N3 i8Psi4s15N4
    i8Psi4s15W
  ring

theorem continuousOn_i8Psi4s15 : ContinuousOn i8Psi4s15 (Ioc 0 1) := by
  rw [show i8Psi4s15 = fun x => i8Psi4s15S0 x from funext i8Psi4s15_eq_S]
  exact continuousOn_i8Psi4s15S0

theorem i8Psi4s15_one : i8Psi4s15 1 = -75 / 2 - 48 * Li 4 (1 / 2) - 13 * zeta3 -
    2 * Real.log 2 ^ 4 + 20 * Real.log 2 + 5 / 12 * π ^ 4 + 49 / 12 * π ^ 2 -
    50 * Real.log 2 * zeta3 - 8 / 3 * Real.log 2 * π ^ 2 + 22 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  rw [i8Psi4s15_eq_S]
  unfold i8Psi4s15S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_negOne_negOne_zero_at_one, hpl_negOne_zero_negOne_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_negOne_negOne_negOne_zero_at_one,
    hpl_negOne_negOne_zero_negOne_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_zero_negOne_at_one]
  norm_num
  ring

end QED.ThreeLoopD
