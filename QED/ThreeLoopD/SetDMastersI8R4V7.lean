/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4V6

/-!
# Set (d), master `I₈`: continuity and values at `1` of the sub-pieces 110 to 118 of `Ψ₄`

Each sub-piece `Ψ₄⁽ⁿ⁾` is continuous on `(0, 1]` (the words beginning with `1` carry a factor
`1 - ξ`), and its value at `ξ = 1` follows from the values of the harmonic polylogarithms at `1`.

## Main results

* `QED.ThreeLoopD.continuousOn_i8Psi4s110`, `QED.ThreeLoopD.i8Psi4s110_one` and their
  companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- Chunk 0 of `i8Psi4s110` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s110S0 (x : ℝ) : ℝ :=
    (-7 / 8 * x - 3 / 16 * x ^ 4 + 7 / 8 * x ^ 3) / x ^ 2 +
    (-1 / 8 + x ^ 4 / 8) / x ^ 2 * hpl [negOne] x +
    (-3 / 4 * x - 3 / 4 * x ^ 3 - x ^ 2 / 8 + x ^ 4 / 4) / x ^ 2 * hpl [zero] x +
    (-1 / 4 + x ^ 2 / 2 - x ^ 4 / 4) / x ^ 2 * hpl [negOne, zero] x +
    (-1 / 4 - x ^ 4 / 4) / x ^ 2 * hpl [zero, negOne] x +
    (x ^ 3 / 2 - x / 2 - x ^ 2 / 4 - x ^ 4 / 4) / x ^ 2 * hpl [zero, zero] x +
    (-1 / 2 + x ^ 4 / 2) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-1 / 2 + x ^ 4 / 2) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-1 / 2 + x ^ 4 / 2) / x ^ 2 * hpl [zero, zero, negOne] x +
    (-1 / 2) * hpl [zero, zero, zero] x +
    (-2) * hpl [zero, negOne, zero, zero] x +
    (-2) * hpl [zero, zero, negOne, zero] x +
    (-2) * hpl [zero, zero, zero, negOne] x

theorem continuousOn_i8Psi4s110S0 : ContinuousOn i8Psi4s110S0 (Ioc 0 1) := by
  unfold i8Psi4s110S0
  exact (((((((((((((i13_cont_coef (p := fun x => -7 / 8 * x - 3 / 16 * x ^ 4 +
    7 / 8 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -1 / 8 + x ^ 4 / 8) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -3 / 4 * x - 3 / 4 * x ^ 3 - x ^ 2 / 8 +
        x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -1 / 4 + x ^ 2 / 2 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 4 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 - x / 2 - x ^ 2 / 4 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne])))

theorem i8Psi4s110_eq_S (x : ℝ) : i8Psi4s110 x = i8Psi4s110S0 x := by
  unfold i8Psi4s110 i8Psi4s110S0 i8Psi4s110N0 i8Psi4s110N1 i8Psi4s110N2 i8Psi4s110N3 i8Psi4s110N4
    i8Psi4s110W
  ring

theorem continuousOn_i8Psi4s110 : ContinuousOn i8Psi4s110 (Ioc 0 1) := by
  rw [show i8Psi4s110 = fun x => i8Psi4s110S0 x from funext i8Psi4s110_eq_S]
  exact continuousOn_i8Psi4s110S0

theorem i8Psi4s110_one : i8Psi4s110 1 = -3 / 16 - 7 / 360 * π ^ 4 - π ^ 2 / 24 := by
  rw [i8Psi4s110_eq_S]
  unfold i8Psi4s110S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s111k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s111k0S0 (x : ℝ) : ℝ :=
    (-x ^ 4 / 4 + 37 / 8 * x ^ 3) / x ^ 2 +
    (x - x ^ 3 - x ^ 2 / 8 + x ^ 4 / 8) / x ^ 2 * hpl [negOne] x +
    (-x ^ 2 - 7 / 2 * x ^ 3 + 3 / 8 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (-x ^ 4 / 2 + 3 / 2 * x + 3 / 2 * x ^ 3 + 7 / 2 * x ^ 2) / x ^ 2 * hpl [negOne, zero] x +
    (x + x ^ 3 - x ^ 4 / 4) / x ^ 2 * hpl [zero, negOne] x +
    (-3 / 2 * x ^ 2 - x ^ 4 / 4 + 3 / 2 * x ^ 3) / x ^ 2 * hpl [zero, zero] x +
    (1 / 2 + x ^ 4 / 2 - x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (x + x ^ 4 / 2 - x ^ 3 - x ^ 2 / 2) / x ^ 2 * hpl [negOne, zero, zero] x +
    (x + x ^ 2 / 2 + x ^ 4 / 2 - x ^ 3) / x ^ 2 * hpl [zero, negOne, zero] x +
    (x + x ^ 4 / 2 - x ^ 3) / x ^ 2 * hpl [zero, zero, negOne] x +
    (-1) * hpl [zero, zero, zero] x +
    (1 - x ^ 4) / x ^ 2 * hpl [negOne, negOne, zero, zero] x +
    (1 - x ^ 4) / x ^ 2 * hpl [negOne, zero, negOne, zero] x +
    (1 - x ^ 4) / x ^ 2 * hpl [negOne, zero, zero, negOne] x +
    (1 - x ^ 4) / x ^ 2 * hpl [zero, negOne, negOne, zero] x +
    (1) * hpl [zero, negOne, zero, zero] x +
    (1) * hpl [zero, zero, negOne, zero] x +
    (1) * hpl [zero, zero, zero, negOne] x +
    (4) * hpl [zero, negOne, negOne, zero, zero] x +
    (4) * hpl [zero, negOne, zero, negOne, zero] x

theorem continuousOn_i8Psi4s111k0S0 : ContinuousOn i8Psi4s111k0S0 (Ioc 0 1) := by
  unfold i8Psi4s111k0S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -x ^ 4 / 4 +
    37 / 8 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x - x ^ 3 - x ^ 2 / 8 + x ^ 4 / 8) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 2 - 7 / 2 * x ^ 3 + 3 / 8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 / 2 + 3 / 2 * x + 3 / 2 * x ^ 3 +
        7 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x + x ^ 3 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -3 / 2 * x ^ 2 - x ^ 4 / 4 + 3 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 1 / 2 + x ^ 4 / 2 - x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => x + x ^ 4 / 2 - x ^ 3 - x ^ 2 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => x + x ^ 2 / 2 + x ^ 4 / 2 - x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => x + x ^ 4 / 2 - x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne, zero])))

/-- Chunk 1 of `i8Psi4s111k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s111k0S1 (x : ℝ) : ℝ :=
    (4) * hpl [zero, negOne, zero, zero, negOne] x +
    (4) * hpl [zero, zero, negOne, negOne, zero] x

theorem continuousOn_i8Psi4s111k0S1 : ContinuousOn i8Psi4s111k0S1 (Ioc 0 1) := by
  unfold i8Psi4s111k0S1
  exact ((continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero, negOne])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne, zero])))

theorem i8Psi4s111k0_eq_S (x : ℝ) : i8Psi4s111k0 x = i8Psi4s111k0S0 x + i8Psi4s111k0S1 x := by
  unfold i8Psi4s111k0 i8Psi4s111k0S0 i8Psi4s111k0S1 i8Psi4s111k0N0 i8Psi4s111k0N1 i8Psi4s111k0N2
    i8Psi4s111k0N3 i8Psi4s111k0N4 i8Psi4s111k0W
  ring

theorem continuousOn_i8Psi4s111k0 : ContinuousOn i8Psi4s111k0 (Ioc 0 1) := by
  rw [show i8Psi4s111k0 = fun x => i8Psi4s111k0S0 x +
    i8Psi4s111k0S1 x from funext i8Psi4s111k0_eq_S]
  exact (continuousOn_i8Psi4s111k0S0.add continuousOn_i8Psi4s111k0S1)

theorem i8Psi4s111k0_one : i8Psi4s111k0 1 = 35 / 8 - 41 / 8 * zeta5 - 17 / 48 * π ^ 2 -
    9 / 8 * zeta3 + 7 / 720 * π ^ 4 + 5 / 12 * π ^ 2 * zeta3 := by
  rw [i8Psi4s111k0_eq_S]
  unfold i8Psi4s111k0S0 i8Psi4s111k0S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_negOne_zero_at_one, hpl_negOne_zero_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one,
    hpl_negOne_negOne_zero_zero_at_one, hpl_negOne_zero_negOne_zero_at_one,
    hpl_negOne_zero_zero_negOne_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_negOne_at_one, hpl_zero_negOne_negOne_zero_zero_at_one,
    hpl_zero_negOne_zero_negOne_zero_at_one, hpl_zero_negOne_zero_zero_negOne_at_one,
    hpl_zero_zero_negOne_negOne_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s111k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s111k1S0 (x : ℝ) : ℝ :=
    (x ^ 3 - x ^ 4 / 8) / x ^ 2 +
    (-3 / 4 * x ^ 3 - x ^ 2 / 4 + x ^ 4 / 4 + 3 / 4 * x) / x ^ 2 * hpl [negOne] x +
    (-3 / 4) * hpl [zero] x +
    (1 / 4 - x ^ 4 / 4) / x ^ 2 * hpl [negOne, negOne] x +
    (x / 2 + x ^ 3 / 2 - x ^ 4 / 4 + x ^ 2 / 4) / x ^ 2 * hpl [zero, negOne] x +
    (1 / 2 + x ^ 4 / 2 - x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (1 / 2 + x ^ 4 / 2) / x ^ 2 * hpl [zero, negOne, negOne] x +
    (1 / 2) * hpl [zero, zero, negOne] x +
    (1 - x ^ 4) / x ^ 2 * hpl [zero, negOne, zero, negOne] x +
    (1 - x ^ 4) / x ^ 2 * hpl [zero, zero, negOne, negOne] x +
    (4) * hpl [zero, zero, negOne, zero, negOne] x +
    (4) * hpl [zero, zero, zero, negOne, negOne] x

theorem continuousOn_i8Psi4s111k1S0 : ContinuousOn i8Psi4s111k1S0 (Ioc 0 1) := by
  unfold i8Psi4s111k1S0
  exact ((((((((((((i13_cont_coef (p := fun x => x ^ 3 - x ^ 4 / 8) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -3 / 4 * x ^ 3 - x ^ 2 / 4 + x ^ 4 / 4 +
        3 / 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 1 / 4 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x / 2 + x ^ 3 / 2 - x ^ 4 / 4 + x ^ 2 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => 1 / 2 + x ^ 4 / 2 - x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 1 / 2 + x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne, negOne])))

theorem i8Psi4s111k1_eq_S (x : ℝ) : i8Psi4s111k1 x = i8Psi4s111k1S0 x := by
  unfold i8Psi4s111k1 i8Psi4s111k1S0 i8Psi4s111k1N0 i8Psi4s111k1N1 i8Psi4s111k1N2 i8Psi4s111k1N3
    i8Psi4s111k1N4 i8Psi4s111k1W
  ring

theorem continuousOn_i8Psi4s111k1 : ContinuousOn i8Psi4s111k1 (Ioc 0 1) := by
  rw [show i8Psi4s111k1 = fun x => i8Psi4s111k1S0 x from funext i8Psi4s111k1_eq_S]
  exact continuousOn_i8Psi4s111k1S0

theorem i8Psi4s111k1_one : i8Psi4s111k1 1 = 7 / 8 + zeta3 / 2 + π ^ 2 / 12 + 3 / 2 * zeta5 -
    π ^ 2 * zeta3 / 12 := by
  rw [i8Psi4s111k1_eq_S]
  unfold i8Psi4s111k1S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_negOne_at_one, hpl_zero_negOne_at_one,
    hpl_negOne_zero_negOne_at_one, hpl_zero_negOne_negOne_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_negOne_zero_negOne_at_one, hpl_zero_zero_negOne_negOne_at_one,
    hpl_zero_zero_negOne_zero_negOne_at_one, hpl_zero_zero_zero_negOne_negOne_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s111 : ContinuousOn i8Psi4s111 (Ioc 0 1) := by
  rw [show i8Psi4s111 = fun x => i8Psi4s111k0 x + i8Psi4s111k1 x from rfl]
  exact (continuousOn_i8Psi4s111k0.add continuousOn_i8Psi4s111k1)

theorem i8Psi4s111_one : i8Psi4s111 1 = 21 / 4 - 29 / 8 * zeta5 - 13 / 48 * π ^ 2 -
    5 / 8 * zeta3 + 7 / 720 * π ^ 4 + π ^ 2 * zeta3 / 3 := by
  unfold i8Psi4s111
  rw [i8Psi4s111k0_one, i8Psi4s111k1_one]
  ring

/-- Chunk 0 of `i8Psi4s112` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s112S0 (x : ℝ) : ℝ :=
    (-11 / 16 * x - 11 / 16 * x ^ 3 + 3 / 16 * x ^ 4) / x ^ 2 +
    (-3 / 16 - 3 / 16 * x ^ 4 + 3 / 8 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (x ^ 3 / 2 - 3 / 16 * x ^ 2 - 3 / 16 * x ^ 4 - x / 2) / x ^ 2 * hpl [zero] x +
    (-1 / 4 + x ^ 4 / 4) / x ^ 2 * hpl [negOne, zero] x +
    (-3 / 8 + 3 / 8 * x ^ 4) / x ^ 2 * hpl [zero, negOne] x +
    (-x / 4 - x ^ 2 / 4 - x ^ 3 / 4 + x ^ 4 / 8) / x ^ 2 * hpl [zero, zero] x +
    (-1 / 4 + x ^ 2 / 2 - x ^ 4 / 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-1 / 2 - x ^ 4 / 2) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-3 / 4 - 3 / 4 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne] x +
    (-1 / 4) * hpl [zero, zero, zero] x +
    (-1 / 2 + x ^ 4 / 2) / x ^ 2 * hpl [zero, negOne, zero, zero] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [zero, zero, negOne, zero] x +
    (-3 / 2 + 3 / 2 * x ^ 4) / x ^ 2 * hpl [zero, zero, zero, negOne] x +
    (-2) * hpl [zero, zero, negOne, zero, zero] x +
    (-4) * hpl [zero, zero, zero, negOne, zero] x +
    (-6) * hpl [zero, zero, zero, zero, negOne] x

theorem continuousOn_i8Psi4s112S0 : ContinuousOn i8Psi4s112S0 (Ioc 0 1) := by
  unfold i8Psi4s112S0
  exact ((((((((((((((((i13_cont_coef (p := fun x => -11 / 16 * x - 11 / 16 * x ^ 3 +
    3 / 16 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -3 / 16 - 3 / 16 * x ^ 4 + 3 / 8 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 - 3 / 16 * x ^ 2 - 3 / 16 * x ^ 4 -
        x / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -1 / 4 + x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -3 / 8 + 3 / 8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -x / 4 - x ^ 2 / 4 - x ^ 3 / 4 + x ^ 4 / 8) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 4 + x ^ 2 / 2 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -3 / 4 - 3 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -3 / 2 + 3 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, negOne])))

theorem i8Psi4s112_eq_S (x : ℝ) : i8Psi4s112 x = i8Psi4s112S0 x := by
  unfold i8Psi4s112 i8Psi4s112S0 i8Psi4s112N0 i8Psi4s112N1 i8Psi4s112N2 i8Psi4s112N3 i8Psi4s112N4
    i8Psi4s112W
  ring

theorem continuousOn_i8Psi4s112 : ContinuousOn i8Psi4s112 (Ioc 0 1) := by
  rw [show i8Psi4s112 = fun x => i8Psi4s112S0 x from funext i8Psi4s112_eq_S]
  exact continuousOn_i8Psi4s112S0

theorem i8Psi4s112_one : i8Psi4s112 1 = -19 / 16 - 15 / 8 * zeta5 + 3 / 8 * zeta3 := by
  rw [i8Psi4s112_eq_S]
  unfold i8Psi4s112S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_at_one,
    hpl_zero_zero_negOne_zero_zero_at_one, hpl_zero_zero_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_zero_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s113` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s113S0 (x : ℝ) : ℝ :=
    (x ^ 4 - 5 * x ^ 3) / x ^ 2 +
    (-x ^ 4 - 4 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-x ^ 3 + 3 * x ^ 2 + 4 * x) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-4) * hpl [zero, zero] x +
    (-2 * x ^ 4 + 4 * x + 4 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-2 * x ^ 2 + 2 * x ^ 3 + 4 * x) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (4) * hpl [zero, zero, one] x +
    (4) * hpl [zero, one, zero] x

theorem continuousOn_i8Psi4s113S0 : ContinuousOn i8Psi4s113S0 (Ioc 0 1) := by
  unfold i8Psi4s113S0
  exact ((((((((i13_cont_coef (p := fun x => x ^ 4 - 5 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 4 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 + 3 * x ^ 2 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 4 + 4 * x + 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 2 + 2 * x ^ 3 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero])))

theorem i8Psi4s113_eq_S (x : ℝ) : i8Psi4s113 x = i8Psi4s113S0 x := by
  unfold i8Psi4s113 i8Psi4s113S0 i8Psi4s113N0 i8Psi4s113N1 i8Psi4s113N2 i8Psi4s113N3 i8Psi4s113N4
    i8Psi4s113W
  ring

theorem continuousOn_i8Psi4s113 : ContinuousOn i8Psi4s113 (Ioc 0 1) := by
  rw [show i8Psi4s113 = fun x => i8Psi4s113S0 x from funext i8Psi4s113_eq_S]
  exact continuousOn_i8Psi4s113S0

theorem i8Psi4s113_one : i8Psi4s113 1 = -4 + π ^ 2 - 4 * zeta3 := by
  rw [i8Psi4s113_eq_S]
  unfold i8Psi4s113S0
  rw [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_one_at_one,
    hpl_zero_one_zero_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s114k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s114k0S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 - 5 / 4 * x ^ 3) / x ^ 2 +
    (-3 / 4 * x ^ 2 - x / 2 - x ^ 3 / 2 - x ^ 4 / 4) / x ^ 2 * hpl [negOne] x +
    (x ^ 3 / 2 + 2 * x ^ 2 - x ^ 4 / 4) / x ^ 2 * hpl [zero] x +
    (x ^ 2 - 3 / 2 * x - x ^ 3 / 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-1 / 2 + x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [negOne, one] x +
    (1 / 2) * hpl [zero, negOne] x +
    (1) * hpl [zero, zero] x +
    (x ^ 3 - x - x ^ 2 / 2 - x ^ 4 / 2) / x ^ 2 * hpl [zero, one] x +
    (-1 / 2 + x ^ 2 / 2 + x ^ 3 / 2 - x / 2) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (x ^ 3 / 2 - x - x ^ 2 / 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-1 + x ^ 4) / x ^ 2 * hpl [negOne, zero, one] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [negOne, one, zero] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [zero, negOne, one] x +
    (-1) * hpl [zero, zero, one] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [zero, one, negOne] x +
    (-1) * hpl [zero, one, zero] x +
    (-4) * hpl [zero, negOne, zero, one] x +
    (-4) * hpl [zero, negOne, one, zero] x +
    (-4) * hpl [zero, zero, negOne, one] x +
    (-4) * hpl [zero, zero, one, negOne] x

theorem continuousOn_i8Psi4s114k0S0 : ContinuousOn i8Psi4s114k0S0 (Ioc 0 1) := by
  unfold i8Psi4s114k0S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 / 2 -
    5 / 4 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -3 / 4 * x ^ 2 - x / 2 - x ^ 3 / 2 -
        x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 + 2 * x ^ 2 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 2 - 3 / 2 * x - x ^ 3 / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - x - x ^ 2 / 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 2 / 2 + x ^ 3 / 2 - x / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 - x - x ^ 2 / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
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

theorem i8Psi4s114k0_eq_S (x : ℝ) : i8Psi4s114k0 x = i8Psi4s114k0S0 x := by
  unfold i8Psi4s114k0 i8Psi4s114k0S0 i8Psi4s114k0N0 i8Psi4s114k0N1 i8Psi4s114k0N2 i8Psi4s114k0N3
    i8Psi4s114k0N4 i8Psi4s114k0W
  ring

theorem continuousOn_i8Psi4s114k0 : ContinuousOn i8Psi4s114k0 (Ioc 0 1) := by
  rw [show i8Psi4s114k0 = fun x => i8Psi4s114k0S0 x from funext i8Psi4s114k0_eq_S]
  exact continuousOn_i8Psi4s114k0S0

theorem i8Psi4s114k0_one : i8Psi4s114k0 1 = -3 / 4 + zeta3 - 2 * Real.log 2 + 8 * Li 4 (1 / 2) -
    π ^ 2 / 8 + Real.log 2 ^ 4 / 3 + 11 / 360 * π ^ 4 - 7 * Real.log 2 * zeta3 -
    π ^ 2 * Real.log 2 ^ 2 / 3 := by
  rw [i8Psi4s114k0_eq_S]
  unfold i8Psi4s114k0S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_negOne_zero_one_at_one,
    hpl_negOne_one_zero_at_one, hpl_zero_negOne_one_at_one, hpl_zero_zero_one_at_one,
    hpl_zero_one_negOne_at_one, hpl_zero_one_zero_at_one, hpl_zero_negOne_zero_one_at_one,
    hpl_zero_negOne_one_zero_at_one, hpl_zero_zero_negOne_one_at_one,
    hpl_zero_zero_one_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s114k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s114k1S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 4 + 5 / 4 * x ^ 3) / x ^ 2 +
    (-x - x ^ 3 - 7 / 4 * x ^ 2 - x ^ 4 / 4) / x ^ 2 * hpl [negOne] x +
    (x ^ 2 - x ^ 3 / 2 - x ^ 4 / 4) / x ^ 2 * hpl [zero] x +
    (x ^ 3 + x ^ 4 / 2 - x - x ^ 2 / 2) / x ^ 2 * hpl [negOne, zero] x +
    (x ^ 3 + x ^ 4 / 2 - x) / x ^ 2 * hpl [zero, negOne] x +
    (1) * hpl [zero, zero] x +
    (1) * hpl [zero, negOne, zero] x +
    (1) * hpl [zero, zero, negOne] x +
    (-1 - x - x ^ 2 - x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (-1 - x - x ^ 2 - x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (-4) * hpl [zero, one, negOne, zero] x +
    (-4) * hpl [zero, one, zero, negOne] x

theorem continuousOn_i8Psi4s114k1S0 : ContinuousOn i8Psi4s114k1S0 (Ioc 0 1) := by
  unfold i8Psi4s114k1S0
  exact ((((((((((((i13_cont_coef (p := fun x => x ^ 4 / 4 + 5 / 4 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -x - x ^ 3 - 7 / 4 * x ^ 2 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 2 - x ^ 3 / 2 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + x ^ 4 / 2 - x - x ^ 2 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + x ^ 4 / 2 - x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 - x - x ^ 2 - x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -1 - x - x ^ 2 - x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne])))

theorem i8Psi4s114k1_eq_S (x : ℝ) : i8Psi4s114k1 x = i8Psi4s114k1S0 x := by
  unfold i8Psi4s114k1 i8Psi4s114k1S0 i8Psi4s114k1N0 i8Psi4s114k1N1 i8Psi4s114k1N2 i8Psi4s114k1N3
    i8Psi4s114k1N4 i8Psi4s114k1W
  ring

theorem continuousOn_i8Psi4s114k1 : ContinuousOn i8Psi4s114k1 (Ioc 0 1) := by
  rw [show i8Psi4s114k1 = fun x => i8Psi4s114k1S0 x from funext i8Psi4s114k1_eq_S]
  exact continuousOn_i8Psi4s114k1S0

theorem i8Psi4s114k1_one : i8Psi4s114k1 1 = 3 / 2 - 4 * Real.log 2 - 19 / 180 * π ^ 4 -
    3 / 4 * zeta3 + π ^ 2 / 24 + 14 * Real.log 2 * zeta3 := by
  rw [i8Psi4s114k1_eq_S]
  unfold i8Psi4s114k1S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_one_negOne_zero_at_one, hpl_zero_one_zero_negOne_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s114 : ContinuousOn i8Psi4s114 (Ioc 0 1) := by
  rw [show i8Psi4s114 = fun x => i8Psi4s114k0 x + i8Psi4s114k1 x from rfl]
  exact (continuousOn_i8Psi4s114k0.add continuousOn_i8Psi4s114k1)

theorem i8Psi4s114_one : i8Psi4s114 1 = 3 / 4 - 6 * Real.log 2 + 8 * Li 4 (1 / 2) -
    3 / 40 * π ^ 4 - π ^ 2 / 12 + Real.log 2 ^ 4 / 3 + zeta3 / 4 + 7 * Real.log 2 * zeta3 -
    π ^ 2 * Real.log 2 ^ 2 / 3 := by
  unfold i8Psi4s114
  rw [i8Psi4s114k0_one, i8Psi4s114k1_one]
  ring

/-- Chunk 0 of `i8Psi4s115k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s115k0S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 - 37 / 4 * x ^ 3) / x ^ 2 +
    (-x ^ 4 / 4 + 3 / 2 * x ^ 3 + 7 / 4 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (-x ^ 4 / 4 + 5 / 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (5 * x ^ 2 - x ^ 3 / 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (2 * x + 2 * x ^ 3 - x ^ 4 / 2 + 9 / 2 * x ^ 2) / x ^ 2 * hpl [negOne, one] x +
    (-2) * hpl [zero, negOne] x +
    (-2 * x ^ 2 + 3 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [zero, one] x +
    (x ^ 3 / 2 + 2 * x - 3 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (x ^ 3 / 2 - 5 / 2 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (x ^ 4 - x ^ 2 - 2 * x ^ 3 + 2 * x) / x ^ 2 * hpl [negOne, zero, one] x +
    (x ^ 4 - x ^ 2 - 2 * x ^ 3 + 2 * x) / x ^ 2 * hpl [negOne, one, zero] x +
    (x ^ 4 - 2 * x ^ 3 + 2 * x) / x ^ 2 * hpl [zero, negOne, one] x +
    (-2) * hpl [zero, zero, one] x +
    (x ^ 4 - 2 * x ^ 3 + 2 * x) / x ^ 2 * hpl [zero, one, negOne] x +
    (-2) * hpl [zero, one, zero] x +
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, zero, one] x +
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, one, zero] x +
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, negOne, one] x +
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one, negOne] x +
    (2) * hpl [zero, negOne, zero, one] x

theorem continuousOn_i8Psi4s115k0S0 : ContinuousOn i8Psi4s115k0S0 (Ioc 0 1) := by
  unfold i8Psi4s115k0S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 / 2 -
    37 / 4 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -x ^ 4 / 4 + 3 / 2 * x ^ 3 + 7 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 / 4 + 5 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 5 * x ^ 2 - x ^ 3 / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => 2 * x + 2 * x ^ 3 - x ^ 4 / 2 +
        9 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 2 + 3 * x ^ 3 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 + 2 * x - 3 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 - 5 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - x ^ 2 - 2 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - x ^ 2 - 2 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 2 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - 2 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, one]))).add
      ((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, one, zero]))).add
      ((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, one]))).add
      ((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one])))

/-- Chunk 1 of `i8Psi4s115k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s115k0S1 (x : ℝ) : ℝ :=
    (2) * hpl [zero, negOne, one, zero] x +
    (2) * hpl [zero, zero, negOne, one] x +
    (2) * hpl [zero, zero, one, negOne] x +
    (8) * hpl [zero, negOne, negOne, zero, one] x +
    (8) * hpl [zero, negOne, negOne, one, zero] x +
    (8) * hpl [zero, negOne, zero, negOne, one] x +
    (8) * hpl [zero, negOne, zero, one, negOne] x

theorem continuousOn_i8Psi4s115k0S1 : ContinuousOn i8Psi4s115k0S1 (Ioc 0 1) := by
  unfold i8Psi4s115k0S1
  exact (((((((continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one, negOne])))

theorem i8Psi4s115k0_eq_S (x : ℝ) : i8Psi4s115k0 x = i8Psi4s115k0S0 x + i8Psi4s115k0S1 x := by
  unfold i8Psi4s115k0 i8Psi4s115k0S0 i8Psi4s115k0S1 i8Psi4s115k0N0 i8Psi4s115k0N1 i8Psi4s115k0N2
    i8Psi4s115k0N3 i8Psi4s115k0N4 i8Psi4s115k0W
  ring

theorem continuousOn_i8Psi4s115k0 : ContinuousOn i8Psi4s115k0 (Ioc 0 1) := by
  rw [show i8Psi4s115k0 = fun x => i8Psi4s115k0S0 x +
    i8Psi4s115k0S1 x from funext i8Psi4s115k0_eq_S]
  exact (continuousOn_i8Psi4s115k0S0.add continuousOn_i8Psi4s115k0S1)

theorem i8Psi4s115k0_one : i8Psi4s115k0 1 = -35 / 4 - 4 * Li 4 (1 / 2) - 4 * Real.log 2 ^ 2 +
    3 * Real.log 2 - 25 / 4 * zeta5 - 11 / 720 * π ^ 4 - Real.log 2 ^ 4 / 6 +
    4 / 3 * Real.log 2 ^ 5 + 7 / 12 * π ^ 2 + 21 / 8 * zeta3 + 14 * zeta3 * Real.log 2 ^ 2 +
    32 * Real.log 2 * Li 4 (1 / 2) - 4 / 3 * π ^ 2 * Real.log 2 ^ 3 -
    2 / 45 * Real.log 2 * π ^ 4 - π ^ 2 * zeta3 / 2 + π ^ 2 * Real.log 2 ^ 2 / 6 +
    7 / 2 * Real.log 2 * zeta3 := by
  rw [i8Psi4s115k0_eq_S]
  unfold i8Psi4s115k0S0 i8Psi4s115k0S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one,
    hpl_zero_one_at_one, hpl_negOne_zero_one_at_one, hpl_negOne_one_zero_at_one,
    hpl_zero_negOne_one_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_zero_at_one, hpl_negOne_negOne_zero_one_at_one, hpl_negOne_negOne_one_zero_at_one,
    hpl_negOne_zero_negOne_one_at_one, hpl_negOne_zero_one_negOne_at_one,
    hpl_zero_negOne_zero_one_at_one, hpl_zero_negOne_one_zero_at_one,
    hpl_zero_zero_negOne_one_at_one, hpl_zero_zero_one_negOne_at_one,
    hpl_zero_negOne_negOne_zero_one_at_one, hpl_zero_negOne_negOne_one_zero_at_one,
    hpl_zero_negOne_zero_negOne_one_at_one, hpl_zero_negOne_zero_one_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s115k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s115k1S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 - 19 / 4 * x ^ 3) / x ^ 2 +
    (2 * x ^ 2 - x ^ 4 / 2 + 3 / 2 * x ^ 3) / x ^ 2 * hpl [negOne] x +
    (-x ^ 4 / 4 + 3 / 2 * x ^ 3) / x ^ 2 * hpl [zero] x +
    (-x ^ 3 / 4 + 5 / 4 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x ^ 4 / 2 - x ^ 3 - 3 / 2 * x ^ 2) / x ^ 2 * hpl [negOne, zero] x +
    (x + x ^ 3 - x ^ 4 / 2 + 5 / 2 * x ^ 2) / x ^ 2 * hpl [negOne, one] x +
    (x ^ 4 / 2 - x ^ 2 - x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (-1) * hpl [zero, one] x +
    (x + x ^ 3 / 2 - x ^ 2 / 2) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (1 + x ^ 4 - 2 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, one] x +
    (1 + x ^ 4 - 2 * x ^ 2) / x ^ 2 * hpl [negOne, one, negOne] x +
    (-2) * hpl [zero, negOne, zero] x +
    (1) * hpl [zero, negOne, one] x +
    (-2) * hpl [zero, zero, negOne] x +
    (1) * hpl [zero, one, negOne] x +
    (x ^ 2 - x ^ 3 + 2 * x) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (x ^ 2 - x ^ 3 + 2 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, one, negOne, zero] x +
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero, negOne] x +
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, negOne, one] x

theorem continuousOn_i8Psi4s115k1S0 : ContinuousOn i8Psi4s115k1S0 (Ioc 0 1) := by
  unfold i8Psi4s115k1S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 / 2 -
    19 / 4 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 2 * x ^ 2 - x ^ 4 / 2 + 3 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 / 4 + 3 / 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 / 4 + 5 / 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - x ^ 3 - 3 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x + x ^ 3 - x ^ 4 / 2 + 5 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - x ^ 2 - x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => x + x ^ 3 / 2 - x ^ 2 / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => 1 + x ^ 4 - 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, one]))).add
      ((i13_cont_coef (p := fun x => 1 + x ^ 4 - 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 - x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 - x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, one])))

/-- Chunk 1 of `i8Psi4s115k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s115k1S1 (x : ℝ) : ℝ :=
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, one, negOne] x +
    (2) * hpl [zero, one, negOne, zero] x +
    (2) * hpl [zero, one, zero, negOne] x +
    (8) * hpl [zero, negOne, one, negOne, zero] x +
    (8) * hpl [zero, negOne, one, zero, negOne] x +
    (8) * hpl [zero, zero, negOne, negOne, one] x +
    (8) * hpl [zero, zero, negOne, one, negOne] x

theorem continuousOn_i8Psi4s115k1S1 : ContinuousOn i8Psi4s115k1S1 (Ioc 0 1) := by
  unfold i8Psi4s115k1S1
  exact ((((((((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, negOne])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one, negOne])))

theorem i8Psi4s115k1_eq_S (x : ℝ) : i8Psi4s115k1 x = i8Psi4s115k1S0 x + i8Psi4s115k1S1 x := by
  unfold i8Psi4s115k1 i8Psi4s115k1S0 i8Psi4s115k1S1 i8Psi4s115k1N0 i8Psi4s115k1N1 i8Psi4s115k1N2
    i8Psi4s115k1N3 i8Psi4s115k1N4 i8Psi4s115k1W
  ring

theorem continuousOn_i8Psi4s115k1 : ContinuousOn i8Psi4s115k1 (Ioc 0 1) := by
  rw [show i8Psi4s115k1 = fun x => i8Psi4s115k1S0 x +
    i8Psi4s115k1S1 x from funext i8Psi4s115k1_eq_S]
  exact (continuousOn_i8Psi4s115k1S0.add continuousOn_i8Psi4s115k1S1)

theorem i8Psi4s115k1_one : i8Psi4s115k1 1 = -17 / 4 - 32 * Li 5 (1 / 2) - 2 * Real.log 2 ^ 2 +
    3 * Real.log 2 - 26 / 15 * Real.log 2 ^ 5 + 5 / 24 * π ^ 2 + 17 / 8 * zeta3 +
    19 / 360 * π ^ 4 + 119 / 2 * zeta5 - 48 * Real.log 2 * Li 4 (1 / 2) - 7 * Real.log 2 * zeta3 -
    7 * zeta3 * Real.log 2 ^ 2 - 41 / 180 * Real.log 2 * π ^ 4 - 7 / 6 * π ^ 2 * zeta3 +
    14 / 9 * π ^ 2 * Real.log 2 ^ 3 := by
  rw [i8Psi4s115k1_eq_S]
  unfold i8Psi4s115k1S0 i8Psi4s115k1S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_negOne_one_at_one,
    hpl_zero_negOne_at_one, hpl_zero_one_at_one, hpl_negOne_negOne_one_at_one,
    hpl_negOne_one_negOne_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_negOne_one_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_one_negOne_at_one, hpl_negOne_one_negOne_zero_at_one,
    hpl_negOne_one_zero_negOne_at_one, hpl_zero_negOne_negOne_one_at_one,
    hpl_zero_negOne_one_negOne_at_one, hpl_zero_one_negOne_zero_at_one,
    hpl_zero_one_zero_negOne_at_one, hpl_zero_negOne_one_negOne_zero_at_one,
    hpl_zero_negOne_one_zero_negOne_at_one, hpl_zero_zero_negOne_negOne_one_at_one,
    hpl_zero_zero_negOne_one_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s115k2` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s115k2S0 (x : ℝ) : ℝ :=
    (x ^ 4 / 2 + 11 / 4 * x ^ 3) / x ^ 2 +
    (-3 * x ^ 3 - 9 / 4 * x ^ 2 - 3 / 4 * x ^ 4) / x ^ 2 * hpl [negOne] x +
    (-x ^ 3 / 2 - x ^ 4 / 4) / x ^ 2 * hpl [zero] x +
    (x ^ 4 + 3 * x + 3 * x ^ 3 + 5 * x ^ 2) / x ^ 2 * hpl [negOne, negOne] x +
    (x ^ 3 + x ^ 2 / 2 + x ^ 4 / 2) / x ^ 2 * hpl [negOne, zero] x +
    (x ^ 3 + x ^ 4 / 2 - 3 * x ^ 2) / x ^ 2 * hpl [zero, negOne] x +
    (x ^ 2 - x ^ 4 - 2 * x ^ 3 + 2 * x) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (x ^ 2 - x ^ 4 - 2 * x ^ 3 + 2 * x) / x ^ 2 * hpl [negOne, zero, negOne] x +
    (-x ^ 2 - x ^ 4 - 2 * x ^ 3 + 2 * x) / x ^ 2 * hpl [zero, negOne, negOne] x +
    (-2) * hpl [zero, negOne, zero] x +
    (-2) * hpl [zero, zero, negOne] x +
    (1 + x - x ^ 2 - x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, negOne] x) +
    (-2) * hpl [zero, negOne, negOne, zero] x +
    (-2) * hpl [zero, negOne, zero, negOne] x +
    (-2) * hpl [zero, zero, negOne, negOne] x +
    (2 - 2 * x ^ 4) / x ^ 2 * hpl [zero, one, negOne, negOne] x +
    (2 + 2 * x + 2 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, negOne, zero] x) +
    (2 + 2 * x + 2 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero, negOne] x) +
    (2 + 2 * x + 2 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne, negOne] x) +
    (8) * hpl [zero, zero, one, negOne, negOne] x

theorem continuousOn_i8Psi4s115k2S0 : ContinuousOn i8Psi4s115k2S0 (Ioc 0 1) := by
  unfold i8Psi4s115k2S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => x ^ 4 / 2 +
    11 / 4 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -3 * x ^ 3 - 9 / 4 * x ^ 2 - 3 / 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 / 2 - x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 3 * x + 3 * x ^ 3 + 5 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + x ^ 2 / 2 + x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + x ^ 4 / 2 - 3 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 - x ^ 4 - 2 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 - x ^ 4 - 2 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -x ^ 2 - x ^ 4 - 2 * x ^ 3 + 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 1 + x - x ^ 2 - x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 - 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x + 2 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x + 2 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 2 + 2 * x + 2 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne, negOne])))

/-- Chunk 1 of `i8Psi4s115k2` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s115k2S1 (x : ℝ) : ℝ :=
    (8) * hpl [zero, one, negOne, negOne, zero] x +
    (8) * hpl [zero, one, negOne, zero, negOne] x +
    (8) * hpl [zero, one, zero, negOne, negOne] x

theorem continuousOn_i8Psi4s115k2S1 : ContinuousOn i8Psi4s115k2S1 (Ioc 0 1) := by
  unfold i8Psi4s115k2S1
  exact (((continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, negOne, zero])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne, negOne])))

theorem i8Psi4s115k2_eq_S (x : ℝ) : i8Psi4s115k2 x = i8Psi4s115k2S0 x + i8Psi4s115k2S1 x := by
  unfold i8Psi4s115k2 i8Psi4s115k2S0 i8Psi4s115k2S1 i8Psi4s115k2N0 i8Psi4s115k2N1 i8Psi4s115k2N2
    i8Psi4s115k2N3 i8Psi4s115k2N4 i8Psi4s115k2W
  ring

theorem continuousOn_i8Psi4s115k2 : ContinuousOn i8Psi4s115k2 (Ioc 0 1) := by
  rw [show i8Psi4s115k2 = fun x => i8Psi4s115k2S0 x +
    i8Psi4s115k2S1 x from funext i8Psi4s115k2_eq_S]
  exact (continuousOn_i8Psi4s115k2S0.add continuousOn_i8Psi4s115k2S1)

theorem i8Psi4s115k2_one : i8Psi4s115k2 1 = 13 / 4 - 47 * zeta5 - 6 * Real.log 2 +
    4 * Li 4 (1 / 2) + 6 * Real.log 2 ^ 2 + 32 * Li 5 (1 / 2) - 7 / 24 * π ^ 2 -
    π ^ 4 / 24 + Real.log 2 ^ 4 / 6 + 2 / 5 * Real.log 2 ^ 5 + 5 / 4 * zeta3 -
    7 * zeta3 * Real.log 2 ^ 2 + 16 * Real.log 2 * Li 4 (1 / 2) - 2 / 9 * π ^ 2 * Real.log 2 ^ 3 -
    π ^ 2 * Real.log 2 ^ 2 / 6 + 7 / 2 * Real.log 2 * zeta3 + 13 / 12 * π ^ 2 * zeta3 +
    49 / 180 * Real.log 2 * π ^ 4 := by
  rw [i8Psi4s115k2_eq_S]
  unfold i8Psi4s115k2S0 i8Psi4s115k2S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_negOne_at_one, hpl_negOne_zero_at_one,
    hpl_zero_negOne_at_one, hpl_negOne_negOne_zero_at_one, hpl_negOne_zero_negOne_at_one,
    hpl_zero_negOne_negOne_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_negOne_negOne_zero_at_one, hpl_zero_negOne_zero_negOne_at_one,
    hpl_zero_zero_negOne_negOne_at_one, hpl_zero_one_negOne_negOne_at_one,
    hpl_zero_zero_one_negOne_negOne_at_one, hpl_zero_one_negOne_negOne_zero_at_one,
    hpl_zero_one_negOne_zero_negOne_at_one, hpl_zero_one_zero_negOne_negOne_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s115 : ContinuousOn i8Psi4s115 (Ioc 0 1) := by
  rw [show i8Psi4s115 = fun x => i8Psi4s115k0 x + i8Psi4s115k1 x + i8Psi4s115k2 x from rfl]
  exact ((continuousOn_i8Psi4s115k0.add continuousOn_i8Psi4s115k1).add continuousOn_i8Psi4s115k2)

theorem i8Psi4s115_one : i8Psi4s115 1 = -39 / 4 + π ^ 2 / 2 + 6 * zeta3 - π ^ 4 / 240 +
    25 / 4 * zeta5 - 7 / 12 * π ^ 2 * zeta3 := by
  unfold i8Psi4s115
  rw [i8Psi4s115k0_one, i8Psi4s115k1_one, i8Psi4s115k2_one]
  ring

/-- Chunk 0 of `i8Psi4s116k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s116k0S0 (x : ℝ) : ℝ :=
    (-3 / 8 * x ^ 4 + 5 / 8 * x ^ 3) / x ^ 2 +
    (x ^ 3 / 2 - x / 2 - x ^ 2 / 4 + x ^ 4 / 4) / x ^ 2 * hpl [negOne] x +
    (-x ^ 3 / 4 + x ^ 4 / 8 + 3 / 2 * x ^ 2) / x ^ 2 * hpl [zero] x +
    (-x - 5 / 8 * x ^ 2 + 3 / 8 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-1 / 2 + x ^ 4 / 2) / x ^ 2 * hpl [negOne, one] x +
    (1 / 2) * hpl [zero, negOne] x +
    (1 / 2) * hpl [zero, zero] x +
    (-x / 2 - x ^ 2 / 2 - x ^ 3 / 2 + x ^ 4 / 4) / x ^ 2 * hpl [zero, one] x +
    (-1 / 2 - x / 2 - x ^ 2 / 2 - x ^ 3 / 2) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (-x / 2 - x ^ 3 / 4 + x ^ 2 / 4) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-1 / 2 + x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [negOne, zero, one] x +
    (-1 / 2 + x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [negOne, one, zero] x +
    (-1 - x ^ 4) / x ^ 2 * hpl [zero, negOne, one] x +
    (-1 / 2) * hpl [zero, zero, one] x +
    (-1 - x ^ 4) / x ^ 2 * hpl [zero, one, negOne] x +
    (-1 / 2) * hpl [zero, one, zero] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [zero, negOne, zero, one] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [zero, negOne, one, zero] x +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne, one] x +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [zero, zero, one, negOne] x

theorem continuousOn_i8Psi4s116k0S0 : ContinuousOn i8Psi4s116k0S0 (Ioc 0 1) := by
  unfold i8Psi4s116k0S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -3 / 8 * x ^ 4 +
    5 / 8 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 3 / 2 - x / 2 - x ^ 2 / 4 + x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 / 4 + x ^ 4 / 8 + 3 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -x - 5 / 8 * x ^ 2 + 3 / 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -x / 2 - x ^ 2 / 2 - x ^ 3 / 2 + x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 - x / 2 - x ^ 2 / 2 - x ^ 3 / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -x / 2 - x ^ 3 / 4 + x ^ 2 / 4) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 2 - x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -1 - x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne])))

/-- Chunk 1 of `i8Psi4s116k0` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s116k0S1 (x : ℝ) : ℝ :=
    (-4) * hpl [zero, zero, negOne, zero, one] x +
    (-4) * hpl [zero, zero, negOne, one, zero] x +
    (-8) * hpl [zero, zero, zero, negOne, one] x +
    (-8) * hpl [zero, zero, zero, one, negOne] x

theorem continuousOn_i8Psi4s116k0S1 : ContinuousOn i8Psi4s116k0S1 (Ioc 0 1) := by
  unfold i8Psi4s116k0S1
  exact ((((continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, one])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one, negOne])))

theorem i8Psi4s116k0_eq_S (x : ℝ) : i8Psi4s116k0 x = i8Psi4s116k0S0 x + i8Psi4s116k0S1 x := by
  unfold i8Psi4s116k0 i8Psi4s116k0S0 i8Psi4s116k0S1 i8Psi4s116k0N0 i8Psi4s116k0N1 i8Psi4s116k0N2
    i8Psi4s116k0N3 i8Psi4s116k0N4 i8Psi4s116k0W
  ring

theorem continuousOn_i8Psi4s116k0 : ContinuousOn i8Psi4s116k0 (Ioc 0 1) := by
  rw [show i8Psi4s116k0 = fun x => i8Psi4s116k0S0 x +
    i8Psi4s116k0S1 x from funext i8Psi4s116k0_eq_S]
  exact (continuousOn_i8Psi4s116k0S0.add continuousOn_i8Psi4s116k0S1)

theorem i8Psi4s116k0_one : i8Psi4s116k0 1 = 1 / 4 - 3 / 4 * zeta3 - π ^ 2 / 6 + 219 / 8 * zeta5 -
    π ^ 2 * zeta3 - Real.log 2 * π ^ 4 / 4 := by
  rw [i8Psi4s116k0_eq_S]
  unfold i8Psi4s116k0S0 i8Psi4s116k0S1
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_negOne_zero_one_at_one,
    hpl_negOne_one_zero_at_one, hpl_zero_negOne_one_at_one, hpl_zero_zero_one_at_one,
    hpl_zero_one_negOne_at_one, hpl_zero_one_zero_at_one, hpl_zero_negOne_zero_one_at_one,
    hpl_zero_negOne_one_zero_at_one, hpl_zero_zero_negOne_one_at_one,
    hpl_zero_zero_one_negOne_at_one, hpl_zero_zero_negOne_zero_one_at_one,
    hpl_zero_zero_negOne_one_zero_at_one, hpl_zero_zero_zero_negOne_one_at_one,
    hpl_zero_zero_zero_one_negOne_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s116k1` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s116k1S0 (x : ℝ) : ℝ :=
    (-7 / 2 * x ^ 3 - 3 / 8 * x ^ 4) / x ^ 2 +
    (x ^ 4 / 2 - 3 * x + 3 * x ^ 3 - x ^ 2 / 2) / x ^ 2 * hpl [negOne] x +
    (x ^ 3 + 3 * x ^ 2 + x ^ 4 / 4) / x ^ 2 * hpl [zero] x +
    (-5 / 2 * x ^ 2 - 3 / 2 * x - 3 / 2 * x ^ 3 - x ^ 4 / 2) / x ^ 2 * hpl [negOne, zero] x +
    (-x ^ 4 - 3 * x - 3 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (3 / 2) * hpl [zero, zero] x +
    (x ^ 3 + x ^ 2 / 2 + x ^ 4 / 2 - x) / x ^ 2 * hpl [zero, negOne, zero] x +
    (x ^ 2 + x ^ 4 - 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [zero, zero, negOne] x +
    (-1 / 2 + x ^ 2 / 2 + x ^ 3 / 2 - x / 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (-1 + x ^ 2 + x ^ 3 - x) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne] x) +
    (1) * hpl [zero, zero, negOne, zero] x +
    (2) * hpl [zero, zero, zero, negOne] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [zero, one, negOne, zero] x +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [zero, one, zero, negOne] x +
    (-1 - x - x ^ 2 - x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne, zero] x) +
    (-2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, zero, zero, negOne] x) +
    (-4) * hpl [zero, zero, one, negOne, zero] x +
    (-8) * hpl [zero, zero, one, zero, negOne] x +
    (-4) * hpl [zero, one, zero, negOne, zero] x +
    (-8) * hpl [zero, one, zero, zero, negOne] x

theorem continuousOn_i8Psi4s116k1S0 : ContinuousOn i8Psi4s116k1S0 (Ioc 0 1) := by
  unfold i8Psi4s116k1S0
  exact ((((((((((((((((((((i13_cont_coef (p := fun x => -7 / 2 * x ^ 3 -
    3 / 8 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 - 3 * x + 3 * x ^ 3 - x ^ 2 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + 3 * x ^ 2 + x ^ 4 / 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => -5 / 2 * x ^ 2 - 3 / 2 * x - 3 / 2 * x ^ 3 -
        x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -x ^ 4 - 3 * x - 3 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + x ^ 2 / 2 + x ^ 4 / 2 - x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 2 + x ^ 4 - 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 / 2 + x ^ 2 / 2 + x ^ 3 / 2 - x / 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 2 + x ^ 3 - x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne]))).add
      ((i13_cont_coef (p := fun x => -1 - x - x ^ 2 - x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero, negOne])))

theorem i8Psi4s116k1_eq_S (x : ℝ) : i8Psi4s116k1 x = i8Psi4s116k1S0 x := by
  unfold i8Psi4s116k1 i8Psi4s116k1S0 i8Psi4s116k1N0 i8Psi4s116k1N1 i8Psi4s116k1N2 i8Psi4s116k1N3
    i8Psi4s116k1N4 i8Psi4s116k1W
  ring

theorem continuousOn_i8Psi4s116k1 : ContinuousOn i8Psi4s116k1 (Ioc 0 1) := by
  rw [show i8Psi4s116k1 = fun x => i8Psi4s116k1S0 x from funext i8Psi4s116k1_eq_S]
  exact continuousOn_i8Psi4s116k1S0

theorem i8Psi4s116k1_one : i8Psi4s116k1 1 = -31 / 8 - 171 / 8 * zeta5 - 7 / 720 * π ^ 4 -
    π ^ 2 / 12 + Real.log 2 * π ^ 4 / 4 + 7 / 12 * π ^ 2 * zeta3 := by
  rw [i8Psi4s116k1_eq_S]
  unfold i8Psi4s116k1S0
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_negOne_at_one,
    hpl_zero_one_negOne_zero_at_one, hpl_zero_one_zero_negOne_at_one,
    hpl_zero_zero_one_negOne_zero_at_one, hpl_zero_zero_one_zero_negOne_at_one,
    hpl_zero_one_zero_negOne_zero_at_one, hpl_zero_one_zero_zero_negOne_at_one]
  norm_num
  ring

theorem continuousOn_i8Psi4s116 : ContinuousOn i8Psi4s116 (Ioc 0 1) := by
  rw [show i8Psi4s116 = fun x => i8Psi4s116k0 x + i8Psi4s116k1 x from rfl]
  exact (continuousOn_i8Psi4s116k0.add continuousOn_i8Psi4s116k1)

theorem i8Psi4s116_one : i8Psi4s116 1 = -29 / 8 + 6 * zeta5 - 7 / 720 * π ^ 4 - 3 / 4 * zeta3 -
    π ^ 2 / 4 - 5 / 12 * π ^ 2 * zeta3 := by
  unfold i8Psi4s116
  rw [i8Psi4s116k0_one, i8Psi4s116k1_one]
  ring

/-- Chunk 0 of `i8Psi4s117` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s117S0 (x : ℝ) : ℝ :=
    (-x ^ 4 + 2 * x ^ 3) / x ^ 2 +
    (-2 * x ^ 2 + 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-8) * hpl [zero, one] x +
    (-4 * x ^ 2 + 4 * x ^ 3 + 8 * x) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (8) * hpl [zero, one, one] x

theorem continuousOn_i8Psi4s117S0 : ContinuousOn i8Psi4s117S0 (Ioc 0 1) := by
  unfold i8Psi4s117S0
  exact (((((i13_cont_coef (p := fun x => -x ^ 4 + 2 * x ^ 3) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 2 + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -4 * x ^ 2 + 4 * x ^ 3 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one])))

theorem i8Psi4s117_eq_S (x : ℝ) : i8Psi4s117 x = i8Psi4s117S0 x := by
  unfold i8Psi4s117 i8Psi4s117S0 i8Psi4s117N0 i8Psi4s117N1 i8Psi4s117N2 i8Psi4s117N3 i8Psi4s117N4
    i8Psi4s117W
  ring

theorem continuousOn_i8Psi4s117 : ContinuousOn i8Psi4s117 (Ioc 0 1) := by
  rw [show i8Psi4s117 = fun x => i8Psi4s117S0 x from funext i8Psi4s117_eq_S]
  exact continuousOn_i8Psi4s117S0

theorem i8Psi4s117_one : i8Psi4s117 1 = 1 + 8 * zeta3 - 4 / 3 * π ^ 2 := by
  rw [i8Psi4s117_eq_S]
  unfold i8Psi4s117S0
  rw [hpl_zero_one_at_one, hpl_zero_one_one_at_one]
  norm_num
  ring

/-- Chunk 0 of `i8Psi4s118` as a sum over words, with the factor `1 - ξ` of the words beginning
with `1` shown. -/
noncomputable def i8Psi4s118S0 (x : ℝ) : ℝ :=
    (-7 / 2 * x ^ 3 - 3 / 4 * x ^ 4) / x ^ 2 +
    (x ^ 4 / 2 + 3 * x ^ 3 + 5 / 2 * x ^ 2) / x ^ 2 * hpl [negOne] x +
    (x ^ 2 + x ^ 3) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (x ^ 4 - x ^ 2 - 2 * x + 2 * x ^ 3) / x ^ 2 * hpl [negOne, one] x +
    (2) * hpl [zero, negOne] x +
    (4) * hpl [zero, one] x +
    (-x ^ 3 - 3 * x ^ 2 - 2 * x) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (x ^ 3 - x ^ 2 - 2 * x) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (-2 + 2 * x ^ 4) / x ^ 2 * hpl [negOne, one, one] x +
    (2) * hpl [zero, negOne, one] x +
    (2) * hpl [zero, one, negOne] x +
    (-2) * hpl [zero, one, one] x +
    (-2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, one] x) +
    (-2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one, negOne] x) +
    (-8) * hpl [zero, negOne, one, one] x +
    (-8) * hpl [zero, one, negOne, one] x +
    (-8) * hpl [zero, one, one, negOne] x

theorem continuousOn_i8Psi4s118S0 : ContinuousOn i8Psi4s118S0 (Ioc 0 1) := by
  unfold i8Psi4s118S0
  exact (((((((((((((((((i13_cont_coef (p := fun x => -7 / 2 * x ^ 3 -
    3 / 4 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => x ^ 4 / 2 + 3 * x ^ 3 + 5 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => x ^ 2 + x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 - x ^ 2 - 2 * x + 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 3 * x ^ 2 - 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 - x ^ 2 - 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      ((i13_cont_coef (p := fun x => -2 + 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, one]))).add
      ((i13_cont_coef (p := fun x => -2 - 2 * x - 2 * x ^ 2 - 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, negOne])))

theorem i8Psi4s118_eq_S (x : ℝ) : i8Psi4s118 x = i8Psi4s118S0 x := by
  unfold i8Psi4s118 i8Psi4s118S0 i8Psi4s118N0 i8Psi4s118N1 i8Psi4s118N2 i8Psi4s118N3 i8Psi4s118N4
    i8Psi4s118W
  ring

theorem continuousOn_i8Psi4s118 : ContinuousOn i8Psi4s118 (Ioc 0 1) := by
  rw [show i8Psi4s118 = fun x => i8Psi4s118S0 x from funext i8Psi4s118_eq_S]
  exact continuousOn_i8Psi4s118S0

theorem i8Psi4s118_one : i8Psi4s118 1 = -17 / 4 - 8 * Li 4 (1 / 2) + 6 * Real.log 2 -
    3 / 4 * zeta3 - Real.log 2 ^ 4 / 3 + π ^ 4 / 36 + 5 / 6 * π ^ 2 - 7 * Real.log 2 * zeta3 +
    π ^ 2 * Real.log 2 ^ 2 / 3 := by
  rw [i8Psi4s118_eq_S]
  unfold i8Psi4s118S0
  rw [hpl_negOne_at_one, hpl_negOne_one_at_one, hpl_zero_negOne_at_one, hpl_zero_one_at_one,
    hpl_negOne_one_one_at_one, hpl_zero_negOne_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_one_at_one, hpl_zero_negOne_one_one_at_one, hpl_zero_one_negOne_one_at_one,
    hpl_zero_one_one_negOne_at_one]
  norm_num
  ring

end QED.ThreeLoopD
