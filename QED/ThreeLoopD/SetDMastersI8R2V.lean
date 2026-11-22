/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R2P

/-!
# Set (d), master `I₈`: `Ψ₂` at `ξ = 1`

Every word of `Ψ₂` beginning with the letter `1` carries the factor `1 - ξ`
(`QED.ThreeLoopD.i8Psi2S`), so `Ψ₂` is continuous on `(0, 1]`, `F₂` is continuous on `[0, ∞)`,
and `F₂(0) = Ψ₂(1) = 12 + 10π²/3 - 2ζ(3)`, from the values `H(w; 1)` of the words of weight at
most three.

## Main results

* `QED.ThreeLoopD.continuousOn_i8F2`, `QED.ThreeLoopD.i8F2_zero`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- `Ψ₂` as a sum over words, with the factor `1 - ξ` of the words beginning with `1` shown. -/
noncomputable def i8Psi2S (x : ℝ) : ℝ :=
    (-16 * x ^ 4 - 9 * x ^ 3 + 37 * x - π ^ 2 * x / 3 - π ^ 2 * x ^ 3 / 3 -
      π ^ 2 * x ^ 4 / 6) / x ^ 2 +
    (-7 / 2 - 4 * x + 4 * x ^ 3 + 7 / 2 * x ^ 4) / x ^ 2 * hpl [negOne] x +
    (7 / 2 * x ^ 2 + 7 / 2 * x ^ 4 + 45 / 2 * x + 53 / 2 * x ^ 3 +
      π ^ 2 * x ^ 2 / 3) / x ^ 2 * hpl [zero] x +
    (7 * x ^ 3 + 15 * x) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (1 - x ^ 4) / x ^ 2 * hpl [negOne, negOne] x +
    (-3 / 2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 - 5 / 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (-1 + x ^ 4) / x ^ 2 * hpl [negOne, one] x +
    (-2 - 8 * x ^ 2 - 4 * x - 4 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x +
    (x ^ 3 + 9 * x - 9 / 2 * x ^ 2 + 3 / 2 * x ^ 4) / x ^ 2 * hpl [zero, zero] x +
    (x ^ 4 + 5 * x ^ 2 + 6 * x + 6 * x ^ 3) / x ^ 2 * hpl [zero, one] x +
    (-1 - x - x ^ 2 - x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (-x ^ 3 - 7 * x ^ 2 + 6 * x) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (-2 * x ^ 2 + 2 * x ^ 3 + 4 * x) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (4) * hpl [zero, negOne, negOne] x +
    (2) * hpl [zero, negOne, zero] x +
    (-4) * hpl [zero, negOne, one] x +
    (-4) * hpl [zero, zero, negOne] x +
    (-11) * hpl [zero, zero, zero] x +
    (-2) * hpl [zero, zero, one] x +
    (-4) * hpl [zero, one, negOne] x +
    (-2) * hpl [zero, one, zero] x +
    (4) * hpl [zero, one, one] x

theorem continuousOn_i8Psi2S : ContinuousOn i8Psi2S (Ioc 0 1) := by
  unfold i8Psi2S
  exact ((((((((((((((((((((((i13_cont_coef (p := fun x => -16 * x ^ 4 - 9 * x ^ 3 + 37 * x -
    π ^ 2 * x / 3 - π ^ 2 * x ^ 3 / 3 - π ^ 2 * x ^ 4 / 6) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => -7 / 2 - 4 * x + 4 * x ^ 3 + 7 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 7 / 2 * x ^ 2 + 7 / 2 * x ^ 4 + 45 / 2 * x + 53 / 2 * x ^ 3 +
        π ^ 2 * x ^ 2 / 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 7 * x ^ 3 + 15 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => 1 - x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => -3 / 2 - 12 * x ^ 2 - 8 * x - 8 * x ^ 3 -
        5 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -1 + x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -2 - 8 * x ^ 2 - 4 * x - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => x ^ 3 + 9 * x - 9 / 2 * x ^ 2 +
        3 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => x ^ 4 + 5 * x ^ 2 + 6 * x + 6 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => -1 - x - x ^ 2 - x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => -x ^ 3 - 7 * x ^ 2 + 6 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => -2 * x ^ 2 + 2 * x ^ 3 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one])))


theorem i8Psi2_eq_S (x : ℝ) : i8Psi2 x = i8Psi2S x := by
  unfold i8Psi2 i8Psi2S i8Psi2N0 i8Psi2N1 i8Psi2N2 i8Psi2N3 i8Psi2N4 i8Psi2W
  ring

theorem continuousOn_i8Psi2 : ContinuousOn i8Psi2 (Ioc 0 1) := by
  rw [show i8Psi2 = i8Psi2S from funext i8Psi2_eq_S]
  exact continuousOn_i8Psi2S

theorem continuousOn_i8F2 : ContinuousOn i8F2 (Ici 0) :=
  continuousOn_i8Psi2.comp continuous_i13Xi.continuousOn fun _ ht =>
    ⟨i13Xi_pos ht, i13Xi_le_one ht⟩

/-- **`Ψ₂(1) = 12 + 10π²/3 - 2ζ(3)`.** -/
theorem i8Psi2_one : i8Psi2 1 = 12 + 10 * π ^ 2 / 3 - 2 * zeta3 := by
  rw [i8Psi2_eq_S]
  unfold i8Psi2S
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_negOne_at_one, hpl_negOne_zero_at_one,
    hpl_negOne_one_at_one, hpl_zero_negOne_at_one, hpl_zero_zero_at_one, hpl_zero_one_at_one,
    hpl_zero_negOne_negOne_at_one, hpl_zero_negOne_zero_at_one, hpl_zero_negOne_one_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_zero_at_one, hpl_zero_zero_one_at_one,
    hpl_zero_one_negOne_at_one, hpl_zero_one_zero_at_one, hpl_zero_one_one_at_one]
  norm_num
  ring

theorem i8F2_zero : i8F2 0 = 12 + 10 * π ^ 2 / 3 - 2 * zeta3 := by
  unfold i8F2
  rw [i13Xi_zero, i8Psi2_one]

end QED.ThreeLoopD
