/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13R4F
public import QED.Polylog.HPLValues5
public import QED.Polylog.HPLValuesAlt5A
public import QED.Polylog.HPLValuesAlt5B
public import QED.Polylog.HPLValuesAlt5C
public import QED.Polylog.HPLValuesAlt5D

/-!
# Set (d), master `I₁₃`: `Ψ₄` at `ξ = 1`

Every word of `Ψ₄` beginning with the letter `1` carries the factor `1 - ξ` (the parts
`QED.ThreeLoopD.i13Psi4Sa`, …), and `(1 - ξ) H(1 · w; ξ) → 0` as `ξ → 1⁻`
(`QED.ThreeLoopD.i13_contOn_one_sub_mul_hpl`). So `Ψ₄` is continuous on `(0, 1]`, `F₄` is
continuous on `[0, ∞)`, and, from the values `H(w; 1)` of the words of weight at most five,

  `F₄(0) = Ψ₄(1) = 4445/16 - 256 Li₄(1/2) - 223 ζ(3) + 12 ζ(5) - 32/3 log⁴ 2 + 137π⁴/45
    - 2π² ζ(3)/3 + 32/3 π² log² 2`

(`QED.ThreeLoopD.i13F4_zero`).

## Main results

* `QED.ThreeLoopD.continuousOn_i13F4`, `QED.ThreeLoopD.i13F4_zero`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- Part a of `Ψ₄` as a sum over words. -/
noncomputable def i13Psi4Sa (x : ℝ) : ℝ :=
    (2777 / 32 - 11 * zeta3 - 27 / 8 * π ^ 2 - π ^ 4 / 90 + 417 / 8 * x + 417 / 8 * x ^ 3 +
      2777 / 32 * x ^ 4 - 8 * x * zeta3 + 8 * zeta3 * x ^ 3 + 11 * zeta3 * x ^ 4 -
      17 / 3 * π ^ 2 * x + x * π ^ 4 / 18 + π ^ 4 * x ^ 3 / 18 + 7 / 180 * π ^ 4 * x ^ 4 +
      17 / 3 * π ^ 2 * x ^ 3 + 27 / 8 * π ^ 2 * x ^ 4) / x ^ 2 +
    (1497 / 16 - 6 * zeta3 - 865 / 4 * x ^ 3 - 499 / 16 * x ^ 4 - 11 / 4 * π ^ 2 +
      33 / 8 * x ^ 2 + 599 / 4 * x - 24 * zeta3 * x ^ 2 - 8 * x * zeta3 - 8 * zeta3 * x ^ 3 -
      3 * π ^ 2 * x ^ 3 + 2 * zeta3 * x ^ 4 - 17 / 3 * π ^ 2 * x - 13 / 3 * π ^ 2 * x ^ 2 -
      π ^ 4 * x ^ 2 / 10 + 11 / 12 * π ^ 2 * x ^ 4) / x ^ 2 * hpl [zero] x +
    (4 * zeta3 + 11 / 6 * π ^ 2 - 4 * zeta3 * x ^ 4 - 11 / 6 * π ^ 2 * x ^ 4 -
      4 / 3 * π ^ 2 * x ^ 3 + 4 / 3 * π ^ 2 * x) / x ^ 2 * hpl [negOne] x +
    (499 / 8 - 4 * zeta3 - 499 / 8 * x ^ 3 - 33 / 8 * x - 11 / 6 * π ^ 2 + 33 / 8 * x ^ 2 -
      4 * x * zeta3 - 4 * zeta3 * x ^ 2 - 4 * zeta3 * x ^ 3 - 19 / 6 * π ^ 2 * x -
      19 / 6 * π ^ 2 * x ^ 2 - 11 / 6 * π ^ 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (729 / 8 - 243 / 8 * x ^ 4 - 21 / 2 * x ^ 3 - 3 / 2 * π ^ 2 + 295 / 4 * x ^ 2 + 387 / 2 * x -
      16 * zeta3 * x ^ 2 - 13 / 3 * π ^ 2 * x ^ 2 - 10 / 3 * π ^ 2 * x - 10 / 3 * π ^ 2 * x ^ 3 -
      π ^ 2 * x ^ 4 / 6) / x ^ 2 * hpl [zero, zero] x +
    (π ^ 2 + 4 * π ^ 2 * x ^ 2 + 16 * zeta3 * x ^ 2 - π ^ 2 * x ^ 4 / 3 + 4 / 3 * π ^ 2 * x +
      4 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [zero, negOne] x

theorem continuousOn_i13Psi4Sa : ContinuousOn i13Psi4Sa (Ioc 0 1) := by
  unfold i13Psi4Sa
  exact ((((((i13_cont_coef (p := fun x => 2777 / 32 - 11 * zeta3 - 27 / 8 * π ^ 2 -
    π ^ 4 / 90 + 417 / 8 * x + 417 / 8 * x ^ 3 + 2777 / 32 * x ^ 4 - 8 * x * zeta3 +
    8 * zeta3 * x ^ 3 + 11 * zeta3 * x ^ 4 - 17 / 3 * π ^ 2 * x + x * π ^ 4 / 18 +
    π ^ 4 * x ^ 3 / 18 + 7 / 180 * π ^ 4 * x ^ 4 + 17 / 3 * π ^ 2 * x ^ 3 +
    27 / 8 * π ^ 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => 1497 / 16 - 6 * zeta3 - 865 / 4 * x ^ 3 - 499 / 16 * x ^ 4 -
        11 / 4 * π ^ 2 + 33 / 8 * x ^ 2 + 599 / 4 * x - 24 * zeta3 * x ^ 2 - 8 * x * zeta3 -
        8 * zeta3 * x ^ 3 - 3 * π ^ 2 * x ^ 3 + 2 * zeta3 * x ^ 4 - 17 / 3 * π ^ 2 * x -
        13 / 3 * π ^ 2 * x ^ 2 - π ^ 4 * x ^ 2 / 10 + 11 / 12 * π ^ 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 4 * zeta3 + 11 / 6 * π ^ 2 - 4 * zeta3 * x ^ 4 -
        11 / 6 * π ^ 2 * x ^ 4 - 4 / 3 * π ^ 2 * x ^ 3 + 4 / 3 * π ^ 2 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 499 / 8 - 4 * zeta3 - 499 / 8 * x ^ 3 - 33 / 8 * x -
        11 / 6 * π ^ 2 + 33 / 8 * x ^ 2 - 4 * x * zeta3 - 4 * zeta3 * x ^ 2 - 4 * zeta3 * x ^ 3 -
        19 / 6 * π ^ 2 * x - 19 / 6 * π ^ 2 * x ^ 2 - 11 / 6 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => 729 / 8 - 243 / 8 * x ^ 4 - 21 / 2 * x ^ 3 -
        3 / 2 * π ^ 2 + 295 / 4 * x ^ 2 + 387 / 2 * x - 16 * zeta3 * x ^ 2 -
        13 / 3 * π ^ 2 * x ^ 2 - 10 / 3 * π ^ 2 * x - 10 / 3 * π ^ 2 * x ^ 3 -
        π ^ 2 * x ^ 4 / 6) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => π ^ 2 + 4 * π ^ 2 * x ^ 2 + 16 * zeta3 * x ^ 2 -
        π ^ 2 * x ^ 4 / 3 + 4 / 3 * π ^ 2 * x + 4 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne])))

/-- Part b of `Ψ₄` as a sum over words. -/
noncomputable def i13Psi4Sb (x : ℝ) : ℝ :=
    (243 / 4 - π ^ 2 - 115 * x ^ 3 + 21 * x - 81 / 4 * x ^ 4 + 107 / 2 * x ^ 2 -
      16 * zeta3 * x ^ 2 - 4 * π ^ 2 * x ^ 2 - 4 / 3 * π ^ 2 * x - 4 / 3 * π ^ 2 * x ^ 3 +
      π ^ 2 * x ^ 4 / 3) / x ^ 2 * hpl [zero, one] x +
    (-81 / 2 - 68 * x + 68 * x ^ 3 + 4 / 3 * π ^ 2 + 81 / 2 * x ^ 4 + 4 * π ^ 2 * x ^ 2 +
      8 / 3 * π ^ 2 * x + 8 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * hpl [negOne, zero] x +
    (-2 / 3 * π ^ 2 + 2 / 3 * π ^ 2 * x ^ 4) / x ^ 2 * hpl [negOne, negOne] x +
    (2 / 3 * π ^ 2 - 2 / 3 * π ^ 2 * x ^ 4) / x ^ 2 * hpl [negOne, one] x +
    (243 / 4 - π ^ 2 + 81 / 4 * x ^ 3 + 327 / 4 * x + 541 / 4 * x ^ 2 + π ^ 2 * x ^ 2 -
      7 / 3 * π ^ 2 * x - π ^ 2 * x ^ 3 / 3) / x ^ 2 * ((1 - x) * hpl [one, zero] x) +
    (2 / 3 * π ^ 2 + 2 / 3 * π ^ 2 * x + 2 / 3 * π ^ 2 * x ^ 2 +
      2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne] x) +
    (81 / 2 - 107 / 2 * x - 81 / 2 * x ^ 3 - 2 / 3 * π ^ 2 + 107 / 2 * x ^ 2 - 2 / 3 * π ^ 2 * x -
      2 / 3 * π ^ 2 * x ^ 2 - 2 / 3 * π ^ 2 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (297 / 4 + 119 * x ^ 3 + 175 * x - 11 / 4 * x ^ 4 + 219 / 2 * x ^ 2 -
      8 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, zero, zero] x +
    (8 / 3 * π ^ 2) * hpl [zero, zero, negOne] x +
    (99 / 2 + 10 * x ^ 3 + 58 * x + 77 * x ^ 2 - 33 / 2 * x ^ 4 -
      8 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, zero, one] x +
    (-33 - 68 * x - 52 * x ^ 2 - 36 * x ^ 3 + 11 * x ^ 4 +
      8 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, negOne, zero] x +
    (-8 / 3 * π ^ 2) * hpl [zero, negOne, negOne] x +
    (8 / 3 * π ^ 2) * hpl [zero, negOne, one] x

theorem continuousOn_i13Psi4Sb : ContinuousOn i13Psi4Sb (Ioc 0 1) := by
  unfold i13Psi4Sb
  exact ((((((((((((((i13_cont_coef (p := fun x => 243 / 4 - π ^ 2 - 115 * x ^ 3 + 21 * x -
    81 / 4 * x ^ 4 + 107 / 2 * x ^ 2 - 16 * zeta3 * x ^ 2 - 4 * π ^ 2 * x ^ 2 -
    4 / 3 * π ^ 2 * x - 4 / 3 * π ^ 2 * x ^ 3 + π ^ 2 * x ^ 4 / 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one])).add
      ((i13_cont_coef (p := fun x => -81 / 2 - 68 * x + 68 * x ^ 3 + 4 / 3 * π ^ 2 +
        81 / 2 * x ^ 4 + 4 * π ^ 2 * x ^ 2 + 8 / 3 * π ^ 2 * x +
        8 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => -2 / 3 * π ^ 2 + 2 / 3 * π ^ 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => 2 / 3 * π ^ 2 - 2 / 3 * π ^ 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => 243 / 4 - π ^ 2 + 81 / 4 * x ^ 3 + 327 / 4 * x +
        541 / 4 * x ^ 2 + π ^ 2 * x ^ 2 - 7 / 3 * π ^ 2 * x - π ^ 2 * x ^ 3 / 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => 2 / 3 * π ^ 2 + 2 / 3 * π ^ 2 * x + 2 / 3 * π ^ 2 * x ^ 2 +
        2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i13_cont_coef (p := fun x => 81 / 2 - 107 / 2 * x - 81 / 2 * x ^ 3 - 2 / 3 * π ^ 2 +
        107 / 2 * x ^ 2 - 2 / 3 * π ^ 2 * x - 2 / 3 * π ^ 2 * x ^ 2 -
        2 / 3 * π ^ 2 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      ((i13_cont_coef (p := fun x => 297 / 4 + 119 * x ^ 3 + 175 * x - 11 / 4 * x ^ 4 +
        219 / 2 * x ^ 2 - 8 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i13_cont_coef (p := fun x => 99 / 2 + 10 * x ^ 3 + 58 * x + 77 * x ^ 2 - 33 / 2 * x ^ 4 -
        8 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -33 - 68 * x - 52 * x ^ 2 - 36 * x ^ 3 + 11 * x ^ 4 +
        8 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one])))

/-- Part c of `Ψ₄` as a sum over words. -/
noncomputable def i13Psi4Sc (x : ℝ) : ℝ :=
    (99 / 2 + 10 * x ^ 3 + 58 * x + 77 * x ^ 2 - 33 / 2 * x ^ 4 -
      8 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, one, zero] x +
    (8 / 3 * π ^ 2) * hpl [zero, one, negOne] x +
    (33 - 52 * x ^ 3 - 20 * x - 11 * x ^ 4 + 50 * x ^ 2 -
      8 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, one, one] x +
    (-55 - 164 * x ^ 2 - 128 * x - 80 * x ^ 3 + 11 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-22 - 16 * x + 16 * x ^ 3 + 22 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one] x +
    (22 - 22 * x ^ 4 - 16 * x ^ 3 + 16 * x) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (-22 - 16 * x + 16 * x ^ 3 + 22 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero] x +
    (99 / 2 + 13 / 2 * x ^ 2 + 33 / 2 * x ^ 3 + 215 / 2 * x) / x ^ 2 * ((1 -
      x) * hpl [one, zero, zero] x) +
    (33 + 11 * x ^ 3 + 13 * x + 63 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, one] x) +
    (-22 - 38 * x - 38 * x ^ 2 - 22 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (33 + 11 * x ^ 3 + 13 * x + 63 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one, zero] x) +
    (22 - 50 * x - 22 * x ^ 3 + 50 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one, one] x) +
    (81 / 2 + 98 * x + 98 * x ^ 3 + 99 * x ^ 2 +
      21 / 2 * x ^ 4) / x ^ 2 * hpl [zero, zero, zero, zero] x +
    (27 - x ^ 4 + 44 * x + 44 * x ^ 3 + 82 * x ^ 2) / x ^ 2 * hpl [zero, zero, zero, one] x +
    (-18 - 52 * x ^ 2 - 40 * x - 40 * x ^ 3 -
      2 * x ^ 4) / x ^ 2 * hpl [zero, zero, negOne, zero] x +
    (27 - x ^ 4 + 44 * x + 44 * x ^ 3 + 82 * x ^ 2) / x ^ 2 * hpl [zero, zero, one, zero] x +
    (18 - 6 * x ^ 4 + 8 * x + 8 * x ^ 3 + 60 * x ^ 2) / x ^ 2 * hpl [zero, zero, one, one] x

theorem continuousOn_i13Psi4Sc : ContinuousOn i13Psi4Sc (Ioc 0 1) := by
  unfold i13Psi4Sc
  exact ((((((((((((((((((i13_cont_coef (p := fun x => 99 / 2 + 10 * x ^ 3 + 58 * x +
    77 * x ^ 2 - 33 / 2 * x ^ 4 - 8 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      ((i13_cont_coef (p := fun x => 33 - 52 * x ^ 3 - 20 * x - 11 * x ^ 4 + 50 * x ^ 2 -
        8 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -55 - 164 * x ^ 2 - 128 * x - 80 * x ^ 3 +
        11 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -22 - 16 * x + 16 * x ^ 3 + 22 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => 22 - 22 * x ^ 4 - 16 * x ^ 3 + 16 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -22 - 16 * x + 16 * x ^ 3 + 22 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => 99 / 2 + 13 / 2 * x ^ 2 + 33 / 2 * x ^ 3 +
        215 / 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 33 + 11 * x ^ 3 + 13 * x + 63 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -22 - 38 * x - 38 * x ^ 2 - 22 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 33 + 11 * x ^ 3 + 13 * x + 63 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero]))).add
      ((i13_cont_coef (p := fun x => 22 - 50 * x - 22 * x ^ 3 + 50 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, one]))).add
      ((i13_cont_coef (p := fun x => 81 / 2 + 98 * x + 98 * x ^ 3 + 99 * x ^ 2 +
        21 / 2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 27 - x ^ 4 + 44 * x + 44 * x ^ 3 +
        82 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      ((i13_cont_coef (p := fun x => -18 - 52 * x ^ 2 - 40 * x - 40 * x ^ 3 -
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 27 - x ^ 4 + 44 * x + 44 * x ^ 3 +
        82 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      ((i13_cont_coef (p := fun x => 18 - 6 * x ^ 4 + 8 * x + 8 * x ^ 3 +
        60 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one])))

/-- Part d of `Ψ₄` as a sum over words. -/
noncomputable def i13Psi4Sd (x : ℝ) : ℝ :=
    (-30 - 80 * x ^ 2 - 72 * x - 72 * x ^ 3 -
      6 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero, zero] x +
    (-12 - 48 * x ^ 2 - 16 * x - 16 * x ^ 3 + 4 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero, one] x +
    (12 - 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
      48 * x ^ 2) / x ^ 2 * hpl [zero, negOne, negOne, zero] x +
    (-12 - 48 * x ^ 2 - 16 * x - 16 * x ^ 3 + 4 * x ^ 4) / x ^ 2 * hpl [zero, negOne, one, zero] x +
    (27 - x ^ 4 + 44 * x + 44 * x ^ 3 + 82 * x ^ 2) / x ^ 2 * hpl [zero, one, zero, zero] x +
    (18 - 6 * x ^ 4 + 8 * x + 8 * x ^ 3 + 60 * x ^ 2) / x ^ 2 * hpl [zero, one, zero, one] x +
    (-12 - 48 * x ^ 2 - 16 * x - 16 * x ^ 3 + 4 * x ^ 4) / x ^ 2 * hpl [zero, one, negOne, zero] x +
    (18 - 6 * x ^ 4 + 8 * x + 8 * x ^ 3 + 60 * x ^ 2) / x ^ 2 * hpl [zero, one, one, zero] x +
    (12 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4 + 24 * x ^ 2) / x ^ 2 * hpl [zero, one, one, one] x +
    (-38 - 144 * x ^ 2 - 96 * x - 96 * x ^ 3 -
      10 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero, zero] x +
    (-20 - 48 * x ^ 2 - 32 * x - 32 * x ^ 3 + 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero, one] x +
    (16 + 32 * x + 32 * x ^ 3 + 48 * x ^ 2) / x ^ 2 * hpl [negOne, zero, negOne, zero] x +
    (-20 - 48 * x ^ 2 - 32 * x - 32 * x ^ 3 + 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one, zero] x +
    (-8 + 8 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one, one] x +
    (28 + 4 * x ^ 4 + 64 * x + 64 * x ^ 3 +
      96 * x ^ 2) / x ^ 2 * hpl [negOne, negOne, zero, zero] x +
    (8 - 8 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, zero, one] x +
    (-8 + 8 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, negOne, zero] x

theorem continuousOn_i13Psi4Sd : ContinuousOn i13Psi4Sd (Ioc 0 1) := by
  unfold i13Psi4Sd
  exact ((((((((((((((((((i13_cont_coef (p := fun x => -30 - 80 * x ^ 2 - 72 * x - 72 * x ^ 3 -
    6 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero])).add
      ((i13_cont_coef (p := fun x => -12 - 48 * x ^ 2 - 16 * x - 16 * x ^ 3 +
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one]))).add
      ((i13_cont_coef (p := fun x => 12 - 4 * x ^ 4 + 16 * x + 16 * x ^ 3 +
        48 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -12 - 48 * x ^ 2 - 16 * x - 16 * x ^ 3 +
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero]))).add
      ((i13_cont_coef (p := fun x => 27 - x ^ 4 + 44 * x + 44 * x ^ 3 +
        82 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 18 - 6 * x ^ 4 + 8 * x + 8 * x ^ 3 +
        60 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -12 - 48 * x ^ 2 - 16 * x - 16 * x ^ 3 +
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 18 - 6 * x ^ 4 + 8 * x + 8 * x ^ 3 +
        60 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero]))).add
      ((i13_cont_coef (p := fun x => 12 - 16 * x - 16 * x ^ 3 - 4 * x ^ 4 +
        24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, one]))).add
      ((i13_cont_coef (p := fun x => -38 - 144 * x ^ 2 - 96 * x - 96 * x ^ 3 -
        10 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -20 - 48 * x ^ 2 - 32 * x - 32 * x ^ 3 +
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero, one]))).add
      ((i13_cont_coef (p := fun x => 16 + 32 * x + 32 * x ^ 3 + 48 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -20 - 48 * x ^ 2 - 32 * x - 32 * x ^ 3 +
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one, zero]))).add
      ((i13_cont_coef (p := fun x => -8 + 8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one, one]))).add
      ((i13_cont_coef (p := fun x => 28 + 4 * x ^ 4 + 64 * x + 64 * x ^ 3 +
        96 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 8 - 8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero, one]))).add
      ((i13_cont_coef (p := fun x => -8 + 8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, negOne, zero])))

/-- Part e of `Ψ₄` as a sum over words. -/
noncomputable def i13Psi4Se (x : ℝ) : ℝ :=
    (8 - 8 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, one, zero] x +
    (-20 - 48 * x ^ 2 - 32 * x - 32 * x ^ 3 + 4 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero, zero] x +
    (-8 + 8 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero, one] x +
    (8 - 8 * x ^ 4) / x ^ 2 * hpl [negOne, one, negOne, zero] x +
    (-8 + 8 * x ^ 4) / x ^ 2 * hpl [negOne, one, one, zero] x +
    (27 + x ^ 3 - 43 * x ^ 2 + 71 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero, zero] x) +
    (18 - 2 * x ^ 2 + 6 * x ^ 3 + 26 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero, one] x) +
    (-12 - 28 * x - 4 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, negOne, zero] x) +
    (18 - 2 * x ^ 2 + 6 * x ^ 3 + 26 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, one, zero] x) +
    (12 - 4 * x + 4 * x ^ 3 + 20 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, one, one] x) +
    (-20 - 52 * x - 4 * x ^ 3 + 28 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero, zero] x) +
    (-8 - 8 * x - 8 * x ^ 2 - 8 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero, one] x) +
    (8 + 8 * x + 8 * x ^ 2 + 8 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, negOne, zero] x) +
    (-8 - 8 * x - 8 * x ^ 2 - 8 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, one, zero] x) +
    (18 - 2 * x ^ 2 + 6 * x ^ 3 + 26 * x) / x ^ 2 * ((1 - x) * hpl [one, one, zero, zero] x) +
    (12 - 4 * x + 4 * x ^ 3 + 20 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one, zero, one] x) +
    (-8 - 8 * x - 8 * x ^ 2 - 8 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, one, negOne, zero] x) +
    (12 - 4 * x + 4 * x ^ 3 + 20 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one, one, zero] x)

theorem continuousOn_i13Psi4Se : ContinuousOn i13Psi4Se (Ioc 0 1) := by
  unfold i13Psi4Se
  exact (((((((((((((((((((i13_cont_coef (p := fun x => 8 - 8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, one, zero])).add
      ((i13_cont_coef (p := fun x => -20 - 48 * x ^ 2 - 32 * x - 32 * x ^ 3 +
        4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -8 + 8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => 8 - 8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -8 + 8 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, one, zero]))).add
      ((i13_cont_coef (p := fun x => 27 + x ^ 3 - 43 * x ^ 2 + 71 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 18 - 2 * x ^ 2 + 6 * x ^ 3 + 26 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero, one]))).add
      ((i13_cont_coef (p := fun x => -12 - 28 * x - 4 * x ^ 3 + 12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 18 - 2 * x ^ 2 + 6 * x ^ 3 + 26 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one, zero]))).add
      ((i13_cont_coef (p := fun x => 12 - 4 * x + 4 * x ^ 3 + 20 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one, one]))).add
      ((i13_cont_coef (p := fun x => -20 - 52 * x - 4 * x ^ 3 + 28 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero, zero]))).add
      ((i13_cont_coef (p := fun x => -8 - 8 * x - 8 * x ^ 2 - 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero, one]))).add
      ((i13_cont_coef (p := fun x => 8 + 8 * x + 8 * x ^ 2 + 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -8 - 8 * x - 8 * x ^ 2 - 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, one, zero]))).add
      ((i13_cont_coef (p := fun x => 18 - 2 * x ^ 2 + 6 * x ^ 3 + 26 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 12 - 4 * x + 4 * x ^ 3 + 20 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero, one]))).add
      ((i13_cont_coef (p := fun x => -8 - 8 * x - 8 * x ^ 2 - 8 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 12 - 4 * x + 4 * x ^ 3 + 20 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, one, zero])))

/-- Part f of `Ψ₄` as a sum over words. -/
noncomputable def i13Psi4Sf (x : ℝ) : ℝ :=
    (8 - 24 * x - 8 * x ^ 3 + 24 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one, one, one] x) +
    (60) * hpl [zero, zero, zero, zero, zero] x +
    (56) * hpl [zero, zero, zero, zero, one] x +
    (-32) * hpl [zero, zero, zero, negOne, zero] x +
    (56) * hpl [zero, zero, zero, one, zero] x +
    (48) * hpl [zero, zero, zero, one, one] x +
    (-48) * hpl [zero, zero, negOne, zero, zero] x +
    (-32) * hpl [zero, zero, negOne, zero, one] x +
    (32) * hpl [zero, zero, negOne, negOne, zero] x +
    (-32) * hpl [zero, zero, negOne, one, zero] x +
    (56) * hpl [zero, zero, one, zero, zero] x +
    (48) * hpl [zero, zero, one, zero, one] x +
    (-32) * hpl [zero, zero, one, negOne, zero] x +
    (48) * hpl [zero, zero, one, one, zero] x +
    (32) * hpl [zero, zero, one, one, one] x +
    (-56) * hpl [zero, negOne, zero, zero, zero] x +
    (-48) * hpl [zero, negOne, zero, zero, one] x +
    (32) * hpl [zero, negOne, zero, negOne, zero] x +
    (-48) * hpl [zero, negOne, zero, one, zero] x +
    (-32) * hpl [zero, negOne, zero, one, one] x +
    (48) * hpl [zero, negOne, negOne, zero, zero] x +
    (32) * hpl [zero, negOne, negOne, zero, one] x +
    (-32) * hpl [zero, negOne, negOne, negOne, zero] x +
    (32) * hpl [zero, negOne, negOne, one, zero] x

theorem continuousOn_i13Psi4Sf : ContinuousOn i13Psi4Sf (Ioc 0 1) := by
  unfold i13Psi4Sf
  exact (((((((((((((((((((((((((i13_cont_coef (p := fun x => 8 - 24 * x - 8 * x ^ 3 +
    24 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, one, one])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, one, zero])))

/-- Part g of `Ψ₄` as a sum over words. -/
noncomputable def i13Psi4Sg (x : ℝ) : ℝ :=
    (-48) * hpl [zero, negOne, one, zero, zero] x +
    (-32) * hpl [zero, negOne, one, zero, one] x +
    (32) * hpl [zero, negOne, one, negOne, zero] x +
    (-32) * hpl [zero, negOne, one, one, zero] x +
    (56) * hpl [zero, one, zero, zero, zero] x +
    (48) * hpl [zero, one, zero, zero, one] x +
    (-32) * hpl [zero, one, zero, negOne, zero] x +
    (48) * hpl [zero, one, zero, one, zero] x +
    (32) * hpl [zero, one, zero, one, one] x +
    (-48) * hpl [zero, one, negOne, zero, zero] x +
    (-32) * hpl [zero, one, negOne, zero, one] x +
    (32) * hpl [zero, one, negOne, negOne, zero] x +
    (-32) * hpl [zero, one, negOne, one, zero] x +
    (48) * hpl [zero, one, one, zero, zero] x +
    (32) * hpl [zero, one, one, zero, one] x +
    (-32) * hpl [zero, one, one, negOne, zero] x +
    (32) * hpl [zero, one, one, one, zero] x

theorem continuousOn_i13Psi4Sg : ContinuousOn i13Psi4Sg (Ioc 0 1) := by
  unfold i13Psi4Sg
  exact (((((((((((((((((continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero, zero])).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, one, zero])))

theorem i13Psi4_eq_S (x : ℝ) : i13Psi4 x = i13Psi4Sa x + i13Psi4Sb x + i13Psi4Sc x +
    i13Psi4Sd x + i13Psi4Se x + i13Psi4Sf x + i13Psi4Sg x := by
  unfold i13Psi4 i13Psi4N0 i13Psi4N1 i13Psi4N2 i13Psi4N3 i13Psi4N4 i13Psi4W i13Psi4N0a i13Psi4N0b
    i13Psi4N0c i13Psi4N1a i13Psi4N1b i13Psi4N1c i13Psi4N2a i13Psi4N2b i13Psi4N3a i13Psi4N3b
    i13Psi4N3c i13Psi4N4a i13Psi4N4b i13Psi4N4c i13Psi4Wa i13Psi4Wb i13Psi4Sa i13Psi4Sb i13Psi4Sc
    i13Psi4Sd i13Psi4Se i13Psi4Sf i13Psi4Sg
  ring

theorem continuousOn_i13Psi4 : ContinuousOn i13Psi4 (Ioc 0 1) := by
  rw [show i13Psi4 = fun x => i13Psi4Sa x + i13Psi4Sb x + i13Psi4Sc x + i13Psi4Sd x +
      i13Psi4Se x + i13Psi4Sf x + i13Psi4Sg x from funext i13Psi4_eq_S]
  exact ((((((continuousOn_i13Psi4Sa.add continuousOn_i13Psi4Sb).add continuousOn_i13Psi4Sc).add
      continuousOn_i13Psi4Sd).add continuousOn_i13Psi4Se).add continuousOn_i13Psi4Sf).add
      continuousOn_i13Psi4Sg)

theorem continuousOn_i13F4 : ContinuousOn i13F4 (Ici 0) :=
  continuousOn_i13Psi4.comp continuous_i13Xi.continuousOn fun _ ht =>
    ⟨i13Xi_pos ht, i13Xi_le_one ht⟩

/-- **The value `Ψ₄(1)`.** -/
theorem i13Psi4_one : i13Psi4 1 =
      4445 / 16 - 256 * Li 4 (1 / 2) - 223 * zeta3 + 12 * zeta5 - 32 / 3 * Real.log 2 ^ 4 +
      137 / 45 * π ^ 4 - 2 / 3 * π ^ 2 * zeta3 + 32 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  have h5 : hpl [zero, zero, zero, zero, zero] 1 = 0 := by
    rw [hpl_of_allZero (by decide)]
    simp
  rw [i13Psi4_eq_S]
  unfold i13Psi4Sa i13Psi4Sb i13Psi4Sc i13Psi4Sd i13Psi4Se i13Psi4Sf i13Psi4Sg
  rw [
    hpl_zero_at_one, hpl_negOne_at_one, hpl_zero_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_one_at_one, hpl_negOne_zero_at_one, hpl_negOne_negOne_at_one, hpl_negOne_one_at_one,
    hpl_zero_zero_zero_at_one, hpl_zero_zero_negOne_at_one, hpl_zero_zero_one_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_negOne_negOne_at_one, hpl_zero_negOne_one_at_one,
    hpl_zero_one_zero_at_one, hpl_zero_one_negOne_at_one, hpl_zero_one_one_at_one,
    hpl_negOne_zero_zero_at_one, hpl_negOne_zero_one_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_negOne_one_zero_at_one, hpl_zero_zero_zero_zero_at_one, hpl_zero_zero_zero_one_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_one_zero_at_one, hpl_zero_zero_one_one_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_negOne_zero_one_at_one,
    hpl_zero_negOne_negOne_zero_at_one, hpl_zero_negOne_one_zero_at_one,
    hpl_zero_one_zero_zero_at_one, hpl_zero_one_zero_one_at_one, hpl_zero_one_negOne_zero_at_one,
    hpl_zero_one_one_zero_at_one, hpl_zero_one_one_one_at_one, hpl_negOne_zero_zero_zero_at_one,
    hpl_negOne_zero_zero_one_at_one, hpl_negOne_zero_negOne_zero_at_one,
    hpl_negOne_zero_one_zero_at_one, hpl_negOne_zero_one_one_at_one,
    hpl_negOne_negOne_zero_zero_at_one, hpl_negOne_negOne_zero_one_at_one,
    hpl_negOne_negOne_negOne_zero_at_one, hpl_negOne_negOne_one_zero_at_one,
    hpl_negOne_one_zero_zero_at_one, hpl_negOne_one_zero_one_at_one,
    hpl_negOne_one_negOne_zero_at_one, hpl_negOne_one_one_zero_at_one, h5,
    hpl_zero_zero_zero_zero_one_at_one, hpl_zero_zero_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_one_zero_at_one, hpl_zero_zero_zero_one_one_at_one,
    hpl_zero_zero_negOne_zero_zero_at_one, hpl_zero_zero_negOne_zero_one_at_one,
    hpl_zero_zero_negOne_negOne_zero_at_one, hpl_zero_zero_negOne_one_zero_at_one,
    hpl_zero_zero_one_zero_zero_at_one, hpl_zero_zero_one_zero_one_at_one,
    hpl_zero_zero_one_negOne_zero_at_one, hpl_zero_zero_one_one_zero_at_one,
    hpl_zero_zero_one_one_one_at_one, hpl_zero_negOne_zero_zero_zero_at_one,
    hpl_zero_negOne_zero_zero_one_at_one, hpl_zero_negOne_zero_negOne_zero_at_one,
    hpl_zero_negOne_zero_one_zero_at_one, hpl_zero_negOne_zero_one_one_at_one,
    hpl_zero_negOne_negOne_zero_zero_at_one, hpl_zero_negOne_negOne_zero_one_at_one,
    hpl_zero_negOne_negOne_negOne_zero_at_one, hpl_zero_negOne_negOne_one_zero_at_one,
    hpl_zero_negOne_one_zero_zero_at_one, hpl_zero_negOne_one_zero_one_at_one,
    hpl_zero_negOne_one_negOne_zero_at_one, hpl_zero_negOne_one_one_zero_at_one,
    hpl_zero_one_zero_zero_zero_at_one, hpl_zero_one_zero_zero_one_at_one,
    hpl_zero_one_zero_negOne_zero_at_one, hpl_zero_one_zero_one_zero_at_one,
    hpl_zero_one_zero_one_one_at_one, hpl_zero_one_negOne_zero_zero_at_one,
    hpl_zero_one_negOne_zero_one_at_one, hpl_zero_one_negOne_negOne_zero_at_one,
    hpl_zero_one_negOne_one_zero_at_one, hpl_zero_one_one_zero_zero_at_one,
    hpl_zero_one_one_zero_one_at_one, hpl_zero_one_one_negOne_zero_at_one,
    hpl_zero_one_one_one_zero_at_one]
  norm_num
  ring

theorem i13F4_zero : i13F4 0 =
      4445 / 16 - 256 * Li 4 (1 / 2) - 223 * zeta3 + 12 * zeta5 - 32 / 3 * Real.log 2 ^ 4 +
      137 / 45 * π ^ 4 - 2 / 3 * π ^ 2 * zeta3 + 32 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  unfold i13F4
  rw [i13Xi_zero, i13Psi4_one]

end QED.ThreeLoopD
