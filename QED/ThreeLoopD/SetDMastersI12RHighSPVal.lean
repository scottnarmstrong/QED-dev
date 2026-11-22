/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighSKVal

/-!
# Set (d), master `I₁₂`: the Taylor coefficients of `P(cε - 1, ε)` through order `4`

After the substitution `x = 2t/(1 + t)` (`QED.ThreeLoopD.i12HSK_integral_F_eq`), the `n`-th
Taylor coefficient of `ε ↦ P(cε - 1, ε)` at `0` is `∫₀¹ G_{c,n}`, with

  `G_{c,n}(t) = 2 ((L - c(log 2 + log (1 + t))) ^ n / t - (L - c log 2) ^ n (1/t - 1/(1 + t)))`,

`L = log 2 + log t - log (1 + t)`. Expanding the powers, `G_{c,n}` is the combination
`∑ k f_a(t) logⁱ t logʲ (1 + t)` listed in `QED.ThreeLoopD.i12HSKL_four` (and its lower-order
companions), with coefficients `k` polynomial in `c` and `log 2` (the terms `logⁱ t / t` cancel),
checked by `ring`. Linearity (`QED.ThreeLoopD.i12HSK_integral_combo`) and the closed forms of
`QED.ThreeLoopD.SetDMastersI12RHighSKVal` give `∫₀¹ G_{c,n}` for `n ≤ 4` as a polynomial in
`c`, `log 2`, `π`, `ζ(3)`, `ζ(5)`, `Li₄(1/2)`, `Li₅(1/2)`. For instance

  `∫₀¹ G_{c,1} = -(2c - 1) log² 2 - (c + 1) π²/6`.

## Main results

* `QED.ThreeLoopD.i12HSKG_zero_integral` … `QED.ThreeLoopD.i12HSKG_four_integral`.
-/

@[expose] public section

open Real Set MeasureTheory QED.Polylog QED.Polylog.HPL

namespace QED.ThreeLoopD

/-- The decomposition of `G_{c,0}`. -/
noncomputable def i12HSKL_zero (_c : ℝ) : List (ℝ × Letter × ℕ × ℕ) :=
  [(2, Letter.negOne, 0, 0)]

theorem i12HSKG_zero_eq (c t : ℝ) :
    i12HSKG c 0 t = ((i12HSKL_zero c).map fun q =>
      q.1 * (q.2.1.kernel t * (log t ^ q.2.2.1 * log (1 + t) ^ q.2.2.2))).sum := by
  simp only [i12HSKG, i12HSKL_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Letter.kernel_negOne]
  ring

/-- **The `0`-th Taylor coefficient of `P(cε - 1, ε)`**, as a polynomial in `c`. -/
theorem i12HSKG_zero_integral (c : ℝ) :
    ∫ t in Ioo (0 : ℝ) 1, i12HSKG c 0 t =
      2 * log 2 := by
  rw [setIntegral_congr_fun measurableSet_Ioo (fun t _ => i12HSKG_zero_eq c t),
    (i12HSK_integral_combo _ (by simp [i12HSKL_zero, i12HSKOk])).2]
  simp only [i12HSKL_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [i12HSK_negOne_0_0]
  ring

/-- The decomposition of `G_{c,1}`. -/
noncomputable def i12HSKL_one (c : ℝ) : List (ℝ × Letter × ℕ × ℕ) :=
  [(-2 * c, Letter.zero, 0, 1), (-2 * c * log 2 + 2 * log 2, Letter.negOne, 0, 0),
    (-2, Letter.negOne, 0, 1), (2, Letter.negOne, 1, 0)]

theorem i12HSKG_one_eq (c t : ℝ) :
    i12HSKG c 1 t = ((i12HSKL_one c).map fun q =>
      q.1 * (q.2.1.kernel t * (log t ^ q.2.2.1 * log (1 + t) ^ q.2.2.2))).sum := by
  simp only [i12HSKG, i12HSKL_one, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Letter.kernel_zero, Letter.kernel_negOne]
  ring

/-- **The `1`-th Taylor coefficient of `P(cε - 1, ε)`**, as a polynomial in `c`. -/
theorem i12HSKG_one_integral (c : ℝ) :
    ∫ t in Ioo (0 : ℝ) 1, i12HSKG c 1 t =
      -2 * c * log 2 ^ 2 - 1 / 6 * c * π ^ 2 + log 2 ^ 2 - 1 / 6 * π ^ 2 := by
  rw [setIntegral_congr_fun measurableSet_Ioo (fun t _ => i12HSKG_one_eq c t),
    (i12HSK_integral_combo _ (by simp [i12HSKL_one, i12HSKOk])).2]
  simp only [i12HSKL_one, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [i12HSK_negOne_0_0, i12HSK_negOne_0_1, i12HSK_negOne_1_0, i12HSK_zero_0_1]
  ring

/-- The decomposition of `G_{c,2}`. -/
noncomputable def i12HSKL_two (c : ℝ) : List (ℝ × Letter × ℕ × ℕ) :=
  [(4 * c ^ 2 * log 2 - 4 * c * log 2, Letter.zero, 0, 1), (2 * c ^ 2 + 4 * c, Letter.zero, 0, 2),
    (-4 * c, Letter.zero, 1, 1),
    (2 * c ^ 2 * log 2 ^ 2 - 4 * c * log 2 ^ 2 + 2 * log 2 ^ 2, Letter.negOne, 0, 0),
    (4 * c * log 2 - 4 * log 2, Letter.negOne, 0, 1), (2, Letter.negOne, 0, 2),
    (-4 * c * log 2 + 4 * log 2, Letter.negOne, 1, 0), (-4, Letter.negOne, 1, 1),
    (2, Letter.negOne, 2, 0)]

theorem i12HSKG_two_eq (c t : ℝ) :
    i12HSKG c 2 t = ((i12HSKL_two c).map fun q =>
      q.1 * (q.2.1.kernel t * (log t ^ q.2.2.1 * log (1 + t) ^ q.2.2.2))).sum := by
  simp only [i12HSKG, i12HSKL_two, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Letter.kernel_zero, Letter.kernel_negOne]
  ring

/-- **The `2`-th Taylor coefficient of `P(cε - 1, ε)`**, as a polynomial in `c`. -/
theorem i12HSKG_two_integral (c : ℝ) :
    ∫ t in Ioo (0 : ℝ) 1, i12HSKG c 2 t =
      2 * c ^ 2 * log 2 ^ 3 + 1 / 3 * c ^ 2 * log 2 * π ^ 2 + 1 / 2 * c ^ 2 * zeta3
        - 2 * c * log 2 ^ 3 + 4 * c * zeta3 + 2 / 3 * log 2 ^ 3 - 1 / 3 * log 2 * π ^ 2
        + 7 / 2 * zeta3 := by
  rw [setIntegral_congr_fun measurableSet_Ioo (fun t _ => i12HSKG_two_eq c t),
    (i12HSK_integral_combo _ (by simp [i12HSKL_two, i12HSKOk])).2]
  simp only [i12HSKL_two, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [i12HSK_negOne_0_0, i12HSK_negOne_0_1, i12HSK_negOne_0_2, i12HSK_negOne_1_0, i12HSK_negOne_1_1,
    i12HSK_negOne_2_0, i12HSK_zero_0_1, i12HSK_zero_0_2, i12HSK_zero_1_1]
  ring

/-- The decomposition of `G_{c,3}`. -/
noncomputable def i12HSKL_three (c : ℝ) : List (ℝ × Letter × ℕ × ℕ) :=
  [(-6 * c ^ 3 * log 2 ^ 2 + 12 * c ^ 2 * log 2 ^ 2 - 6 * c * log 2 ^ 2, Letter.zero, 0, 1),
    (-6 * c ^ 3 * log 2 - 6 * c ^ 2 * log 2 + 12 * c * log 2, Letter.zero, 0, 2),
    (-2 * c ^ 3 - 6 * c ^ 2 - 6 * c, Letter.zero, 0, 3),
    (12 * c ^ 2 * log 2 - 12 * c * log 2, Letter.zero, 1, 1),
    (6 * c ^ 2 + 12 * c, Letter.zero, 1, 2), (-6 * c, Letter.zero, 2, 1),
    (-2 * c ^ 3 * log 2 ^ 3 + 6 * c ^ 2 * log 2 ^ 3 - 6 * c * log 2 ^ 3
      + 2 * log 2 ^ 3, Letter.negOne, 0, 0),
    (-6 * c ^ 2 * log 2 ^ 2 + 12 * c * log 2 ^ 2 - 6 * log 2 ^ 2, Letter.negOne, 0, 1),
    (-6 * c * log 2 + 6 * log 2, Letter.negOne, 0, 2), (-2, Letter.negOne, 0, 3),
    (6 * c ^ 2 * log 2 ^ 2 - 12 * c * log 2 ^ 2 + 6 * log 2 ^ 2, Letter.negOne, 1, 0),
    (12 * c * log 2 - 12 * log 2, Letter.negOne, 1, 1), (6, Letter.negOne, 1, 2),
    (-6 * c * log 2 + 6 * log 2, Letter.negOne, 2, 0), (-6, Letter.negOne, 2, 1),
    (2, Letter.negOne, 3, 0)]

theorem i12HSKG_three_eq (c t : ℝ) :
    i12HSKG c 3 t = ((i12HSKL_three c).map fun q =>
      q.1 * (q.2.1.kernel t * (log t ^ q.2.2.1 * log (1 + t) ^ q.2.2.2))).sum := by
  simp only [i12HSKG, i12HSKL_three, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Letter.kernel_zero, Letter.kernel_negOne]
  ring

/-- **The `3`-th Taylor coefficient of `P(cε - 1, ε)`**, as a polynomial in `c`. -/
theorem i12HSKG_three_integral (c : ℝ) :
    ∫ t in Ioo (0 : ℝ) 1, i12HSKG c 3 t =
      -3 / 2 * c ^ 3 * log 2 ^ 4 - c ^ 3 * log 2 ^ 2 * π ^ 2 + 9 * c ^ 3 * log 2 * zeta3
        - 2 / 15 * c ^ 3 * π ^ 4 + 12 * c ^ 3 * Li 4 (1 / 2) + 7 / 2 * c ^ 2 * log 2 ^ 4
        - 3 / 20 * c ^ 2 * π ^ 4 + 12 * c ^ 2 * Li 4 (1 / 2) - 5 / 2 * c * log 2 ^ 4
        + c * log 2 ^ 2 * π ^ 2 - 9 * c * log 2 * zeta3 - 1 / 60 * c * π ^ 4
        - 12 * c * Li 4 (1 / 2) - 12 * Li 4 (1 / 2) := by
  rw [setIntegral_congr_fun measurableSet_Ioo (fun t _ => i12HSKG_three_eq c t),
    (i12HSK_integral_combo _ (by simp [i12HSKL_three, i12HSKOk])).2]
  simp only [i12HSKL_three, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [i12HSK_negOne_0_0, i12HSK_negOne_0_1, i12HSK_negOne_0_2, i12HSK_negOne_0_3, i12HSK_negOne_1_0,
    i12HSK_negOne_1_1, i12HSK_negOne_1_2, i12HSK_negOne_2_0, i12HSK_negOne_2_1, i12HSK_negOne_3_0,
    i12HSK_zero_0_1, i12HSK_zero_0_2, i12HSK_zero_0_3, i12HSK_zero_1_1, i12HSK_zero_1_2,
    i12HSK_zero_2_1]
  ring

/-- The decomposition of `G_{c,4}`. -/
noncomputable def i12HSKL_four (c : ℝ) : List (ℝ × Letter × ℕ × ℕ) :=
  [
    (8 * c ^ 4 * log 2 ^ 3 - 24 * c ^ 3 * log 2 ^ 3 + 24 * c ^ 2 * log 2 ^ 3
      - 8 * c * log 2 ^ 3, Letter.zero, 0, 1),
    (12 * c ^ 4 * log 2 ^ 2 - 36 * c ^ 2 * log 2 ^ 2 + 24 * c * log 2 ^ 2, Letter.zero, 0, 2),
    (8 * c ^ 4 * log 2 + 16 * c ^ 3 * log 2 - 24 * c * log 2, Letter.zero, 0, 3),
    (2 * c ^ 4 + 8 * c ^ 3 + 12 * c ^ 2 + 8 * c, Letter.zero, 0, 4),
    (-24 * c ^ 3 * log 2 ^ 2 + 48 * c ^ 2 * log 2 ^ 2 - 24 * c * log 2 ^ 2, Letter.zero, 1, 1),
    (-24 * c ^ 3 * log 2 - 24 * c ^ 2 * log 2 + 48 * c * log 2, Letter.zero, 1, 2),
    (-8 * c ^ 3 - 24 * c ^ 2 - 24 * c, Letter.zero, 1, 3),
    (24 * c ^ 2 * log 2 - 24 * c * log 2, Letter.zero, 2, 1),
    (12 * c ^ 2 + 24 * c, Letter.zero, 2, 2), (-8 * c, Letter.zero, 3, 1),
    (2 * c ^ 4 * log 2 ^ 4 - 8 * c ^ 3 * log 2 ^ 4 + 12 * c ^ 2 * log 2 ^ 4 - 8 * c * log 2 ^ 4
      + 2 * log 2 ^ 4, Letter.negOne, 0, 0),

    (8 * c ^ 3 * log 2 ^ 3 - 24 * c ^ 2 * log 2 ^ 3 + 24 * c * log 2 ^ 3
      - 8 * log 2 ^ 3, Letter.negOne, 0, 1),
    (12 * c ^ 2 * log 2 ^ 2 - 24 * c * log 2 ^ 2 + 12 * log 2 ^ 2, Letter.negOne, 0, 2),
    (8 * c * log 2 - 8 * log 2, Letter.negOne, 0, 3), (2, Letter.negOne, 0, 4),
    (-8 * c ^ 3 * log 2 ^ 3 + 24 * c ^ 2 * log 2 ^ 3 - 24 * c * log 2 ^ 3
      + 8 * log 2 ^ 3, Letter.negOne, 1, 0),
    (-24 * c ^ 2 * log 2 ^ 2 + 48 * c * log 2 ^ 2 - 24 * log 2 ^ 2, Letter.negOne, 1, 1),
    (-24 * c * log 2 + 24 * log 2, Letter.negOne, 1, 2), (-8, Letter.negOne, 1, 3),
    (12 * c ^ 2 * log 2 ^ 2 - 24 * c * log 2 ^ 2 + 12 * log 2 ^ 2, Letter.negOne, 2, 0),
    (24 * c * log 2 - 24 * log 2, Letter.negOne, 2, 1), (12, Letter.negOne, 2, 2),
    (-8 * c * log 2 + 8 * log 2, Letter.negOne, 3, 0), (-8, Letter.negOne, 3, 1),
    (2, Letter.negOne, 4, 0)]

theorem i12HSKG_four_eq (c t : ℝ) :
    i12HSKG c 4 t = ((i12HSKL_four c).map fun q =>
      q.1 * (q.2.1.kernel t * (log t ^ q.2.2.1 * log (1 + t) ^ q.2.2.2))).sum := by
  simp only [i12HSKG, i12HSKL_four, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Letter.kernel_zero, Letter.kernel_negOne]
  ring

/-- **The `4`-th Taylor coefficient of `P(cε - 1, ε)`**, as a polynomial in `c`. -/
theorem i12HSKG_four_integral (c : ℝ) :
    ∫ t in Ioo (0 : ℝ) 1, i12HSKG c 4 t =
      -8 / 5 * c ^ 4 * log 2 ^ 5 + 4 * c ^ 4 * log 2 ^ 3 * π ^ 2
        - 60 * c ^ 4 * log 2 ^ 2 * zeta3 + 8 / 15 * c ^ 4 * log 2 * π ^ 4
        - 96 * c ^ 4 * log 2 * Li 4 (1 / 2) + 48 * c ^ 4 * zeta5
        - 48 * c ^ 4 * Li 5 (1 / 2) - 36 / 5 * c ^ 3 * log 2 ^ 5
        + 4 / 3 * c ^ 3 * log 2 ^ 3 * π ^ 2 - 24 * c ^ 3 * log 2 ^ 2 * zeta3
        + 1 / 15 * c ^ 3 * log 2 * π ^ 4 - 96 * c ^ 3 * log 2 * Li 4 (1 / 2)
        - 4 * c ^ 3 * π ^ 2 * zeta3 + 285 / 2 * c ^ 3 * zeta5 - 96 * c ^ 3 * Li 5 (1 / 2)
        + 8 * c ^ 2 * log 2 ^ 5 - 4 * c ^ 2 * log 2 ^ 3 * π ^ 2
        + 60 * c ^ 2 * log 2 ^ 2 * zeta3 - 8 / 15 * c ^ 2 * log 2 * π ^ 4
        + 96 * c ^ 2 * log 2 * Li 4 (1 / 2) - 8 * c ^ 2 * π ^ 2 * zeta3
        + 96 * c ^ 2 * zeta5 + 6 / 5 * c * log 2 ^ 5 - 4 / 3 * c * log 2 ^ 3 * π ^ 2
        + 24 * c * log 2 ^ 2 * zeta3 - 1 / 15 * c * log 2 * π ^ 4
        + 96 * c * log 2 * Li 4 (1 / 2) - 4 * c * π ^ 2 * zeta3 + 3 / 2 * c * zeta5
        + 96 * c * Li 5 (1 / 2) + 48 * Li 5 (1 / 2) := by
  rw [setIntegral_congr_fun measurableSet_Ioo (fun t _ => i12HSKG_four_eq c t),
    (i12HSK_integral_combo _ (by simp [i12HSKL_four, i12HSKOk])).2]
  simp only [i12HSKL_four, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [i12HSK_negOne_0_0, i12HSK_negOne_0_1, i12HSK_negOne_0_2, i12HSK_negOne_0_3, i12HSK_negOne_0_4,
    i12HSK_negOne_1_0, i12HSK_negOne_1_1, i12HSK_negOne_1_2, i12HSK_negOne_1_3, i12HSK_negOne_2_0,
    i12HSK_negOne_2_1, i12HSK_negOne_2_2, i12HSK_negOne_3_0, i12HSK_negOne_3_1, i12HSK_negOne_4_0,
    i12HSK_zero_0_1, i12HSK_zero_0_2, i12HSK_zero_0_3, i12HSK_zero_0_4, i12HSK_zero_1_1,
    i12HSK_zero_1_2, i12HSK_zero_1_3, i12HSK_zero_2_1, i12HSK_zero_2_2, i12HSK_zero_3_1]
  ring

end QED.ThreeLoopD
