/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4C
public import QED.ThreeLoopD.SetDMastersI8R3L
public import QED.ThreeLoopD.SetDMastersI13R4S

/-!
# Set (d), master `I₈`: Lyndon-basis decompositions of weight four and five

The words of weight four and five met by the primitive of `p₄` that are not covered by
`QED.ThreeLoopD.SetDMastersI13R3W`, `QED.ThreeLoopD.SetDMastersI13R4W`,
`QED.ThreeLoopD.SetDMastersI13R4X` and `QED.ThreeLoopD.SetDMastersI8R3W`, written through the
shuffle product (`QED.Polylog.HPL.hpl_mul_hpl`) in the Lyndon basis for the order `0 < -1 < 1`.

## Main results

* `QED.ThreeLoopD.i8hw_mmmm` and its companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

theorem i8hw_m0m1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, zero, negOne, one] x = -hpl [zero, negOne, one, negOne] x -
    2 * hpl [zero, negOne, negOne, one] x + hpl [zero, negOne, one] x * hpl [negOne] x := by
  have h0 := hpl_mul_hpl [negOne] [zero, negOne, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0

theorem i8hw_mm0m {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, negOne, zero, negOne] x = 3 * hpl [zero, negOne, negOne, negOne] x +
    hpl [zero, negOne] x * hpl [negOne] x ^ 2 / 2 -
    2 * hpl [zero, negOne, negOne] x * hpl [negOne] x := by
  have h0 := hpl_mul_hpl [zero] [negOne, negOne, negOne] hx
  have h1 := hpl_mul_hpl [negOne] [negOne, zero, negOne] hx
  have h2 := hpl_mul_hpl [negOne] [negOne, negOne, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1 h2
  linear_combination (3) * h0 + (-3) * hpl [negOne, negOne, negOne] x * hpl_zero x +
    (-3 * Real.log x) * i13hw_mmm hx + (-3 / 2) * h1 +
    (3 / 2 * hpl [negOne] x) * i13hw_m0m hx + (-1) * h2 + (hpl [negOne] x) * i13hw_mm0 hx

theorem i8hw_mmmm {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, negOne, negOne, negOne] x = hpl [negOne] x ^ 4 / 24 := by
  have h0 := hpl_mul_hpl [negOne] [negOne, negOne, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1 / 4) * h0 + (hpl [negOne] x / 4) * i13hw_mmm hx

theorem i8hw_mm1m {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, negOne, one, negOne] x = -3 * hpl [negOne, negOne, negOne, one] x +
    hpl [negOne] x * hpl [negOne, negOne, one] x := by
  have h0 := hpl_mul_hpl [negOne] [negOne, negOne, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0

theorem i8hw_m10m {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, one, zero, negOne] x = hpl [zero, negOne, one, negOne] x +
    2 * hpl [zero, one, negOne, negOne] x + hpl [zero, negOne] x * hpl [negOne, one] x -
    hpl [zero, one, negOne] x * hpl [negOne] x - hpl [zero, negOne, one] x * hpl [negOne] x := by
  have h0 := hpl_mul_hpl [one] [negOne, zero, negOne] hx
  have h1 := hpl_mul_hpl [negOne] [one, zero, negOne] hx
  have h2 := hpl_mul_hpl [zero, negOne] [negOne, one] hx
  have h3 := hpl_mul_hpl [one] [zero, negOne, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    at h0 h1 h2 h3
  linear_combination (1) * h0 + (-hpl [one] x) * i13hw_m0m hx + (-1) * h1 +
    (hpl [negOne] x) * i13hw_10m hx + (-1) * h2 + (2) * h3

theorem i8hw_m1mm {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, one, negOne, negOne] x = 3 * hpl [negOne, negOne, negOne, one] x +
    hpl [negOne, one] x * hpl [negOne] x ^ 2 / 2 -
    2 * hpl [negOne] x * hpl [negOne, negOne, one] x := by
  have h0 := hpl_mul_hpl [one] [negOne, negOne, negOne] hx
  have h1 := hpl_mul_hpl [negOne] [one, negOne, negOne] hx
  have h2 := hpl_mul_hpl [negOne] [negOne, one, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1 h2
  linear_combination (3) * h0 + (-3 * hpl [one] x) * i13hw_mmm hx + (-1) * h1 +
    (hpl [negOne] x) * i13hw_1mm hx + (-3 / 2) * h2 + (3 / 2 * hpl [negOne] x) * i8hw_m1m hx

theorem i8hw_m1m1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, one, negOne, one] x = hpl [negOne, one] x ^ 2 / 2 -
    2 * hpl [negOne, negOne, one, one] x := by
  have h0 := hpl_mul_hpl [one] [negOne, one, negOne] hx
  have h1 := hpl_mul_hpl [one] [negOne, negOne, one] hx
  have h2 := hpl_mul_hpl [negOne, one] [one, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1 h2
  linear_combination (-1 / 2) * h0 + (hpl [one] x / 2) * i8hw_m1m hx + (-1) * h1 +
    (1 / 2) * h2 + (-hpl [negOne, one] x / 2) * i13hw_1m hx

theorem i8hw_m11m {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, one, one, negOne] x = -hpl [negOne, one] x ^ 2 / 2 +
    hpl [negOne] x * hpl [negOne, one, one] x := by
  have h0 := hpl_mul_hpl [one] [negOne, one, negOne] hx
  have h1 := hpl_mul_hpl [negOne] [one, one, negOne] hx
  have h2 := hpl_mul_hpl [negOne, one] [one, negOne] hx
  have h3 := hpl_mul_hpl [one] [one, negOne, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    at h0 h1 h2 h3
  linear_combination (1 / 2) * h0 + (-hpl [one] x / 2) * i8hw_m1m hx + (-1) * h1 +
    (hpl [negOne] x) * i13hw_11m hx + (-1 / 2) * h2 + (hpl [negOne, one] x / 2) * i13hw_1m hx +
    (1) * h3 + (-hpl [one] x) * i13hw_1mm hx

theorem i8hw_1mmm {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, negOne, negOne, negOne] x = -hpl [negOne, negOne, negOne, one] x +
    hpl [negOne] x * hpl [negOne, negOne, one] x -
    hpl [negOne, one] x * hpl [negOne] x ^ 2 / 2 + hpl [one] x * hpl [negOne] x ^ 3 / 6 := by
  have h0 := hpl_mul_hpl [one] [negOne, negOne, negOne] hx
  have h1 := hpl_mul_hpl [negOne] [negOne, one, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1
  linear_combination (-1) * h0 + (hpl [one] x) * i13hw_mmm hx + (1 / 2) * h1 +
    (-hpl [negOne] x / 2) * i8hw_m1m hx

theorem i8hw_1mm1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, negOne, negOne, one] x = -hpl [negOne, one] x ^ 2 / 2 +
    hpl [one] x * hpl [negOne, negOne, one] x := by
  have h0 := hpl_mul_hpl [negOne, one] [one, negOne] hx
  have h1 := hpl_mul_hpl [one] [negOne, one, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1
  linear_combination (-1 / 2) * h0 + (hpl [negOne, one] x / 2) * i13hw_1m hx + (1 / 2) * h1 +
    (-hpl [one] x / 2) * i8hw_m1m hx

theorem i8hw_1m1m {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, negOne, one, negOne] x = hpl [negOne, one] x ^ 2 / 2 +
    2 * hpl [negOne, negOne, one, one] x - 2 * hpl [one] x * hpl [negOne, negOne, one] x -
    2 * hpl [negOne] x * hpl [negOne, one, one] x +
    hpl [one] x * hpl [negOne] x * hpl [negOne, one] x := by
  have h0 := hpl_mul_hpl [one] [one, negOne, negOne] hx
  have h1 := hpl_mul_hpl [one] [negOne, one, negOne] hx
  have h2 := hpl_mul_hpl [negOne] [one, one, negOne] hx
  have h3 := hpl_mul_hpl [negOne, one] [one, negOne] hx
  have h4 := hpl_mul_hpl [one] [negOne, negOne, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    at h0 h1 h2 h3 h4
  linear_combination (-2) * h0 + (2 * hpl [one] x) * i13hw_1mm hx + (-3 / 2) * h1 +
    (3 / 2 * hpl [one] x) * i8hw_m1m hx + (2) * h2 + (-2 * hpl [negOne] x) * i13hw_11m hx +
    (1 / 2) * h3 + (-hpl [negOne, one] x / 2) * i13hw_1m hx + (1) * h4

theorem i8hw_1m11 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, negOne, one, one] x = -3 * hpl [negOne, one, one, one] x +
    hpl [one] x * hpl [negOne, one, one] x := by
  have h0 := hpl_mul_hpl [one] [negOne, one, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0

theorem i8hw_11mm {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, one, negOne, negOne] x = -hpl [negOne, negOne, one, one] x +
    hpl [one] x * hpl [negOne, negOne, one] x + hpl [negOne] x * hpl [negOne, one, one] x +
    hpl [one] x ^ 2 * hpl [negOne] x ^ 2 / 4 -
    hpl [one] x * hpl [negOne] x * hpl [negOne, one] x := by
  have h0 := hpl_mul_hpl [one] [one, negOne, negOne] hx
  have h1 := hpl_mul_hpl [negOne] [one, one, negOne] hx
  have h2 := hpl_mul_hpl [one] [negOne, one, negOne] hx
  have h3 := hpl_mul_hpl [one] [negOne, negOne, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    at h0 h1 h2 h3
  linear_combination (1 / 2) * h0 + (-hpl [one] x / 2) * i13hw_1mm hx + (-1) * h1 +
    (hpl [negOne] x) * i13hw_11m hx + (1 / 2) * h2 + (-hpl [one] x / 2) * i8hw_m1m hx +
    (-1 / 2) * h3

theorem i8hw_11m1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, one, negOne, one] x = 3 * hpl [negOne, one, one, one] x +
    hpl [negOne, one] x * hpl [one] x ^ 2 / 2 - 2 * hpl [one] x * hpl [negOne, one, one] x := by
  have h0 := hpl_mul_hpl [one] [one, one, negOne] hx
  have h1 := hpl_mul_hpl [one] [one, negOne, one] hx
  have h2 := hpl_mul_hpl [negOne] [one, one, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1 h2
  linear_combination (-1) * h0 + (hpl [one] x) * i13hw_11m hx + (-3 / 2) * h1 +
    (3 / 2 * hpl [one] x) * i13hw_1m1 hx + (3) * h2 + (-3 * hpl [negOne] x) * i13hw_111 hx

theorem i8hw_111m {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, one, one, negOne] x = -hpl [negOne, one, one, one] x +
    hpl [one] x * hpl [negOne, one, one] x - hpl [negOne, one] x * hpl [one] x ^ 2 / 2 +
    hpl [negOne] x * hpl [one] x ^ 3 / 6 := by
  have h0 := hpl_mul_hpl [negOne] [one, one, one] hx
  have h1 := hpl_mul_hpl [one] [one, negOne, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1
  linear_combination (-1) * h0 + (hpl [negOne] x) * i13hw_111 hx + (1 / 2) * h1 +
    (-hpl [one] x / 2) * i13hw_1m1 hx

theorem i8hw_0m00m {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, negOne, zero, zero, negOne] x = -6 * hpl [zero, zero, zero, negOne, negOne] x -
    3 * hpl [zero, zero, negOne, zero, negOne] x +
    hpl [zero, zero, negOne] x * hpl [zero, negOne] x := by
  have h0 := hpl_mul_hpl [zero, negOne] [zero, zero, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0

theorem i8hw_0mm0m {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, negOne, negOne, zero, negOne] x = -6 * hpl [zero, zero, negOne, negOne, negOne] x -
    3 * hpl [zero, negOne, zero, negOne, negOne] x +
    hpl [zero, negOne] x * hpl [zero, negOne, negOne] x := by
  have h0 := hpl_mul_hpl [zero, negOne] [zero, negOne, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0

theorem i8hw_0m10m {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, negOne, one, zero, negOne] x = -hpl [zero, negOne, zero, one, negOne] x -
    4 * hpl [zero, zero, negOne, negOne, one] x - 2 * hpl [zero, zero, negOne, one, negOne] x -
    2 * hpl [zero, negOne, zero, negOne, one] x +
    hpl [zero, negOne] x * hpl [zero, negOne, one] x := by
  have h0 := hpl_mul_hpl [zero, negOne] [zero, negOne, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0

theorem i8hw_0100m {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, one, zero, zero, negOne] x = -hpl [zero, zero, negOne, zero, one] x -
    3 * hpl [zero, zero, zero, one, negOne] x - 3 * hpl [zero, zero, zero, negOne, one] x -
    2 * hpl [zero, zero, one, zero, negOne] x + hpl [zero, zero, negOne] x * hpl [zero, one] x := by
  have h0 := hpl_mul_hpl [zero, one] [zero, zero, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0

theorem i8hw_010mm {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, one, zero, negOne, negOne] x = -hpl [zero, negOne, zero, one, negOne] x -
    hpl [zero, negOne, zero, negOne, one] x - hpl [zero, negOne, negOne, zero, one] x -
    2 * hpl [zero, zero, one, negOne, negOne] x - 2 * hpl [zero, zero, negOne, one, negOne] x -
    2 * hpl [zero, zero, negOne, negOne, one] x +
    hpl [zero, one] x * hpl [zero, negOne, negOne] x := by
  have h0 := hpl_mul_hpl [zero, one] [zero, negOne, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0

theorem i8hw_010m1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, one, zero, negOne, one] x = -hpl [zero, negOne, one, zero, one] x -
    4 * hpl [zero, zero, negOne, one, one] x - 2 * hpl [zero, zero, one, negOne, one] x -
    2 * hpl [zero, negOne, zero, one, one] x + hpl [zero, one] x * hpl [zero, negOne, one] x := by
  have h0 := hpl_mul_hpl [zero, one] [zero, negOne, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0

theorem i8hw_01m0m {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, one, negOne, zero, negOne] x = hpl [zero, negOne, zero, one, negOne] x +
    2 * hpl [zero, zero, negOne, one, negOne] x + 2 * hpl [zero, negOne, zero, negOne, one] x +
    2 * hpl [zero, negOne, negOne, zero, one] x + 4 * hpl [zero, zero, negOne, negOne, one] x +
    hpl [zero, one, negOne] x * hpl [zero, negOne] x -
    2 * hpl [zero, one] x * hpl [zero, negOne, negOne] x := by
  have h0 := hpl_mul_hpl [zero] [one, negOne, zero, negOne] hx
  have h1 := hpl_mul_hpl [zero, negOne] [one, zero, negOne] hx
  have h2 := hpl_mul_hpl [zero, negOne] [one, negOne, zero] hx
  have h3 := hpl_mul_hpl [zero, negOne, negOne] [one, zero] hx
  have h4 := hpl_mul_hpl [zero] [zero, negOne, one, negOne] hx
  have h5 := hpl_mul_hpl [zero] [zero, negOne, negOne, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    at h0 h1 h2 h3 h4 h5
  linear_combination (-1) * h0 + (1) * hpl [one, negOne, zero, negOne] x * hpl_zero x +
    (Real.log x) * i13hw_1m0m hx + (1) * h1 + (-hpl [zero, negOne] x) * i13hw_10m hx +
    (1) * h2 + (-hpl [zero, negOne] x) * i13hw_1m0 hx + (-2) * h3 +
    (2 * hpl [zero, negOne, negOne] x) * i13hw_10 hx + (1) * h4 +
    (-1) * hpl [zero, negOne, one, negOne] x * hpl_zero x + (2) * h5 +
    (-2) * hpl [zero, negOne, negOne, one] x * hpl_zero x

theorem i8hw_0110m {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, one, one, zero, negOne] x = hpl [zero, negOne, zero, one, one] x +
    hpl [zero, negOne, one, zero, one] x - hpl [zero, one, zero, one, negOne] x -
    2 * hpl [zero, zero, one, one, negOne] x + 2 * hpl [zero, zero, negOne, one, one] x +
    hpl [zero, one, one] x * hpl [zero, negOne] x -
    hpl [zero, one] x * hpl [zero, negOne, one] x := by
  have h0 := hpl_mul_hpl [zero] [zero, one, one, negOne] hx
  have h1 := hpl_mul_hpl [zero] [one, one, zero, negOne] hx
  have h2 := hpl_mul_hpl [zero, one] [one, zero, negOne] hx
  have h3 := hpl_mul_hpl [zero, negOne] [one, one, zero] hx
  have h4 := hpl_mul_hpl [zero, one, negOne] [one, zero] hx
  have h5 := hpl_mul_hpl [zero] [zero, negOne, one, one] hx
  have h6 := hpl_mul_hpl [zero] [one, zero, negOne, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    at h0 h1 h2 h3 h4 h5 h6
  linear_combination (-1) * h0 + (1) * hpl [zero, one, one, negOne] x * hpl_zero x + (1) * h1 +
    (-1) * hpl [one, one, zero, negOne] x * hpl_zero x + (-Real.log x) * i13hw_110m hx +
    (-1) * h2 + (hpl [zero, one] x) * i13hw_10m hx + (-1) * h3 +
    (hpl [zero, negOne] x) * i13hw_110 hx + (1) * h4 +
    (-hpl [zero, one, negOne] x) * i13hw_10 hx + (1) * h5 +
    (-1) * hpl [zero, negOne, one, one] x * hpl_zero x + (1) * h6 +
    (-1) * hpl [one, zero, negOne, one] x * hpl_zero x + (-Real.log x) * i13hw_10m1 hx

end QED.ThreeLoopD
