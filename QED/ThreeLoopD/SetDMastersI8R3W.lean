/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R3C

/-!
# Set (d), master `I₈`: further Lyndon-basis decompositions

The words of weight three and four met by the primitive of `p₃` that are not covered by
`QED.ThreeLoopD.SetDMastersI13R3W`, written through the shuffle product
(`QED.Polylog.HPL.hpl_mul_hpl`) in the Lyndon basis for the order `0 < -1 < 1`.

## Main results

* `QED.ThreeLoopD.i8hw_mmm` and its companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

theorem i8hw_mmm {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, negOne, negOne] x = hpl [negOne] x ^ 3 / 6 := by
  have h0 := hpl_mul_hpl [negOne] [negOne, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1 / 3) * h0 + (hpl [negOne] x / 3) * i13hw_mm hx

theorem i8hw_m1m {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, one, negOne] x = -2 * hpl [negOne, negOne, one] x +
    hpl [negOne] x * hpl [negOne, one] x := by
  have h0 := hpl_mul_hpl [one] [negOne, negOne] hx
  have h1 := hpl_mul_hpl [negOne] [one, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1
  linear_combination (-2) * h0 + (2 * hpl [one] x) * i13hw_mm hx + (1) * h1 +
    (-hpl [negOne] x) * i13hw_1m hx

theorem i8hw_1mm {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, negOne, negOne] x = hpl [negOne, negOne, one] x +
    hpl [one] x * hpl [negOne] x ^ 2 / 2 - hpl [negOne] x * hpl [negOne, one] x := by
  have h0 := hpl_mul_hpl [one] [negOne, negOne] hx
  have h1 := hpl_mul_hpl [negOne] [one, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1
  linear_combination (1) * h0 + (-hpl [one] x) * i13hw_mm hx + (-1) * h1 +
    (hpl [negOne] x) * i13hw_1m hx

theorem i8hw_1m1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, negOne, one] x = -2 * hpl [negOne, one, one] x +
    hpl [one] x * hpl [negOne, one] x := by
  have h0 := hpl_mul_hpl [one] [negOne, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0

theorem i8hw_11m {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, one, negOne] x = hpl [negOne, one, one] x + hpl [negOne] x * hpl [one] x ^ 2 / 2 -
    hpl [one] x * hpl [negOne, one] x := by
  have h0 := hpl_mul_hpl [one] [one, negOne] hx
  have h1 := hpl_mul_hpl [negOne] [one, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1
  linear_combination (-1) * h0 + (hpl [one] x) * i13hw_1m hx + (1) * h1 +
    (-hpl [negOne] x) * i13hw_11 hx

theorem i8hw_0m0m {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, negOne, zero, negOne] x = hpl [zero, negOne] x ^ 2 / 2 -
    2 * hpl [zero, zero, negOne, negOne] x := by
  have h0 := hpl_mul_hpl [zero, negOne] [zero, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1 / 2) * h0

theorem i8hw_010m {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, one, zero, negOne] x = -hpl [zero, negOne, zero, one] x -
    2 * hpl [zero, zero, one, negOne] x - 2 * hpl [zero, zero, negOne, one] x +
    hpl [zero, one] x * hpl [zero, negOne] x := by
  have h0 := hpl_mul_hpl [zero, one] [zero, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0

end QED.ThreeLoopD
