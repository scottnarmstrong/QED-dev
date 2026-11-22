/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLLowWeight
public import QED.Polylog.HPLShuffle

/-!
# Set (d), master `I₁₃`: harmonic polylogarithms in a Lyndon basis

For the letters ordered `0 < -1 < 1`, the shuffle algebra of harmonic polylogarithms is the
polynomial algebra on the Lyndon words. This file writes each word `w` used for the third
coefficient of `Rem` (`QED.ThreeLoopD.i13Psi3` and the third bubble coefficient) as a polynomial
in `log x` and the `H(l; x)`, `l` a Lyndon word, on `(0, 1)`: `QED.ThreeLoopD.i13hw_m0` is
`H(-1, 0) = log x H(-1) - H(0, -1)`, and so on (the name codes the word, `m` for `-1`). Each
identity is a combination of shuffle products (`QED.Polylog.HPL.hpl_mul_hpl`).

Every Lyndon word of length at least two begins with `0` and does not end with `0`, so the
basis functions other than `log x` have power series at `0` (`QED.Polylog.HPL.hasSum_coef_mul_pow`).
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

theorem i13hw_00 (x : ℝ) :
    hpl [zero, zero] x = Real.log x ^ 2 / 2 := by
  rw [hpl_of_allZero (by decide)]
  simp

theorem i13hw_m0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, zero] x = -hpl [zero, negOne] x + Real.log x * hpl [negOne] x := by
  have h0 := hpl_mul_hpl [zero] [negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0 + (1) * hpl [negOne] x * hpl_zero x

theorem i13hw_mm {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, negOne] x = hpl [negOne] x ^ 2 / 2 := by
  have h0 := hpl_mul_hpl [negOne] [negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1 / 2) * h0

theorem i13hw_10 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, zero] x = -hpl [zero, one] x + Real.log x * hpl [one] x := by
  have h0 := hpl_mul_hpl [zero] [one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0 + (1) * hpl [one] x * hpl_zero x

theorem i13hw_1m {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, negOne] x = -hpl [negOne, one] x + hpl [one] x * hpl [negOne] x := by
  have h0 := hpl_mul_hpl [one] [negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0

theorem i13hw_11 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, one] x = hpl [one] x ^ 2 / 2 := by
  have h0 := hpl_mul_hpl [one] [one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1 / 2) * h0

theorem i13hw_000 (x : ℝ) :
    hpl [zero, zero, zero] x = Real.log x ^ 3 / 6 := by
  rw [hpl_of_allZero (by decide)]
  simp [Nat.factorial]

theorem i13hw_0m0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, negOne, zero] x = -2 * hpl [zero, zero, negOne] x + Real.log x * hpl [zero, negOne] x
    := by
  have h0 := hpl_mul_hpl [zero] [zero, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0 + (1) * hpl [zero, negOne] x * hpl_zero x

theorem i13hw_010 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, one, zero] x = -2 * hpl [zero, zero, one] x + Real.log x * hpl [zero, one] x := by
  have h0 := hpl_mul_hpl [zero] [zero, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0 + (1) * hpl [zero, one] x * hpl_zero x

theorem i13hw_m00 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, zero, zero] x = hpl [zero, zero, negOne] x + hpl [negOne] x * Real.log x ^ 2 / 2 -
    Real.log x * hpl [zero, negOne] x := by
  have h0 := hpl_mul_hpl [zero] [negOne, zero] hx
  have h1 := hpl_mul_hpl [negOne] [zero, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1
  linear_combination (-1) * h0 + (1) * hpl [negOne, zero] x * hpl_zero x + (Real.log x) * i13hw_m0
    hx + (1) * h1 + (-hpl [negOne] x) * i13hw_00 x

theorem i13hw_m0m {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, zero, negOne] x = -2 * hpl [zero, negOne, negOne] x + hpl [zero, negOne] x * hpl
    [negOne] x := by
  have h0 := hpl_mul_hpl [negOne] [zero, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0

theorem i13hw_m01 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, zero, one] x = -hpl [zero, one, negOne] x - hpl [zero, negOne, one] x + hpl [zero,
    one] x * hpl [negOne] x := by
  have h0 := hpl_mul_hpl [negOne] [zero, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0

theorem i13hw_mm0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, negOne, zero] x = hpl [zero, negOne, negOne] x + Real.log x * hpl [negOne] x ^ 2 /
    2 - hpl [zero, negOne] x * hpl [negOne] x := by
  have h0 := hpl_mul_hpl [zero] [negOne, negOne] hx
  have h1 := hpl_mul_hpl [negOne] [negOne, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1
  linear_combination (1) * h0 + (-1) * hpl [negOne, negOne] x * hpl_zero x + (-Real.log x) *
    i13hw_mm hx + (-1) * h1 + (hpl [negOne] x) * i13hw_m0 hx

theorem i13hw_m10 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, one, zero] x = hpl [zero, one, negOne] x + Real.log x * hpl [negOne, one] x - hpl
    [zero, one] x * hpl [negOne] x := by
  have h0 := hpl_mul_hpl [negOne] [one, zero] hx
  have h1 := hpl_mul_hpl [zero] [one, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1
  linear_combination (-1) * h0 + (hpl [negOne] x) * i13hw_10 hx + (1) * h1 + (-1) * hpl [one,
    negOne] x * hpl_zero x + (-Real.log x) * i13hw_1m hx

theorem i13hw_100 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, zero, zero] x = hpl [zero, zero, one] x + hpl [one] x * Real.log x ^ 2 / 2 - Real.log
    x * hpl [zero, one] x := by
  have h0 := hpl_mul_hpl [zero] [one, zero] hx
  have h1 := hpl_mul_hpl [one] [zero, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1
  linear_combination (-1) * h0 + (1) * hpl [one, zero] x * hpl_zero x + (Real.log x) * i13hw_10 hx +
    (1) * h1 + (-hpl [one] x) * i13hw_00 x

theorem i13hw_10m {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, zero, negOne] x = -hpl [zero, one, negOne] x - hpl [zero, negOne, one] x + hpl [zero,
    negOne] x * hpl [one] x := by
  have h0 := hpl_mul_hpl [one] [zero, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0

theorem i13hw_101 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, zero, one] x = -2 * hpl [zero, one, one] x + hpl [zero, one] x * hpl [one] x := by
  have h0 := hpl_mul_hpl [one] [zero, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0

theorem i13hw_1m0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, negOne, zero] x = hpl [zero, negOne, one] x - Real.log x * hpl [negOne, one] x - hpl
    [zero, negOne] x * hpl [one] x + Real.log x * hpl [one] x * hpl [negOne] x := by
  have h0 := hpl_mul_hpl [one] [negOne, zero] hx
  have h1 := hpl_mul_hpl [zero] [negOne, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1
  linear_combination (-1) * h0 + (hpl [one] x) * i13hw_m0 hx + (1) * h1 + (-1) * hpl [negOne, one] x
    * hpl_zero x

theorem i13hw_110 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, one, zero] x = hpl [zero, one, one] x + Real.log x * hpl [one] x ^ 2 / 2 - hpl [zero,
    one] x * hpl [one] x := by
  have h0 := hpl_mul_hpl [zero] [one, one] hx
  have h1 := hpl_mul_hpl [one] [one, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1
  linear_combination (1) * h0 + (-1) * hpl [one, one] x * hpl_zero x + (-Real.log x) * i13hw_11 hx +
    (-1) * h1 + (hpl [one] x) * i13hw_10 hx

theorem i13hw_111 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, one, one] x = hpl [one] x ^ 3 / 6 := by
  have h0 := hpl_mul_hpl [one] [one, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1 / 3) * h0 + (hpl [one] x / 3) * i13hw_11 hx

theorem i13hw_00m0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, zero, negOne, zero] x = -3 * hpl [zero, zero, zero, negOne] x + Real.log x * hpl
    [zero, zero, negOne] x := by
  have h0 := hpl_mul_hpl [zero] [zero, zero, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0 + (1) * hpl [zero, zero, negOne] x * hpl_zero x

theorem i13hw_0010 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, zero, one, zero] x = -3 * hpl [zero, zero, zero, one] x + Real.log x * hpl [zero,
    zero, one] x := by
  have h0 := hpl_mul_hpl [zero] [zero, zero, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0 + (1) * hpl [zero, zero, one] x * hpl_zero x

theorem i13hw_0m00 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, negOne, zero, zero] x = 3 * hpl [zero, zero, zero, negOne] x + hpl [zero, negOne] x *
    Real.log x ^ 2 / 2 - 2 * Real.log x * hpl [zero, zero, negOne] x := by
  have h0 := hpl_mul_hpl [zero] [zero, negOne, zero] hx
  have h1 := hpl_mul_hpl [zero] [negOne, zero, zero] hx
  have h2 := hpl_mul_hpl [negOne] [zero, zero, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1 h2
  linear_combination (-3 / 2) * h0 + (3 / 2) * hpl [zero, negOne, zero] x * hpl_zero x + (3 / 2 *
    Real.log x) * i13hw_0m0 hx + (-1) * h1 + (1) * hpl [negOne, zero, zero] x * hpl_zero x +
    (Real.log x) * i13hw_m00 hx + (3) * h2 + (-3 * hpl [negOne] x) * i13hw_000 x

theorem i13hw_0mm0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, negOne, negOne, zero] x = -hpl [zero, negOne] x ^ 2 / 2 + Real.log x * hpl [zero,
    negOne, negOne] x := by
  have h0 := hpl_mul_hpl [zero, negOne] [negOne, zero] hx
  have h1 := hpl_mul_hpl [zero] [negOne, zero, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1
  linear_combination (-1 / 2) * h0 + (hpl [zero, negOne] x / 2) * i13hw_m0 hx + (1 / 2) * h1 + (-1 /
    2) * hpl [negOne, zero, negOne] x * hpl_zero x + (-Real.log x / 2) * i13hw_m0m hx

theorem i13hw_0m10 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, negOne, one, zero] x = -hpl [zero, negOne, zero, one] x - 2 * hpl [zero, zero,
    negOne, one] x + Real.log x * hpl [zero, negOne, one] x := by
  have h0 := hpl_mul_hpl [zero] [zero, negOne, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1) * h0 + (1) * hpl [zero, negOne, one] x * hpl_zero x

theorem i13hw_0100 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, one, zero, zero] x = 3 * hpl [zero, zero, zero, one] x + hpl [zero, one] x * Real.log
    x ^ 2 / 2 - 2 * Real.log x * hpl [zero, zero, one] x := by
  have h0 := hpl_mul_hpl [zero] [zero, one, zero] hx
  have h1 := hpl_mul_hpl [zero] [one, zero, zero] hx
  have h2 := hpl_mul_hpl [one] [zero, zero, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1 h2
  linear_combination (-3 / 2) * h0 + (3 / 2) * hpl [zero, one, zero] x * hpl_zero x + (3 / 2 *
    Real.log x) * i13hw_010 hx + (-1) * h1 + (1) * hpl [one, zero, zero] x * hpl_zero x + (Real.log
    x) * i13hw_100 hx + (3) * h2 + (-3 * hpl [one] x) * i13hw_000 x

theorem i13hw_0101 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, one, zero, one] x = hpl [zero, one] x ^ 2 / 2 - 2 * hpl [zero, zero, one, one] x :=
    by
  have h0 := hpl_mul_hpl [zero, one] [zero, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0
  linear_combination (-1 / 2) * h0

theorem i13hw_01m0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, one, negOne, zero] x = hpl [zero, negOne, zero, one] x + 2 * hpl [zero, zero, negOne,
    one] x + Real.log x * hpl [zero, one, negOne] x - hpl [zero, one] x * hpl [zero, negOne] x := by
  have h0 := hpl_mul_hpl [zero, negOne] [one, zero] hx
  have h1 := hpl_mul_hpl [zero] [zero, negOne, one] hx
  have h2 := hpl_mul_hpl [zero] [one, zero, negOne] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1 h2
  linear_combination (-1) * h0 + (hpl [zero, negOne] x) * i13hw_10 hx + (1) * h1 + (-1) * hpl [zero,
    negOne, one] x * hpl_zero x + (1) * h2 + (-1) * hpl [one, zero, negOne] x * hpl_zero x +
    (-Real.log x) * i13hw_10m hx

theorem i13hw_0110 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, one, one, zero] x = -hpl [zero, one] x ^ 2 / 2 + Real.log x * hpl [zero, one, one] x
    := by
  have h0 := hpl_mul_hpl [zero, one] [one, zero] hx
  have h1 := hpl_mul_hpl [zero] [one, zero, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at h0 h1
  linear_combination (-1 / 2) * h0 + (hpl [zero, one] x / 2) * i13hw_10 hx + (1 / 2) * h1 + (-1 / 2)
    * hpl [one, zero, one] x * hpl_zero x + (-Real.log x / 2) * i13hw_101 hx

end QED.ThreeLoopD
