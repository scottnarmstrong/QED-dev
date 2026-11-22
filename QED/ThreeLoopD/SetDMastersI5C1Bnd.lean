/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1Bas

/-!
# Set (d), master `I₅`: the polylogarithm arguments of the primitive lie in `(-1, 1)`

For `0 < ξ < 1` and `0 < x < 1 - ξ`, each dilogarithm and trilogarithm argument of the primitive
`QED.ThreeLoopD.i5C1PB` has absolute value `< 1` (`QED.ThreeLoopD.i5C1E_b9`, ...). These are the
bounds used for the derivatives in `QED.ThreeLoopD.SetDMastersI5C1Bas` and
`QED.ThreeLoopD.SetDMastersI5C1Tri`, stated separately for the endpoint limits of the primitive.

## Main results

* `QED.ThreeLoopD.i5C1E_b9`, ..., `QED.ThreeLoopD.i5C1E_b53`.
-/

@[expose] public section

open Set Real

namespace QED.ThreeLoopD

/-- `|Li₂ argument 9| < 1` on `(0, 1 - ξ)` (from `i5C1B_d0`). -/
theorem i5C1E_b9 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |x| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |x| < 1 := by
    rw [abs_of_pos (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ) + (by positivity : (0 : ℝ) < (1 - ξ - x))
  exact hlt

/-- `|Li₂ argument 10| < 1` on `(0, 1 - ξ)` (from `i5C1B_d1`). -/
theorem i5C1E_b10 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |x / (1 - ξ)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |x / (1 - ξ)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < (1 - ξ - x))
  exact hlt

/-- `|Li₂ argument 11| < 1` on `(0, 1 - ξ)` (from `i5C1B_d2`). -/
theorem i5C1E_b11 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |ξ / (1 - x)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |ξ / (1 - x)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < (1 - ξ - x))
  exact hlt

/-- `|Li₂ argument 12| < 1` on `(0, 1 - ξ)` (from `i5C1B_d3`). -/
theorem i5C1E_b12 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |ξ * (1 - x)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |ξ * (1 - x)| < 1 := by
    rw [abs_of_pos (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x)) + (by positivity : (0 : ℝ) < x ^ 2) + 2 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x)) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  exact hlt

/-- `|Li₂ argument 13| < 1` on `(0, 1 - ξ)` (from `i5C1B_d4`). -/
theorem i5C1E_b13 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |-(ξ * x / (1 - ξ))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |-(ξ * x / (1 - ξ))| < 1 := by
    rw [abs_neg, abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < x ^ 2) + 2 * (by positivity : (0 : ℝ) < x * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  exact hlt

/-- `|Li₂ argument 14| < 1` on `(0, 1 - ξ)` (from `i5C1B_d5`). -/
theorem i5C1E_b14 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |x / (ξ * x + (1 - ξ))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |x / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x)) + (by positivity : (0 : ℝ) < x * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  exact hlt

/-- `|Li₂ argument 15| < 1` on `(0, 1 - ξ)` (from `i5C1B_d6`). -/
theorem i5C1E_b15 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |-(ξ * x ^ 2 / (1 - ξ) ^ 2)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |-(ξ * x ^ 2 / (1 - ξ) ^ 2)| < 1 := by
    rw [abs_neg, abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < ξ * (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < x ^ 3) + 3 *
        (by positivity : (0 : ℝ) < x ^ 2 * (1 - ξ - x)) + 3 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 3)
  exact hlt

/-- `|Li₂ argument 16| < 1` on `(0, 1 - ξ)` (from `i5C1B_d7`). -/
theorem i5C1E_b16 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |ξ * (1 - ξ - x) / (1 - ξ)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |ξ * (1 - ξ - x) / (1 - ξ)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < x ^ 2) + 2 *
        (by positivity : (0 : ℝ) < x * (1 - ξ - x)) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  exact hlt

/-- `|Li₂ argument 17| < 1` on `(0, 1 - ξ)` (from `i5C1B_d8`). -/
theorem i5C1E_b17 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |(1 + ξ) * x / (ξ * x + (1 - ξ))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |(1 + ξ) * x / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < (1 - ξ - x))
  exact hlt

/-- `|Li₂ argument 18| < 1` on `(0, 1 - ξ)` (from `i5C1B_d9`). -/
theorem i5C1E_b18 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |x / (ξ * x + (1 - ξ) ^ 2)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |x / (ξ * x + (1 - ξ) ^ 2)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < x * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  exact hlt

/-- `|Li₂ argument 19| < 1` on `(0, 1 - ξ)` (from `i5C1B_d10`). -/
theorem i5C1E_b19 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |ξ * (1 - ξ) / (ξ * x + (1 - ξ))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |ξ * (1 - ξ) / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < x ^ 2) + 2 *
        (by positivity : (0 : ℝ) < x * (1 - ξ - x)) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  exact hlt

/-- `|Li₂ argument 20| < 1` on `(0, 1 - ξ)` (from `i5C1B_d11`). -/
theorem i5C1E_b20 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))| < 1 := by
    rw [abs_neg, abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < x ^ 2) +
        2 * (by positivity : (0 : ℝ) < x * (1 - ξ - x)) + (by positivity : (0 : ℝ) <
        (1 - ξ - x) ^ 2)
  exact hlt

/-- `|Li₂ argument 21| < 1` on `(0, 1 - ξ)` (from `i5C1B_d12`). -/
theorem i5C1E_b21 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)| < 1 := by
    rw [abs_neg, abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 4 * (by positivity : (0 : ℝ) < ξ ^ 2 * x ^ 2) + 4 *
        (by positivity : (0 : ℝ) < ξ ^ 2 * x * (1 - ξ - x)) + 4 *
        (by positivity : (0 : ℝ) < ξ * x ^ 3) + 10 * (by positivity : (0 : ℝ) < ξ * x ^ 2 *
        (1 - ξ - x)) + 7 * (by positivity : (0 : ℝ) < ξ * x * (1 - ξ - x) ^ 2) +
        (by positivity : (0 : ℝ) < ξ * (1 - ξ - x) ^ 3) + (by positivity : (0 : ℝ) < x ^ 4) + 4 *
        (by positivity : (0 : ℝ) < x ^ 3 * (1 - ξ - x)) + 6 * (by positivity : (0 : ℝ) < x ^ 2 *
        (1 - ξ - x) ^ 2) + 4 * (by positivity : (0 : ℝ) < x * (1 - ξ - x) ^ 3) +
        (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 4)
  exact hlt

/-- `|Li₃ argument 22| < 1` on `(0, 1 - ξ)` (from `i5C1T_d0`). -/
theorem i5C1E_b22 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |(1 - x)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |(1 - x)| < 1 := by
    rw [abs_of_pos (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < x)
  exact hlt

/-- `|Li₃ argument 23| < 1` on `(0, 1 - ξ)` (from `i5C1T_d1`). -/
theorem i5C1E_b23 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |x / (1 - ξ)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |x / (1 - ξ)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < (1 - ξ - x))
  exact hlt

/-- `|Li₃ argument 24| < 1` on `(0, 1 - ξ)` (from `i5C1T_d2`). -/
theorem i5C1E_b24 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |ξ / (1 - x)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |ξ / (1 - x)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < (1 - ξ - x))
  exact hlt

/-- `|Li₃ argument 25| < 1` on `(0, 1 - ξ)` (from `i5C1T_d3`). -/
theorem i5C1E_b25 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |ξ * (1 - x)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |ξ * (1 - x)| < 1 := by
    rw [abs_of_pos (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x)) + (by positivity : (0 : ℝ) < x ^ 2) + 2 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x)) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  exact hlt

/-- `|Li₃ argument 26| < 1` on `(0, 1 - ξ)` (from `i5C1T_d4`). -/
theorem i5C1E_b26 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |-(ξ * x / (1 - ξ))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |-(ξ * x / (1 - ξ))| < 1 := by
    rw [abs_neg, abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < x ^ 2) + 2 * (by positivity : (0 : ℝ) < x * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  exact hlt

/-- `|Li₃ argument 27| < 1` on `(0, 1 - ξ)` (from `i5C1T_d5`). -/
theorem i5C1E_b27 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |(ξ * x + (1 - ξ))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |(ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ ^ 2) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x))
  exact hlt

/-- `|Li₃ argument 28| < 1` on `(0, 1 - ξ)` (from `i5C1T_d6`). -/
theorem i5C1E_b28 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |(1 - ξ - x) / (1 - x)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |(1 - ξ - x) / (1 - x)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ)
  exact hlt

/-- `|Li₃ argument 29| < 1` on `(0, 1 - ξ)` (from `i5C1T_d7`). -/
theorem i5C1E_b29 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |-(ξ * x ^ 2 / (1 - ξ) ^ 2)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |-(ξ * x ^ 2 / (1 - ξ) ^ 2)| < 1 := by
    rw [abs_neg, abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < ξ * (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < x ^ 3) + 3 *
        (by positivity : (0 : ℝ) < x ^ 2 * (1 - ξ - x)) + 3 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 3)
  exact hlt

/-- `|Li₃ argument 30| < 1` on `(0, 1 - ξ)` (from `i5C1T_d8`). -/
theorem i5C1E_b30 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |(1 - ξ - x) / (1 - ξ)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |(1 - ξ - x) / (1 - ξ)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < x)
  exact hlt

/-- `|Li₃ argument 31| < 1` on `(0, 1 - ξ)` (from `i5C1T_d9`). -/
theorem i5C1E_b31 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |ξ * (1 - ξ - x) / (1 - ξ)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |ξ * (1 - ξ - x) / (1 - ξ)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < x ^ 2) + 2 *
        (by positivity : (0 : ℝ) < x * (1 - ξ - x)) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  exact hlt

/-- `|Li₃ argument 32| < 1` on `(0, 1 - ξ)` (from `i5C1T_d10`). -/
theorem i5C1E_b32 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |(1 + ξ) * x / (ξ * x + (1 - ξ))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |(1 + ξ) * x / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < (1 - ξ - x))
  exact hlt

/-- `|Li₃ argument 33| < 1` on `(0, 1 - ξ)` (from `i5C1T_d11`). -/
theorem i5C1E_b33 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |ξ * (1 - ξ) / (ξ * x + (1 - ξ))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |ξ * (1 - ξ) / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < x ^ 2) + 2 *
        (by positivity : (0 : ℝ) < x * (1 - ξ - x)) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  exact hlt

/-- `|Li₃ argument 34| < 1` on `(0, 1 - ξ)` (from `i5C1T_d12`). -/
theorem i5C1E_b34 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |(1 - ξ - x) / (ξ * x + (1 - ξ))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |(1 - ξ - x) / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < x ^ 2) +
        (by positivity : (0 : ℝ) < x * (1 - ξ - x))
  exact hlt

/-- `|Li₃ argument 35| < 1` on `(0, 1 - ξ)` (from `i5C1T_d13`). -/
theorem i5C1E_b35 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))| < 1 := by
    rw [abs_neg, abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < x ^ 2) +
        2 * (by positivity : (0 : ℝ) < x * (1 - ξ - x)) + (by positivity : (0 : ℝ) <
        (1 - ξ - x) ^ 2)
  exact hlt

/-- `|Li₃ argument 36| < 1` on `(0, 1 - ξ)` (from `i5C1T_d14`). -/
theorem i5C1E_b36 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |(1 - ξ) * (1 - x) / (ξ * x + (1 - ξ))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |(1 - ξ) * (1 - x) / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < x)
  exact hlt

/-- `|Li₃ argument 37| < 1` on `(0, 1 - ξ)` (from `i5C1T_d15`). -/
theorem i5C1E_b37 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |(ξ * x + (1 - ξ) ^ 2) / (1 - ξ)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |(ξ * x + (1 - ξ) ^ 2) / (1 - ξ)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * (1 - ξ - x))
  exact hlt

/-- `|Li₃ argument 38| < 1` on `(0, 1 - ξ)` (from `i5C1T_d16`). -/
theorem i5C1E_b38 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |(ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |(ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x))
  exact hlt

/-- `|Li₃ argument 39| < 1` on `(0, 1 - ξ)` (from `i5C1T_d17`). -/
theorem i5C1E_b39 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |(ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ) ^ 2)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |(ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ) ^ 2)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ ^ 2 * x) + (by positivity : (0 : ℝ) < ξ * x *
        (1 - ξ - x))
  exact hlt

/-- `|Li₃ argument 40| < 1` on `(0, 1 - ξ)` (from `i5C1T_d18`). -/
theorem i5C1E_b40 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |ξ * x / (ξ * x + (1 - ξ))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |ξ * x / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < x) + (by positivity : (0 : ℝ) < (1 - ξ - x))
  exact hlt

/-- `|Li₃ argument 41| < 1` on `(0, 1 - ξ)` (from `i5C1T_d19`). -/
theorem i5C1E_b41 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |ξ * (1 - ξ - x) / ((1 - ξ) * (1 + ξ))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |ξ * (1 - ξ - x) / ((1 - ξ) * (1 + ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x)) + (by positivity : (0 : ℝ) < x ^ 2) + 2 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x)) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  exact hlt

/-- `|Li₃ argument 42| < 1` on `(0, 1 - ξ)` (from `i5C1T_d20`). -/
theorem i5C1E_b42 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |ξ ^ 2 * (1 - ξ - x) / (ξ * x + (1 - ξ))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |ξ ^ 2 * (1 - ξ - x) / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ ^ 2 * x) + 3 *
        (by positivity : (0 : ℝ) < ξ * x ^ 2) + 5 * (by positivity : (0 : ℝ) < ξ * x *
        (1 - ξ - x)) + 2 * (by positivity : (0 : ℝ) < ξ * (1 - ξ - x) ^ 2) +
        (by positivity : (0 : ℝ) < x ^ 3) + 3 * (by positivity : (0 : ℝ) < x ^ 2 * (1 - ξ - x)) +
        3 * (by positivity : (0 : ℝ) < x * (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) <
        (1 - ξ - x) ^ 3)
  exact hlt

/-- `|Li₃ argument 43| < 1` on `(0, 1 - ξ)` (from `i5C1T_d21`). -/
theorem i5C1E_b43 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |ξ * x ^ 2 / (ξ * x ^ 2 + (1 - ξ) ^ 2)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |ξ * x ^ 2 / (ξ * x ^ 2 + (1 - ξ) ^ 2)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < x ^ 2) + 2 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x)) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  exact hlt

/-- `|Li₃ argument 44| < 1` on `(0, 1 - ξ)` (from `i5C1T_d22`). -/
theorem i5C1E_b44 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |(1 - ξ) ^ 2 / (ξ * x + (1 - ξ) ^ 2)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |(1 - ξ) ^ 2 / (ξ * x + (1 - ξ) ^ 2)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * x)
  exact hlt

/-- `|Li₃ argument 45| < 1` on `(0, 1 - ξ)` (from `i5C1T_d23`). -/
theorem i5C1E_b45 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |(1 - ξ - x) / ((1 - ξ) * (1 + ξ) * (1 - x))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |(1 - ξ - x) / ((1 - ξ) * (1 + ξ) * (1 - x))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ ^ 2 * x) +
        (by positivity : (0 : ℝ) < ξ ^ 2 * (1 - ξ - x)) + (by positivity : (0 : ℝ) < ξ * x ^ 2) +
        2 * (by positivity : (0 : ℝ) < ξ * x * (1 - ξ - x)) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x) ^ 2)
  exact hlt

/-- `|Li₃ argument 46| < 1` on `(0, 1 - ξ)` (from `i5C1T_d24`). -/
theorem i5C1E_b46 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ)))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ)))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x ^ 2) + 2 *
        (by positivity : (0 : ℝ) < ξ * x * (1 - ξ - x)) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < x ^ 3) + 3 *
        (by positivity : (0 : ℝ) < x ^ 2 * (1 - ξ - x)) + 3 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 3)
  exact hlt

/-- `|Li₃ argument 47| < 1` on `(0, 1 - ξ)` (from `i5C1T_d25`). -/
theorem i5C1E_b47 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < (1 - ξ - x))
  exact hlt

/-- `|Li₃ argument 48| < 1` on `(0, 1 - ξ)` (from `i5C1T_d26`). -/
theorem i5C1E_b48 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < x * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  exact hlt

/-- `|Li₃ argument 49| < 1` on `(0, 1 - ξ)` (from `i5C1T_d27`). -/
theorem i5C1E_b49 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |-(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |-(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))| < 1 := by
    rw [abs_neg, abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x ^ 2) +
        (by positivity : (0 : ℝ) < ξ * x * (1 - ξ - x)) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < x ^ 3) + 3 *
        (by positivity : (0 : ℝ) < x ^ 2 * (1 - ξ - x)) + 3 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 3)
  exact hlt

/-- `|Li₃ argument 50| < 1` on `(0, 1 - ξ)` (from `i5C1T_d28`). -/
theorem i5C1E_b50 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |(1 - ξ) ^ 2 * (1 - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |(1 - ξ) ^ 2 * (1 - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * x ^ 2) + (by positivity : (0 : ℝ) < x ^ 3) +
        2 * (by positivity : (0 : ℝ) < x ^ 2 * (1 - ξ - x)) + (by positivity : (0 : ℝ) < x *
        (1 - ξ - x) ^ 2)
  exact hlt

/-- `|Li₃ argument 51| < 1` on `(0, 1 - ξ)` (from `i5C1T_d29`). -/
theorem i5C1E_b51 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |(1 + ξ) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |(1 + ξ) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ ^ 2 * (1 - ξ - x))
  exact hlt

/-- `|Li₃ argument 52| < 1` on `(0, 1 - ξ)` (from `i5C1T_d30`). -/
theorem i5C1E_b52 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |ξ * (ξ * x ^ 2 + (1 - ξ) ^ 2) / ((1 - ξ) * (ξ * x + (1 - ξ)) * (1 - x))| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |ξ * (ξ * x ^ 2 + (1 - ξ) ^ 2) / ((1 - ξ) * (ξ * x + (1 - ξ)) * (1 - x))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * x * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < x ^ 2 * (1 - ξ - x)) + 2 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 3)
  exact hlt

/-- `|Li₃ argument 53| < 1` on `(0, 1 - ξ)` (from `i5C1T_d31`). -/
theorem i5C1E_b53 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    |(ξ * x + (1 - ξ)) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x ^ 2 + (1 - ξ) ^ 2)| < 1 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hlt : |(ξ * x + (1 - ξ)) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x ^ 2 + (1 - ξ) ^ 2)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ ^ 2 * x * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < ξ ^ 2 * (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < ξ * x *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < ξ * (1 - ξ - x) ^ 3)
  exact hlt

end QED.ThreeLoopD
