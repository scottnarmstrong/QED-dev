/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Derivatives of the dilogarithm and trilogarithm

On `(-1, 1)` the power series of `Li₂` and `Li₃` may be differentiated termwise.

## Main results

* `QED.Polylog.hasDerivAt_tsum_pow_div_pow`: for `1 ≤ k` and `|x| < 1`, the derivative of
  `∑ y ^ (n + 1) / (n + 1) ^ k` is `∑ x ^ n / (n + 1) ^ (k - 1)`.
* `QED.Polylog.hasDerivAt_Li₂`: `Li₂' x = -log (1 - x) / x` for `0 < |x| < 1`, and
  `QED.Polylog.hasDerivAt_Li₂_zero`: `Li₂' 0 = 1`.
* `QED.Polylog.hasDerivAt_Li₃`: `Li₃' x = Li₂ x / x` for `0 < |x| < 1`, and
  `QED.Polylog.hasDerivAt_Li₃_zero`: `Li₃' 0 = 1`.
* `QED.Polylog.mul_deriv_Li₂`, `QED.Polylog.mul_deriv_Li₃`: `x Li₂' x = -log (1 - x)` and
  `x Li₃' x = Li₂ x` on `(-1, 1)`.
-/

public section

open Real Set

namespace QED.Polylog

/-- Termwise differentiation of the polylogarithm series: for `1 ≤ k` and `|x| < 1`, the
derivative of `y ↦ ∑ y ^ (n + 1) / (n + 1) ^ k` at `x` is `∑ x ^ n / (n + 1) ^ (k - 1)`. -/
theorem hasDerivAt_tsum_pow_div_pow {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (fun y : ℝ => ∑' n : ℕ, y ^ (n + 1) / ((n : ℝ) + 1) ^ k)
      (∑' n : ℕ, x ^ n / ((n : ℝ) + 1) ^ (k - 1)) x := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set r : ℝ := (|x| + 1) / 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr]; linarith
  have hxr : |x| < r := by rw [hr]; linarith
  refine hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ => r ^ n) (t := Ioo (-r) r)
    (g := fun (n : ℕ) (y : ℝ) => y ^ (n + 1) / ((n : ℝ) + 1) ^ (j + 1))
    (g' := fun (n : ℕ) (y : ℝ) => y ^ n / ((n : ℝ) + 1) ^ j)
    (y₀ := 0) (summable_geometric_of_lt_one hr0 hr1) isOpen_Ioo isPreconnected_Ioo ?_ ?_
    ⟨by linarith [abs_nonneg x], by linarith [abs_nonneg x]⟩ ?_ (abs_lt.mp hxr)
  · intro n y _
    have h := (hasDerivAt_pow (n + 1) y).div_const (((n : ℝ) + 1) ^ (j + 1))
    convert h using 1
    have : ((n : ℝ) + 1) ^ j ≠ 0 := by positivity
    push_cast
    rw [pow_succ ((n : ℝ) + 1) j]
    field_simp
  · intro n y hy
    have hy' : |y| ≤ r := (abs_lt.mpr hy).le
    rw [Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ j)]
    calc |y| ^ n / ((n : ℝ) + 1) ^ j ≤ |y| ^ n :=
          div_le_self (by positivity) (one_le_pow₀ (by linarith [n.cast_nonneg (α := ℝ)]))
      _ ≤ r ^ n := pow_le_pow_left₀ (abs_nonneg y) hy' n
  · simp

/-- `Li₂` has derivative `∑ x ^ n / (n + 1)` at every `x` with `|x| < 1`. -/
theorem hasDerivAt_Li₂_tsum {x : ℝ} (hx : |x| < 1) :
    HasDerivAt Li₂ (∑' n : ℕ, x ^ n / ((n : ℝ) + 1)) x := by
  have h : Li₂ = fun y : ℝ => ∑' n : ℕ, y ^ (n + 1) / ((n : ℝ) + 1) ^ 2 := rfl
  rw [h]
  simpa using hasDerivAt_tsum_pow_div_pow (k := 2) (by norm_num) hx

/-- `Li₃` has derivative `∑ x ^ n / (n + 1) ^ 2` at every `x` with `|x| < 1`. -/
theorem hasDerivAt_Li₃_tsum {x : ℝ} (hx : |x| < 1) :
    HasDerivAt Li₃ (∑' n : ℕ, x ^ n / ((n : ℝ) + 1) ^ 2) x := by
  have h : Li₃ = fun y : ℝ => ∑' n : ℕ, y ^ (n + 1) / ((n : ℝ) + 1) ^ 3 := rfl
  rw [h]
  exact hasDerivAt_tsum_pow_div_pow (k := 3) (by norm_num) hx

/-- `x ∑ x ^ n / (n + 1) = -log (1 - x)` for `|x| < 1`. -/
theorem mul_tsum_pow_div_eq_neg_log {x : ℝ} (hx : |x| < 1) :
    x * ∑' n : ℕ, x ^ n / ((n : ℝ) + 1) = -log (1 - x) := by
  rw [← (Real.hasSum_pow_div_log_of_abs_lt_one hx).tsum_eq, ← tsum_mul_left]
  congr 1
  funext n
  ring

/-- `x ∑ x ^ n / (n + 1) ^ 2 = Li₂ x`. -/
theorem mul_tsum_pow_div_sq_eq_Li₂ (x : ℝ) :
    x * ∑' n : ℕ, x ^ n / ((n : ℝ) + 1) ^ 2 = Li₂ x := by
  rw [Li₂, ← tsum_mul_left]
  congr 1
  funext n
  ring

/-- The derivative of the dilogarithm: `Li₂' x = -log (1 - x) / x` for `0 < |x| < 1`. -/
theorem hasDerivAt_Li₂ {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) :
    HasDerivAt Li₂ (-log (1 - x) / x) x := by
  convert hasDerivAt_Li₂_tsum hx using 1
  rw [← mul_tsum_pow_div_eq_neg_log hx]
  field_simp

/-- The derivative of the dilogarithm at `0` is `1`. -/
theorem hasDerivAt_Li₂_zero : HasDerivAt Li₂ 1 0 := by
  convert hasDerivAt_Li₂_tsum (x := 0) (by norm_num) using 1
  rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
  simp

/-- `x Li₂' x = -log (1 - x)` for `|x| < 1`. -/
theorem mul_deriv_Li₂ {x : ℝ} (hx : |x| < 1) : x * deriv Li₂ x = -log (1 - x) := by
  rw [(hasDerivAt_Li₂_tsum hx).deriv, mul_tsum_pow_div_eq_neg_log hx]

/-- The derivative of the trilogarithm: `Li₃' x = Li₂ x / x` for `0 < |x| < 1`. -/
theorem hasDerivAt_Li₃ {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) :
    HasDerivAt Li₃ (Li₂ x / x) x := by
  convert hasDerivAt_Li₃_tsum hx using 1
  rw [← mul_tsum_pow_div_sq_eq_Li₂ x]
  field_simp

/-- The derivative of the trilogarithm at `0` is `1`. -/
theorem hasDerivAt_Li₃_zero : HasDerivAt Li₃ 1 0 := by
  convert hasDerivAt_Li₃_tsum (x := 0) (by norm_num) using 1
  rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
  simp

/-- `x Li₃' x = Li₂ x` for `|x| < 1`. -/
theorem mul_deriv_Li₃ {x : ℝ} (hx : |x| < 1) : x * deriv Li₃ x = Li₂ x := by
  rw [(hasDerivAt_Li₃_tsum hx).deriv, mul_tsum_pow_div_sq_eq_Li₂]

end QED.Polylog
