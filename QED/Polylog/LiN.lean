/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import QED.Polylog.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The polylogarithms `Li k` on `[-1, 1]`

The real polylogarithm of integer order `k`, defined by its power series
`Li k x = ∑_{n ≥ 1} x ^ n / n ^ k`. The series converges absolutely for `|x| < 1` (every `k`)
and for `|x| ≤ 1` when `2 ≤ k`; elsewhere the `tsum` is `0`.

## Main results

* `QED.Polylog.summable_Li`, `QED.Polylog.summable_Li_of_abs_lt_one`: convergence.
* `QED.Polylog.Li_two`, `QED.Polylog.Li_three`: `Li 2 = Li₂` and `Li 3 = Li₃`.
* `QED.Polylog.Li_one`: `Li 1 x = -log (1 - x)` for `|x| < 1`.
* `QED.Polylog.riemannZeta_natCast_eq_Li_one`, `QED.Polylog.riemannZeta_natCast_re`:
  `ζ(k) = Li k 1` for `2 ≤ k`.
* `QED.Polylog.Li_add_Li_neg`, `QED.Polylog.Li_add_Li_neg_zpow`: the duplication formula
  `Li k x + Li k (-x) = 2 ^ (1 - k) Li k (x ^ 2)` for `2 ≤ k`, `|x| ≤ 1`.
* `QED.Polylog.hasDerivAt_Li`, `QED.Polylog.mul_deriv_Li`: `x Li k' x = Li (k - 1) x` on
  `(-1, 1)` for `1 ≤ k`.
-/

@[expose] public section

open Real

namespace QED.Polylog

/-- The real polylogarithm `Li k x = ∑_{n ≥ 1} x ^ n / n ^ k`. The series converges for
`|x| < 1`, and for `|x| ≤ 1` when `2 ≤ k`; elsewhere this `tsum` is `0`. -/
noncomputable def Li (k : ℕ) (x : ℝ) : ℝ := ∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ k

/-- The polylogarithm series converges for `2 ≤ k` and `|x| ≤ 1`. -/
theorem summable_Li {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : |x| ≤ 1) :
    Summable fun n : ℕ => x ^ (n + 1) / ((n : ℝ) + 1) ^ k :=
  summable_pow_div_pow hk hx

/-- The polylogarithm series converges for every `k` when `|x| < 1`. -/
theorem summable_Li_of_abs_lt_one (k : ℕ) {x : ℝ} (hx : |x| < 1) :
    Summable fun n : ℕ => x ^ (n + 1) / ((n : ℝ) + 1) ^ k := by
  refine .of_norm_bounded ((summable_geometric_of_lt_one (abs_nonneg x) hx).mul_left |x|)
    fun n => ?_
  have hp : (0 : ℝ) < ((n : ℝ) + 1) ^ k := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hp, ← pow_succ']
  exact div_le_self (pow_nonneg (abs_nonneg x) _)
    (one_le_pow₀ (by linarith [n.cast_nonneg (α := ℝ)]))

/-- The series of `Li k x` has sum `Li k x` for `2 ≤ k`, `|x| ≤ 1`. -/
theorem hasSum_Li {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun n : ℕ => x ^ (n + 1) / ((n : ℝ) + 1) ^ k) (Li k x) :=
  (summable_Li hk hx).hasSum

/-- The series of `Li k x` has sum `Li k x` for `|x| < 1`. -/
theorem hasSum_Li_of_abs_lt_one (k : ℕ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => x ^ (n + 1) / ((n : ℝ) + 1) ^ k) (Li k x) :=
  (summable_Li_of_abs_lt_one k hx).hasSum

/-- `Li 2` is the dilogarithm `Li₂`. -/
theorem Li_two : Li 2 = Li₂ := rfl

/-- `Li 3` is the trilogarithm `Li₃`. -/
theorem Li_three : Li 3 = Li₃ := rfl

/-- `Li k 0 = 0`. -/
@[simp] theorem Li_zero (k : ℕ) : Li k 0 = 0 := by simp [Li]

/-- `Li 1 x = -log (1 - x)` for `|x| < 1`. -/
theorem Li_one {x : ℝ} (hx : |x| < 1) : Li 1 x = -log (1 - x) := by
  rw [← (Real.hasSum_pow_div_log_of_abs_lt_one hx).tsum_eq, Li]
  simp only [pow_one]

/-- `Li k 1 = ∑_{n ≥ 1} 1 / n ^ k`. -/
theorem Li_at_one (k : ℕ) : Li k 1 = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ k := by
  simp [Li]

/-- `ζ(k) = Li k 1` for `2 ≤ k`. -/
theorem riemannZeta_natCast_eq_Li_one {k : ℕ} (hk : 2 ≤ k) :
    riemannZeta k = (Li k 1 : ℂ) := by
  have hre : 1 < ((k : ℂ)).re := by
    rw [Complex.natCast_re]; exact_mod_cast hk
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre, Li_at_one, Complex.ofReal_tsum]
  congr 1
  funext n
  rw [Complex.cpow_natCast]
  push_cast
  rfl

/-- `Li k 1` is the real part of `ζ(k)` for `2 ≤ k`. -/
theorem riemannZeta_natCast_re {k : ℕ} (hk : 2 ≤ k) : (riemannZeta k).re = Li k 1 := by
  rw [riemannZeta_natCast_eq_Li_one hk, Complex.ofReal_re]

/-- `Li 3 1 = zeta3`. -/
theorem Li_three_one : Li 3 1 = zeta3 := Li₃_one

/-- `Li k` is continuous on `[-1, 1]` for `2 ≤ k`. -/
theorem continuousOn_Li {k : ℕ} (hk : 2 ≤ k) : ContinuousOn (Li k) (Set.Icc (-1) 1) :=
  continuousOn_tsum_pow_div_pow hk

/-- The duplication formula `Li k x + Li k (-x) = (2 / 2 ^ k) Li k (x ^ 2)` for `2 ≤ k`,
`|x| ≤ 1`. -/
theorem Li_add_Li_neg {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : |x| ≤ 1) :
    Li k x + Li k (-x) = 2 / 2 ^ k * Li k (x ^ 2) :=
  tsum_pow_div_pow_add_tsum_neg hk hx

/-- The duplication formula `Li k x + Li k (-x) = 2 ^ (1 - k) Li k (x ^ 2)` for `2 ≤ k`,
`|x| ≤ 1`, with an integer exponent. -/
theorem Li_add_Li_neg_zpow {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : |x| ≤ 1) :
    Li k x + Li k (-x) = (2 : ℝ) ^ (1 - (k : ℤ)) * Li k (x ^ 2) := by
  rw [Li_add_Li_neg hk hx, zpow_sub₀ (by norm_num), zpow_one, zpow_natCast]

/-- `x ∑ x ^ n / (n + 1) ^ j = Li j x`. -/
theorem mul_tsum_pow_div_eq_Li (j : ℕ) (x : ℝ) :
    x * ∑' n : ℕ, x ^ n / ((n : ℝ) + 1) ^ j = Li j x := by
  rw [Li, ← tsum_mul_left]
  congr 1
  funext n
  ring

/-- `Li k` has derivative `∑ x ^ n / (n + 1) ^ (k - 1)` at every `x` with `|x| < 1`, for
`1 ≤ k`. -/
theorem hasDerivAt_Li_tsum {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (Li k) (∑' n : ℕ, x ^ n / ((n : ℝ) + 1) ^ (k - 1)) x :=
  hasDerivAt_tsum_pow_div_pow hk hx

/-- The derivative of the polylogarithm: `Li k' x = Li (k - 1) x / x` for `1 ≤ k` and
`0 < |x| < 1`. -/
theorem hasDerivAt_Li {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) :
    HasDerivAt (Li k) (Li (k - 1) x / x) x := by
  convert hasDerivAt_Li_tsum hk hx using 1
  rw [← mul_tsum_pow_div_eq_Li]
  field_simp

/-- `x Li k' x = Li (k - 1) x` for `1 ≤ k` and `|x| < 1`. -/
theorem mul_deriv_Li {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : |x| < 1) :
    x * deriv (Li k) x = Li (k - 1) x := by
  rw [(hasDerivAt_Li_tsum hk hx).deriv, mul_tsum_pow_div_eq_Li]

end QED.Polylog
