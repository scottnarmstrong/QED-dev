/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Numerical enclosures for the two-loop constant A₁⁽⁴⁾

Rigorous rational enclosures of the three transcendental ingredients of the constant (U₁)
`A₁⁽⁴⁾ = 197/144 + π²/12 - (π²/2) ln 2 + (3/4) ζ(3)` of packet T2 (decision D-39).

* `ζ(3) = ∑_{n ≥ 0} (n+1)⁻³`: the first `N` terms plus the telescoping tail bounds
  `½/((N+1)(N+2)) ≤ ∑_{m > N} m⁻³ ≤ ½/(N(N+1))`, from
  `1/(m(m+1)(m+2)) ≤ m⁻³ ≤ 1/((m-1)m(m+1))`. With `N = 40` this gives
  `QED.TwoLoop.Numerics.zeta_three_gt` and `QED.TwoLoop.Numerics.zeta_three_lt`:
  `1.202042 < ζ(3) < 1.202057`.
* `π²/12 - (π²/2) ln 2`: from Mathlib's six-digit bounds on `π` and nine-digit bounds on
  `ln 2` (`QED.TwoLoop.Numerics.pi_sq_log_two_gt` and `QED.TwoLoop.Numerics.pi_sq_log_two_lt`).
-/

public section

open Finset

namespace QED.TwoLoop.Numerics

/-- The series `∑ (n+1)⁻³` defining `ζ(3)` is summable. -/
theorem summable_one_div_add_one_pow_three :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 3) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3))
  exact_mod_cast h

/-- The telescoping upper comparison `(x+1)⁻³ ≤ 1/(x(x+1)(x+2))` for `x > 0`. -/
theorem one_div_add_one_pow_three_le {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ^ 3 ≤ 1 / 2 / (x * (x + 1)) - 1 / 2 / ((x + 1) * (x + 1 + 1)) := by
  rw [show 1 / 2 / (x * (x + 1)) - 1 / 2 / ((x + 1) * (x + 1 + 1)) =
      1 / (x * (x + 1) * (x + 2)) by field_simp; ring]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- The telescoping lower comparison `1/((x+1)(x+2)(x+3)) ≤ (x+1)⁻³` for `x ≥ 0`. -/
theorem le_one_div_add_one_pow_three {x : ℝ} (hx : 0 ≤ x) :
    1 / 2 / ((x + 1) * (x + 2)) - 1 / 2 / ((x + 1 + 1) * (x + 1 + 2)) ≤ 1 / (x + 1) ^ 3 := by
  rw [show 1 / 2 / ((x + 1) * (x + 2)) - 1 / 2 / ((x + 1 + 1) * (x + 1 + 2)) =
      1 / ((x + 1) * (x + 2) * (x + 3)) by field_simp; ring]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [sq_nonneg x]

/-- Upper bound for a partial sum of the tail `∑_{m > N} m⁻³`, for `N ≥ 1`. -/
theorem sum_range_tail_le (N : ℕ) (hN : 1 ≤ N) (K : ℕ) :
    ∑ i ∈ range K, 1 / ((i : ℝ) + N + 1) ^ 3 ≤
      1 / 2 / ((N : ℝ) * (N + 1)) - 1 / 2 / (((N : ℝ) + K) * ((N : ℝ) + K + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have key := one_div_add_one_pow_three_le (x := (N : ℝ) + K) (by positivity)
    rw [sum_range_succ]
    push_cast
    rw [show (K : ℝ) + N + 1 = N + K + 1 by ring, show (N : ℝ) + (K + 1) = N + K + 1 by ring]
    linarith

/-- Lower bound for a partial sum of the tail `∑_{m > N} m⁻³`. -/
theorem sum_range_tail_ge (N K : ℕ) :
    1 / 2 / (((N : ℝ) + 1) * (N + 2)) - 1 / 2 / (((N : ℝ) + K + 1) * ((N : ℝ) + K + 2)) ≤
      ∑ i ∈ range K, 1 / ((i : ℝ) + N + 1) ^ 3 := by
  induction K with
  | zero => simp
  | succ K ih =>
    have key := le_one_div_add_one_pow_three (x := (N : ℝ) + K) (by positivity)
    rw [sum_range_succ]
    push_cast
    rw [show (K : ℝ) + N + 1 = N + K + 1 by ring, show (N : ℝ) + (K + 1) = N + K + 1 by ring]
    linarith

/-- The tail `∑_{m > N} m⁻³` is summable. -/
theorem summable_tail (N : ℕ) : Summable (fun i : ℕ => 1 / ((i : ℝ) + N + 1) ^ 3) := by
  have h := (summable_nat_add_iff N).mpr summable_one_div_add_one_pow_three
  exact_mod_cast h

/-- `ζ(3)` is the sum of its first `N` terms and the tail `∑_{m > N} m⁻³`. -/
theorem tsum_eq_sum_add_tsum_tail (N : ℕ) :
    ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3 =
      ∑ i ∈ range N, 1 / ((i : ℝ) + 1) ^ 3 + ∑' i : ℕ, 1 / ((i : ℝ) + N + 1) ^ 3 := by
  rw [← summable_one_div_add_one_pow_three.sum_add_tsum_nat_add N]
  push_cast
  rfl

/-- The tail bound `∑_{m > N} m⁻³ ≤ ½/(N(N+1))` for `N ≥ 1`. -/
theorem tsum_tail_le (N : ℕ) (hN : 1 ≤ N) :
    ∑' i : ℕ, 1 / ((i : ℝ) + N + 1) ^ 3 ≤ 1 / 2 / ((N : ℝ) * (N + 1)) := by
  refine Real.tsum_le_of_sum_range_le (fun _ => by positivity) fun K => ?_
  have h := sum_range_tail_le N hN K
  have h0 : 0 ≤ 1 / 2 / (((N : ℝ) + K) * ((N : ℝ) + K + 1)) := by positivity
  linarith

/-- The tail bound `½/((N+1)(N+2)) - ½/((N+K+1)(N+K+2)) ≤ ∑_{m > N} m⁻³`, for every `K`. -/
theorem le_tsum_tail (N K : ℕ) :
    1 / 2 / (((N : ℝ) + 1) * (N + 2)) - 1 / 2 / (((N : ℝ) + K + 1) * ((N : ℝ) + K + 2)) ≤
      ∑' i : ℕ, 1 / ((i : ℝ) + N + 1) ^ 3 :=
  (sum_range_tail_ge N K).trans
    ((summable_tail N).sum_le_tsum _ fun _ _ => by positivity)

/-- Lower enclosure `1.202042 < ζ(3)` (true value `1.2020569…`). -/
theorem zeta_three_gt : (1.202042 : ℝ) < ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3 := by
  rw [tsum_eq_sum_add_tsum_tail 40]
  have h := le_tsum_tail 40 10000
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- Upper enclosure `ζ(3) < 1.202057` (true value `1.2020569…`). -/
theorem zeta_three_lt : ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3 < (1.202057 : ℝ) := by
  rw [tsum_eq_sum_add_tsum_tail 40]
  have h := tsum_tail_le 40 (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- Lower enclosure of `π²/12 - (π²/2) ln 2`, from `π < 3.141593` and `ln 2 < 0.6931471808`. -/
theorem pi_sq_log_two_gt :
    (3.141593 : ℝ) ^ 2 * (1 / 12 - 0.6931471808 / 2) <
      Real.pi ^ 2 / 12 - Real.pi ^ 2 / 2 * Real.log 2 := by
  have hp0 := Real.pi_pos
  have hp := Real.pi_lt_d6
  have hl := Real.log_two_lt_d9
  have hP : Real.pi ^ 2 < (3.141593 : ℝ) ^ 2 := by gcongr
  have hc : (1 / 12 - 0.6931471808 / 2 : ℝ) < 1 / 12 - Real.log 2 / 2 := by linarith
  have hc0 : (1 / 12 - 0.6931471808 / 2 : ℝ) < 0 := by norm_num
  nlinarith [mul_pos (pow_pos hp0 2) (sub_pos.mpr hc),
    mul_pos (neg_pos.mpr hc0) (sub_pos.mpr hP)]

/-- Upper enclosure of `π²/12 - (π²/2) ln 2`, from `3.141592 < π` and `0.6931471803 < ln 2`. -/
theorem pi_sq_log_two_lt :
    Real.pi ^ 2 / 12 - Real.pi ^ 2 / 2 * Real.log 2 <
      (3.141592 : ℝ) ^ 2 * (1 / 12 - 0.6931471803 / 2) := by
  have hp := Real.pi_gt_d6
  have hl := Real.log_two_gt_d9
  have hP : (3.141592 : ℝ) ^ 2 < Real.pi ^ 2 := by gcongr
  have hc : (1 / 12 - Real.log 2 / 2 : ℝ) < 1 / 12 - 0.6931471803 / 2 := by linarith
  have hc0 : (1 / 12 - Real.log 2 / 2 : ℝ) < 0 := by linarith [Real.log_two_gt_d9]
  nlinarith [mul_pos (by norm_num : (0 : ℝ) < 3.141592 ^ 2) (sub_pos.mpr hc),
    mul_pos (neg_pos.mpr hc0) (sub_pos.mpr hP)]

end QED.TwoLoop.Numerics

end
