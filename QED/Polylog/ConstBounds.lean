/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.LiHalf
public import QED.Polylog.Zeta5
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Certified enclosures of `log 2`, `Li 3 (1 / 2)`, `Li 4 (1 / 2)`, `ζ(3)` and `ζ(5)`

Each enclosure has width below `10⁻¹⁶`; all are proved, the arithmetic by `norm_num`.

* For `0 ≤ x < 1` the series of `Li k x` is its first `N` terms plus a tail in
  `[0, x ^ (N + 1) / ((N + 1) ^ k (1 - x))]` (`QED.Polylog.Li_mem_partial`), the tail being
  dominated termwise by a geometric series. At `x = 1 / 2` this gives `log 2 = Li 1 (1 / 2)`
  (`N = 55`), `Li 3 (1 / 2)` (`N = 45`) and `Li 4 (1 / 2)` (`N = 40`) to within `5 · 10⁻¹⁹`.
* `ζ(3)` follows from `Li 3 (1 / 2)` by Landen's closed form
  (`QED.Polylog.zeta3_eq_Li_three_one_half`), with Mathlib's twenty-digit bounds on `π`.
* `ζ(5)`: the first `40` terms plus the tail `∑_{m > 40} m⁻⁵`, enclosed by telescoping
  (midpoint Euler–Maclaurin) functions of `u = m - 1/2`,
  `z5hi u = 1/(4u⁴) - 5/(24u⁶) + 49/(192u⁸)` and `z5lo u = z5hi u - 31/(64u¹⁰)`, which satisfy
  `z5lo(k + 1/2) - z5lo(k + 3/2) ≤ (k+1)⁻⁵ ≤ z5hi(k + 1/2) - z5hi(k + 3/2)` for every natural
  `k` (the differences are rational functions whose numerators have positive coefficients).

## Main results

* `QED.Polylog.log_two_gt_d20`, `QED.Polylog.log_two_lt_d20`
* `QED.Polylog.Li_three_one_half_gt`, `QED.Polylog.Li_three_one_half_lt`
* `QED.Polylog.Li_four_one_half_gt`, `QED.Polylog.Li_four_one_half_lt`
* `QED.Polylog.zeta3_gt_d18`, `QED.Polylog.zeta3_lt_d18`
* `QED.Polylog.zeta5_gt_d17`, `QED.Polylog.zeta5_lt_d17`
-/

@[expose] public section

open Real Finset

namespace QED.Polylog

/-! ### Partial sums and geometric tails -/

/-- For `0 ≤ x < 1`, `Li k x` lies between its `N`-th partial sum and that partial sum plus
`x ^ (N + 1) / ((N + 1) ^ k (1 - x))`. -/
theorem Li_mem_partial (k N : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∑ i ∈ range N, x ^ (i + 1) / ((i : ℝ) + 1) ^ k ≤ Li k x ∧
      Li k x ≤ ∑ i ∈ range N, x ^ (i + 1) / ((i : ℝ) + 1) ^ k +
        x ^ (N + 1) / (((N : ℝ) + 1) ^ k * (1 - x)) := by
  have hax : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have hs := summable_Li_of_abs_lt_one k hax
  have hsplit := (hs.sum_add_tsum_nat_add N).symm
  have hst := (summable_nat_add_iff N).mpr hs
  have hterm : ∀ i : ℕ, x ^ (i + N + 1) / (((i + N : ℕ) : ℝ) + 1) ^ k ≤
      x ^ (N + 1) / ((N : ℝ) + 1) ^ k * x ^ i := by
    intro i
    have h1 : ((N : ℝ) + 1) ^ k ≤ (((i + N : ℕ) : ℝ) + 1) ^ k := by
      gcongr; linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
    have h2 : (0 : ℝ) < ((N : ℝ) + 1) ^ k := by positivity
    rw [show x ^ (i + N + 1) = x ^ (N + 1) * x ^ i by ring, mul_comm (x ^ (N + 1) / _),
      mul_div_assoc', mul_comm (x ^ i)]
    exact div_le_div_of_nonneg_left (by positivity) h2 h1
  have hgeom := (summable_geometric_of_lt_one hx0 hx1).mul_left (x ^ (N + 1) / ((N : ℝ) + 1) ^ k)
  have htail_le : ∑' i : ℕ, x ^ (i + N + 1) / (((i + N : ℕ) : ℝ) + 1) ^ k ≤
      x ^ (N + 1) / (((N : ℝ) + 1) ^ k * (1 - x)) := by
    refine (hst.tsum_le_tsum hterm hgeom).trans_eq ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one hx0 hx1]
    field_simp
  have htail_nn : 0 ≤ ∑' i : ℕ, x ^ (i + N + 1) / (((i + N : ℕ) : ℝ) + 1) ^ k :=
    tsum_nonneg fun i => by positivity
  unfold Li
  rw [hsplit]
  constructor <;> linarith

/-! ### `log 2`, `Li 3 (1 / 2)`, `Li 4 (1 / 2)` -/

/-- `0.69314718055994530893 < log 2` (true value `0.693147180559945309417…`). -/
theorem log_two_gt_d20 : (0.69314718055994530893 : ℝ) < log 2 := by
  have h := (Li_mem_partial 1 55 (x := 1 / 2) (by norm_num) (by norm_num)).1
  rw [Li_one_one_half] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 2 < 0.69314718055994530943` (true value `0.693147180559945309417…`). -/
theorem log_two_lt_d20 : log 2 < (0.69314718055994530943 : ℝ) := by
  have h := (Li_mem_partial 1 55 (x := 1 / 2) (by norm_num) (by norm_num)).2
  rw [Li_one_one_half] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `0.53721319360804020066 < Li 3 (1 / 2)` (true value `0.537213193608040200940…`). -/
theorem Li_three_one_half_gt : (0.53721319360804020066 : ℝ) < Li 3 (1 / 2) := by
  have h := (Li_mem_partial 3 45 (x := 1 / 2) (by norm_num) (by norm_num)).1
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `Li 3 (1 / 2) < 0.53721319360804020096` (true value `0.537213193608040200940…`). -/
theorem Li_three_one_half_lt : Li 3 (1 / 2) < (0.53721319360804020096 : ℝ) := by
  have h := (Li_mem_partial 3 45 (x := 1 / 2) (by norm_num) (by norm_num)).2
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `0.51747906167389938603 < Li 4 (1 / 2)` (true value `0.517479061673899386330…`). -/
theorem Li_four_one_half_gt : (0.51747906167389938603 : ℝ) < Li 4 (1 / 2) := by
  have h := (Li_mem_partial 4 40 (x := 1 / 2) (by norm_num) (by norm_num)).1
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `Li 4 (1 / 2) < 0.51747906167389938636` (true value `0.517479061673899386330…`). -/
theorem Li_four_one_half_lt : Li 4 (1 / 2) < (0.51747906167389938636 : ℝ) := by
  have h := (Li_mem_partial 4 40 (x := 1 / 2) (by norm_num) (by norm_num)).2
  norm_num [Finset.sum_range_succ] at h
  linarith

/-! ### `ζ(3)` -/

/-- Lower and upper bounds on the product of two nonnegative reals from bounds on each. -/
theorem mul_bounds {a b c d x y : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hx : a ≤ x ∧ x ≤ b)
    (hy : c ≤ y ∧ y ≤ d) : a * c ≤ x * y ∧ x * y ≤ b * d :=
  ⟨mul_le_mul hx.1 hy.1 hc (ha.trans hx.1),
    mul_le_mul hx.2 hy.2 (hc.trans hy.1) ((ha.trans hx.1).trans hx.2)⟩

/-- Bounds on `π ^ 2` from Mathlib's twenty-digit bounds on `π`. -/
theorem pi_sq_bounds : (3.14159265358979323846 : ℝ) ^ 2 ≤ π ^ 2 ∧
    π ^ 2 ≤ (3.14159265358979323847 : ℝ) ^ 2 := by
  have p1 := Real.pi_gt_d20
  have p2 := Real.pi_lt_d20
  rw [sq, sq, sq]
  exact mul_bounds (by norm_num) (by norm_num) ⟨p1.le, p2.le⟩ ⟨p1.le, p2.le⟩

/-- Bounds on `log 2`. -/
theorem log_two_bounds : (0.69314718055994530893 : ℝ) ≤ log 2 ∧
    log 2 ≤ (0.69314718055994530943 : ℝ) :=
  ⟨log_two_gt_d20.le, log_two_lt_d20.le⟩

/-- `1.202056903159594284 < ζ(3)` (true value `1.2020569031595942853997…`). -/
theorem zeta3_gt_d18 : (1.202056903159594284 : ℝ) < zeta3 := by
  have hp := pi_sq_bounds
  have hl := log_two_bounds
  have hpl := mul_bounds (by norm_num) (by norm_num) hp hl
  have hl2 := mul_bounds (by norm_num) (by norm_num) hl hl
  have hl3 := mul_bounds (by norm_num) (by norm_num) hl2 hl
  have h3 := Li_three_one_half_gt
  rw [zeta3_eq_Li_three_one_half,
    show π ^ 2 / 12 * log 2 = π ^ 2 * log 2 / 12 by ring,
    show log 2 ^ 3 = log 2 * log 2 * log 2 by ring]
  norm_num at hpl hl3 ⊢
  linarith [hpl.1, hl3.2]

/-- `ζ(3) < 1.202056903159594286` (true value `1.2020569031595942853997…`). -/
theorem zeta3_lt_d18 : zeta3 < (1.202056903159594286 : ℝ) := by
  have hp := pi_sq_bounds
  have hl := log_two_bounds
  have hpl := mul_bounds (by norm_num) (by norm_num) hp hl
  have hl2 := mul_bounds (by norm_num) (by norm_num) hl hl
  have hl3 := mul_bounds (by norm_num) (by norm_num) hl2 hl
  have h3 := Li_three_one_half_lt
  rw [zeta3_eq_Li_three_one_half,
    show π ^ 2 / 12 * log 2 = π ^ 2 * log 2 / 12 by ring,
    show log 2 ^ 3 = log 2 * log 2 * log 2 by ring]
  norm_num at hpl hl3 ⊢
  linarith [hpl.2, hl3.1]

/-! ### `ζ(5)` -/

/-- The lower telescoping function `z5lo u = 1/(4u⁴) - 5/(24u⁶) + 49/(192u⁸) - 31/(64u¹⁰)`. -/
noncomputable def z5lo (u : ℝ) : ℝ :=
  1 / (4 * u ^ 4) - 5 / (24 * u ^ 6) + 49 / (192 * u ^ 8) - 31 / (64 * u ^ 10)

/-- The upper telescoping function `z5hi u = 1/(4u⁴) - 5/(24u⁶) + 49/(192u⁸)`. -/
noncomputable def z5hi (u : ℝ) : ℝ := 1 / (4 * u ^ 4) - 5 / (24 * u ^ 6) + 49 / (192 * u ^ 8)

theorem z5lo_sub_le (k : ℕ) :
    z5lo ((k : ℝ) + 1 / 2) - z5lo ((k : ℝ) + 1 / 2 + 1) ≤ 1 / ((k : ℝ) + 1) ^ 5 := by
  rw [← sub_nonneg]
  have key : 1 / ((k : ℝ) + 1) ^ 5 - (z5lo ((k : ℝ) + 1 / 2) - z5lo ((k : ℝ) + 1 / 2 + 1)) =
      (51499008 * (k : ℝ) ^ 12 + 617988096 * k ^ 11 + 3422636032 * k ^ 10 +
        11566796800 * k ^ 9 + 26561470720 * k ^ 8 + 43654547456 * k ^ 7 +
        52643464448 * k ^ 6 + 46922247680 * k ^ 5 + 30672377200 * k ^ 4 +
        14336658880 * k ^ 3 + 4547013928 * k ^ 2 + 878350032 * k + 78127611) /
        (3 * ((k : ℝ) + 1) ^ 5 * (2 * k + 1) ^ 10 * (2 * k + 3) ^ 10) := by
    have h1 : (k : ℝ) + 1 / 2 ≠ 0 := by positivity
    have h2 : (k : ℝ) + 1 / 2 + 1 ≠ 0 := by positivity
    have h3 : (k : ℝ) + 1 ≠ 0 := by positivity
    have h4 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have h5 : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
    unfold z5lo
    field_simp
    ring
  rw [key]
  positivity

theorem le_z5hi_sub (k : ℕ) :
    1 / ((k : ℝ) + 1) ^ 5 ≤ z5hi ((k : ℝ) + 1 / 2) - z5hi ((k : ℝ) + 1 / 2 + 1) := by
  rw [← sub_nonneg]
  have key : z5hi ((k : ℝ) + 1 / 2) - z5hi ((k : ℝ) + 1 / 2 + 1) - 1 / ((k : ℝ) + 1) ^ 5 =
      (952320 * (k : ℝ) ^ 10 + 9523200 * k ^ 9 + 42968832 * k ^ 8 + 115193856 * k ^ 7 +
        203207552 * k ^ 6 + 246490368 * k ^ 5 + 208239936 * k ^ 4 + 121006336 * k ^ 3 +
        46294368 * k ^ 2 + 10531008 * k + 1081757) /
        (3 * ((k : ℝ) + 1) ^ 5 * (2 * k + 1) ^ 8 * (2 * k + 3) ^ 8) := by
    have h1 : (k : ℝ) + 1 / 2 ≠ 0 := by positivity
    have h2 : (k : ℝ) + 1 / 2 + 1 ≠ 0 := by positivity
    have h3 : (k : ℝ) + 1 ≠ 0 := by positivity
    have h4 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have h5 : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
    unfold z5hi
    field_simp
    ring
  rw [key]
  positivity

theorem z5hi_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ z5hi u := by
  have h : z5hi u = (48 * u ^ 4 - 40 * u ^ 2 + 49) / (192 * u ^ 8) := by
    unfold z5hi
    field_simp
    ring
  rw [h]
  exact div_nonneg (by nlinarith [sq_nonneg (u ^ 2 - 1 / 2)]) (by positivity)

/-- Telescoping upper bound for a partial sum of the tail `∑_{m > N} m⁻⁵`. -/
theorem sum_range_tail5_le (N K : ℕ) :
    ∑ i ∈ range K, 1 / ((i : ℝ) + N + 1) ^ 5 ≤
      z5hi ((N : ℝ) + 1 / 2) - z5hi ((N : ℝ) + K + 1 / 2) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have key := le_z5hi_sub (N + K)
    rw [sum_range_succ]
    push_cast at key ⊢
    rw [show (K : ℝ) + N + 1 = N + K + 1 by ring]
    rw [show (N : ℝ) + (K + 1) + 1 / 2 = N + K + 1 / 2 + 1 by ring]
    linarith

/-- Telescoping lower bound for a partial sum of the tail `∑_{m > N} m⁻⁵`. -/
theorem z5lo_sub_le_sum_range_tail (N K : ℕ) :
    z5lo ((N : ℝ) + 1 / 2) - z5lo ((N : ℝ) + K + 1 / 2) ≤
      ∑ i ∈ range K, 1 / ((i : ℝ) + N + 1) ^ 5 := by
  induction K with
  | zero => simp
  | succ K ih =>
    have key := z5lo_sub_le (N + K)
    rw [sum_range_succ]
    push_cast at key ⊢
    rw [show (K : ℝ) + N + 1 = N + K + 1 by ring]
    rw [show (N : ℝ) + (K + 1) + 1 / 2 = N + K + 1 / 2 + 1 by ring]
    linarith

/-- The tail `∑_{m > N} m⁻⁵` is summable. -/
theorem summable_tail5 (N : ℕ) : Summable (fun i : ℕ => 1 / ((i : ℝ) + N + 1) ^ 5) := by
  have h := (summable_nat_add_iff N).mpr (summable_one_div_add_one_pow (k := 5) (by norm_num))
  exact_mod_cast h

/-- `ζ(5)` is the sum of its first `N` terms and the tail `∑_{m > N} m⁻⁵`. -/
theorem zeta5_eq_sum_add_tsum_tail (N : ℕ) :
    zeta5 = ∑ i ∈ range N, 1 / ((i : ℝ) + 1) ^ 5 + ∑' i : ℕ, 1 / ((i : ℝ) + N + 1) ^ 5 := by
  rw [zeta5, ← (summable_one_div_add_one_pow (k := 5) (by norm_num)).sum_add_tsum_nat_add N]
  push_cast
  rfl

theorem tsum_tail5_le_z5hi (N : ℕ) :
    ∑' i : ℕ, 1 / ((i : ℝ) + N + 1) ^ 5 ≤ z5hi ((N : ℝ) + 1 / 2) := by
  refine Real.tsum_le_of_sum_range_le (fun _ => by positivity) fun K => ?_
  have h := sum_range_tail5_le N K
  have h0 := z5hi_nonneg (u := (N : ℝ) + K + 1 / 2) (by positivity)
  linarith

theorem z5lo_sub_le_tsum_tail5 (N K : ℕ) :
    z5lo ((N : ℝ) + 1 / 2) - z5lo ((N : ℝ) + K + 1 / 2) ≤
      ∑' i : ℕ, 1 / ((i : ℝ) + N + 1) ^ 5 :=
  (z5lo_sub_le_sum_range_tail N K).trans
    ((summable_tail5 N).sum_le_tsum _ fun _ _ => by positivity)

/-- `1.03692775514336992626 < ζ(5)` (true value `1.036927755143369926331…`). -/
theorem zeta5_gt_d17 : (1.03692775514336992626 : ℝ) < zeta5 := by
  rw [zeta5_eq_sum_add_tsum_tail 40]
  have h := z5lo_sub_le_tsum_tail5 40 1000000
  norm_num [z5lo, Finset.sum_range_succ] at h ⊢
  linarith

/-- `ζ(5) < 1.03692775514336996706` (true value `1.036927755143369926331…`). -/
theorem zeta5_lt_d17 : zeta5 < (1.03692775514336996706 : ℝ) := by
  rw [zeta5_eq_sum_add_tsum_tail 40]
  have h := tsum_tail5_le_z5hi 40
  norm_num [z5hi, Finset.sum_range_succ] at h ⊢
  linarith

end QED.Polylog
