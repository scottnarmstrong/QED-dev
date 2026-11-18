/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.VPChainSetB
public import QED.TwoLoop.A1FourNumerics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An enclosure of the set (b) constant (O3-14)

`0.00255852 < A_(b) < 0.00255853` for `A_(b) = QED.Chain.aSetB = (8/3) ζ(3) - (4/135) π² - 943/324`
(numerically `0.002 558 524 936 5…`). It is **not** frozen.

The width `10⁻⁸` needs `ζ(3)` to about `10⁻⁹`, beyond the `1.5·10⁻⁵` of
`QED.TwoLoop.Numerics.zeta_three_gt`/`zeta_three_lt`. The first `40` terms of `∑ (n+1)⁻³` are kept
(`QED.TwoLoop.Numerics.tsum_eq_sum_add_tsum_tail`); the tail `∑_{m > 40} m⁻³` is enclosed by sharper
telescoping functions of `u = m - 1/2`,
`zlo u = 1/(2u²) - 1/(8u⁴)` and `zhi u = zlo u + 7/(96u⁶)`, which satisfy, for every natural `k`,
`zlo(k + 1/2) - zlo(k + 3/2) ≤ (k+1)⁻³ ≤ zhi(k + 1/2) - zhi(k + 3/2)` (the differences are
rational functions whose numerators have positive coefficients in `k`). This gives
`1.202056903 < ζ(3) < 1.2020569033` (`zeta3_gt`, `zeta3_lt`); `π` is taken from Mathlib's
twenty-digit bounds.
-/

@[expose] public section

open Real Finset

namespace QED.Chain

/-- The lower telescoping function `zlo u = 1/(2u²) - 1/(8u⁴)`. -/
noncomputable def zlo (u : ℝ) : ℝ := 1 / (2 * u ^ 2) - 1 / (8 * u ^ 4)

/-- The upper telescoping function `zhi u = 1/(2u²) - 1/(8u⁴) + 7/(96u⁶)`. -/
noncomputable def zhi (u : ℝ) : ℝ := 1 / (2 * u ^ 2) - 1 / (8 * u ^ 4) + 7 / (96 * u ^ 6)

theorem zlo_sub_le (k : ℕ) :
    zlo ((k : ℝ) + 1 / 2) - zlo ((k : ℝ) + 1 / 2 + 1) ≤ 1 / ((k : ℝ) + 1) ^ 3 := by
  rw [← sub_nonneg]
  have key : 1 / ((k : ℝ) + 1) ^ 3 - (zlo ((k : ℝ) + 1 / 2) - zlo ((k : ℝ) + 1 / 2 + 1)) =
      (112 * (k : ℝ) ^ 4 + 448 * k ^ 3 + 656 * k ^ 2 + 416 * k + 97) /
        (((k : ℝ) + 1) ^ 3 * (2 * k + 1) ^ 4 * (2 * k + 3) ^ 4) := by
    have h1 : (k : ℝ) + 1 / 2 ≠ 0 := by positivity
    have h2 : (k : ℝ) + 1 / 2 + 1 ≠ 0 := by positivity
    have h3 : (k : ℝ) + 1 ≠ 0 := by positivity
    have h4 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have h5 : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
    unfold zlo
    field_simp
    ring
  rw [key]
  positivity

theorem le_zhi_sub (k : ℕ) :
    1 / ((k : ℝ) + 1) ^ 3 ≤ zhi ((k : ℝ) + 1 / 2) - zhi ((k : ℝ) + 1 / 2 + 1) := by
  rw [← sub_nonneg]
  have key : zhi ((k : ℝ) + 1 / 2) - zhi ((k : ℝ) + 1 / 2 + 1) - 1 / ((k : ℝ) + 1) ^ 3 =
      (7936 * (k : ℝ) ^ 6 + 47616 * k ^ 5 + 118608 * k ^ 4 + 156992 * k ^ 3 + 116520 * k ^ 2 +
        46032 * k + 7573) /
        (3 * ((k : ℝ) + 1) ^ 3 * (2 * k + 1) ^ 6 * (2 * k + 3) ^ 6) := by
    have h1 : (k : ℝ) + 1 / 2 ≠ 0 := by positivity
    have h2 : (k : ℝ) + 1 / 2 + 1 ≠ 0 := by positivity
    have h3 : (k : ℝ) + 1 ≠ 0 := by positivity
    have h4 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have h5 : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
    unfold zhi
    field_simp
    ring
  rw [key]
  positivity

theorem zhi_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ zhi u := by
  have h : zhi u = (48 * u ^ 4 - 12 * u ^ 2 + 7) / (96 * u ^ 6) := by
    unfold zhi
    field_simp
    ring
  rw [h]
  exact div_nonneg (by nlinarith [sq_nonneg (u ^ 2 - 1 / 8)]) (by positivity)

/-- Telescoping upper bound for a partial sum of the tail `∑_{m > N} m⁻³`. -/
theorem sum_range_tail_le_zhi (N K : ℕ) :
    ∑ i ∈ range K, 1 / ((i : ℝ) + N + 1) ^ 3 ≤
      zhi ((N : ℝ) + 1 / 2) - zhi ((N : ℝ) + K + 1 / 2) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have key := le_zhi_sub (N + K)
    rw [sum_range_succ]
    push_cast at key ⊢
    rw [show (K : ℝ) + N + 1 = N + K + 1 by ring]
    rw [show (N : ℝ) + (K + 1) + 1 / 2 = N + K + 1 / 2 + 1 by ring]
    linarith

/-- Telescoping lower bound for a partial sum of the tail `∑_{m > N} m⁻³`. -/
theorem zlo_sub_le_sum_range_tail (N K : ℕ) :
    zlo ((N : ℝ) + 1 / 2) - zlo ((N : ℝ) + K + 1 / 2) ≤
      ∑ i ∈ range K, 1 / ((i : ℝ) + N + 1) ^ 3 := by
  induction K with
  | zero => simp
  | succ K ih =>
    have key := zlo_sub_le (N + K)
    rw [sum_range_succ]
    push_cast at key ⊢
    rw [show (K : ℝ) + N + 1 = N + K + 1 by ring]
    rw [show (N : ℝ) + (K + 1) + 1 / 2 = N + K + 1 / 2 + 1 by ring]
    linarith

theorem tsum_tail_le_zhi (N : ℕ) :
    ∑' i : ℕ, 1 / ((i : ℝ) + N + 1) ^ 3 ≤ zhi ((N : ℝ) + 1 / 2) := by
  refine Real.tsum_le_of_sum_range_le (fun _ => by positivity) fun K => ?_
  have h := sum_range_tail_le_zhi N K
  have h0 := zhi_nonneg (u := (N : ℝ) + K + 1 / 2) (by positivity)
  linarith

theorem zlo_sub_le_tsum_tail (N K : ℕ) :
    zlo ((N : ℝ) + 1 / 2) - zlo ((N : ℝ) + K + 1 / 2) ≤ ∑' i : ℕ, 1 / ((i : ℝ) + N + 1) ^ 3 :=
  (zlo_sub_le_sum_range_tail N K).trans
    ((QED.TwoLoop.Numerics.summable_tail N).sum_le_tsum _ fun _ _ => by positivity)

/-- `1.202056903 < ζ(3)` (true value `1.2020569031596…`). -/
theorem zeta3_gt : (1.202056903 : ℝ) < QED.Polylog.zeta3 := by
  unfold QED.Polylog.zeta3
  rw [QED.TwoLoop.Numerics.tsum_eq_sum_add_tsum_tail 40]
  have h := zlo_sub_le_tsum_tail 40 1000000
  norm_num [zlo, Finset.sum_range_succ] at h ⊢
  linarith

/-- `ζ(3) < 1.2020569033` (true value `1.2020569031596…`). -/
theorem zeta3_lt : QED.Polylog.zeta3 < (1.2020569033 : ℝ) := by
  unfold QED.Polylog.zeta3
  rw [QED.TwoLoop.Numerics.tsum_eq_sum_add_tsum_tail 40]
  have h := tsum_tail_le_zhi 40
  norm_num [zhi, Finset.sum_range_succ] at h ⊢
  linarith

/-- **O3-14.** `0.00255852 < A_(b) < 0.00255853`. -/
theorem aSetB_bounds : 0.00255852 < aSetB ∧ aSetB < 0.00255853 := by
  have z1 := zeta3_gt
  have z2 := zeta3_lt
  have hp0 := Real.pi_pos
  have p1 := Real.pi_gt_d20
  have p2 := Real.pi_lt_d20
  have q1 : (3.14159265358979323846 : ℝ) ^ 2 < π ^ 2 := by gcongr
  have q2 : π ^ 2 < (3.14159265358979323847 : ℝ) ^ 2 := by gcongr
  norm_num at q1 q2
  unfold aSetB
  constructor <;> linarith

end QED.Chain
