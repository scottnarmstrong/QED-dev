/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCornerReduce
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The corner error terms: bounds on the coefficients

Section 6.3 of `docs/TWO-LOOP-UNITS.md`. For `(y₃, y₄)` in the open triangle and `0 < x < 1` the
coefficients of the `b`-integrand of the corner graph (`QED.TwoLoop.UnitSCLimit.cornerAX_eq`) are
bounded by `x` times powers of `g = y₃(1 - Y)`:

`|a₀| ≤ x/2`, `|a₁| ≤ 3xg/4`, `|a₂| ≤ xg²/4`, `|c₁| ≤ 9x/8`, `|c₂| ≤ 7xg/4`, `|c₃| ≤ 3xg²/4`,

from `|p₁| ≤ 2`, `|p₂| ≤ 4`, `|q| ≤ 1`, `|r| ≤ 3` and `0 < g ≤ 1/4`. It also proves the elementary
inequalities `log(1 + t) ≤ 2 √t` and `x log(1 + a/x) ≤ 1 + log(1 + a)` (`0 < x ≤ 1`) used by the
bounds of the error terms.
-/

@[expose] public section

open Real Set

namespace QED.TwoLoop.UnitSCCorner

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-! ### Elementary inequalities -/

/-- `log(1 + t) ≤ 2 √t` for `t ≥ 0`. -/
theorem log_one_add_le_two_sqrt {t : ℝ} (ht : 0 ≤ t) : log (1 + t) ≤ 2 * √t := by
  have hs := Real.sqrt_nonneg t
  have hsq := Real.sq_sqrt ht
  have h1 : 1 + t ≤ (1 + √t) ^ 2 := by nlinarith
  calc log (1 + t) ≤ log ((1 + √t) ^ 2) := log_le_log (by linarith) h1
    _ = 2 * log (1 + √t) := by rw [log_pow]; norm_num
    _ ≤ 2 * √t := by
        have := log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + √t)
        linarith

/-- `x log(1 + a/x) ≤ 1 + log(1 + a)` for `0 < x ≤ 1`, `a ≥ 0`. -/
theorem mul_log_one_add_div_le {x a : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (ha : 0 ≤ a) :
    x * log (1 + a / x) ≤ 1 + log (1 + a) := by
  have h1 : 1 + a / x ≤ (1 + a) * (1 + 1 / x) := by
    have : 0 ≤ a / x := by positivity
    have e : (1 + a) * (1 + 1 / x) = 1 + a / x + (a + 1 / x) := by ring
    rw [e]; have : 0 ≤ 1 / x := by positivity
    linarith
  have hl : log (1 + a / x) ≤ log (1 + a) + log (1 + 1 / x) := by
    rw [← log_mul (by positivity) (by positivity)]
    exact log_le_log (by positivity) h1
  have hla : 0 ≤ log (1 + a) := log_nonneg (by linarith)
  have hlx : x * log (1 + 1 / x) ≤ 1 := by
    have := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / x)
    have e : x * (1 + 1 / x - 1) = 1 := by field_simp; ring
    nlinarith
  have : x * log (1 + a) ≤ log (1 + a) := by nlinarith
  nlinarith

/-! ### The triangle -/

section Coeff

variable {x y3 y4 : ℝ}

theorem cornerG_pos (h3 : 0 < y3) (hY : y3 + y4 < 1) : 0 < cornerG y3 y4 := by
  unfold cornerG
  have : 0 < 1 - y3 - y4 := by linarith
  positivity

theorem cornerG_le_quarter (h3 : 0 < y3) (h4 : 0 < y4) : cornerG y3 y4 ≤ 1 / 4 := by
  unfold cornerG
  nlinarith [sq_nonneg (y3 - 1 / 2), mul_pos h3 h4]

theorem cornerG_le_one_sub (hY : y3 + y4 < 1) (h4 : 0 < y4) :
    cornerG y3 y4 ≤ 1 - (y3 + y4) := by
  unfold cornerG
  have : 0 < 1 - y3 - y4 := by linarith
  nlinarith

theorem abs_cornerP1_le (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (h3 : 0 ≤ y3) (h4 : 0 ≤ y4)
    (hY : y3 + y4 ≤ 1) : |UnitSCReduce.cornerP1 x y3 y4| ≤ 2 := by
  unfold UnitSCReduce.cornerP1
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg hx0 h3, mul_nonneg hx0 h4, mul_nonneg h3 h4,
      mul_nonneg (sub_nonneg.2 hx1) h3, mul_nonneg (sub_nonneg.2 hx1) h4,
      mul_nonneg (sub_nonneg.2 hY) hx0, mul_nonneg (mul_nonneg hx0 hx0) h3]
  · nlinarith [mul_nonneg hx0 h3, mul_nonneg hx0 h4, mul_nonneg h3 h4,
      mul_nonneg (sub_nonneg.2 hx1) h3, mul_nonneg (sub_nonneg.2 hx1) h4,
      mul_nonneg (sub_nonneg.2 hY) hx0, mul_nonneg (mul_nonneg hx0 hx0) h3]

theorem abs_cornerP2_le (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (h3 : 0 ≤ y3) (h4 : 0 ≤ y4)
    (hY : y3 + y4 ≤ 1) : |UnitSCReduce.cornerP2 x y3 y4| ≤ 4 := by
  unfold UnitSCReduce.cornerP2
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg hx0 h3, mul_nonneg hx0 h4, mul_nonneg h3 h4,
      mul_nonneg (sub_nonneg.2 hx1) h3, mul_nonneg (sub_nonneg.2 hx1) h4,
      mul_nonneg (sub_nonneg.2 hY) hx0, mul_nonneg (mul_nonneg hx0 hx0) h3]
  · nlinarith [mul_nonneg hx0 h3, mul_nonneg hx0 h4, mul_nonneg h3 h4,
      mul_nonneg (sub_nonneg.2 hx1) h3, mul_nonneg (sub_nonneg.2 hx1) h4,
      mul_nonneg (sub_nonneg.2 hY) hx0, mul_nonneg (mul_nonneg hx0 hx0) h3]

theorem abs_cornerQ_le (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (h3 : 0 ≤ y3) (h3' : y3 ≤ 1) :
    |cornerQ x y3| ≤ 1 := by
  unfold cornerQ
  have e1 : 0 ≤ x * (2 - x) := by nlinarith
  have e2 : x * (2 - x) ≤ 1 := by nlinarith [sq_nonneg (x - 1)]
  have e3 : |1 - 2 * y3| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  rw [abs_mul, abs_of_nonneg e1]
  nlinarith [abs_nonneg (1 - 2 * y3)]

theorem abs_cornerR_le (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (h3 : 0 ≤ y3) (h3' : y3 ≤ 1) :
    |cornerR x y3| ≤ 3 := by
  unfold cornerR
  have e3 : |1 - 2 * y3| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * x)]
  nlinarith [abs_nonneg (1 - 2 * y3)]

variable (hx : x ∈ Ioo (0 : ℝ) 1) (h3 : 0 < y3) (h4 : 0 < y4) (hY : y3 + y4 < 1)
include hx h3 h4 hY

theorem abs_cornerA0_le : |cornerA0 x y3 y4| ≤ x / 2 := by
  have hp := abs_cornerP1_le hx.1.le hx.2.le h3.le h4.le hY.le
  unfold cornerA0
  rw [abs_mul, abs_of_nonneg (by linarith [hx.1] : (0 : ℝ) ≤ x / 4)]
  nlinarith [hx.1]

theorem abs_cornerA1_le : |cornerA1 x y3 y4| ≤ 3 / 4 * x * cornerG y3 y4 := by
  have hp := abs_cornerP1_le hx.1.le hx.2.le h3.le h4.le hY.le
  have hq := abs_cornerQ_le hx.1.le hx.2.le h3.le (by linarith)
  have hg := cornerG_pos h3 hY
  have hqp : |cornerQ x y3 - UnitSCReduce.cornerP1 x y3 y4| ≤ 3 := (abs_sub _ _).trans (by linarith)
  unfold cornerA1
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hx.1] : (0 : ℝ) ≤ x / 4), abs_of_pos hg]
  have : 0 ≤ x / 4 * cornerG y3 y4 := by have := hx.1; positivity
  nlinarith

theorem abs_cornerA2_le : |cornerA2 x y3 y4| ≤ x * cornerG y3 y4 ^ 2 / 4 := by
  have hq := abs_cornerQ_le hx.1.le hx.2.le h3.le (by linarith)
  unfold cornerA2
  rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (by linarith [hx.1] : (0 : ℝ) ≤ x / 4),
    abs_of_nonneg (sq_nonneg (cornerG y3 y4))]
  have : 0 ≤ x / 4 * cornerG y3 y4 ^ 2 := by have := hx.1; positivity
  nlinarith

theorem abs_cornerC1_le : |cornerC1 x y3 y4| ≤ 9 / 8 * x := by
  have hp := abs_cornerP2_le hx.1.le hx.2.le h3.le h4.le hY.le
  have hg := cornerG_pos h3 hY
  have hg4 := cornerG_le_quarter h3 h4
  have h1 : |UnitSCReduce.cornerP2 x y3 y4 - 2 * (x - 1) * cornerG y3 y4| ≤ 9 / 2 := by
    have : |2 * (x - 1) * cornerG y3 y4| ≤ 1 / 2 := by
      rw [abs_of_nonpos (by nlinarith [hx.2])]
      nlinarith [hx.1, hx.2]
    calc _ ≤ |UnitSCReduce.cornerP2 x y3 y4| + |2 * (x - 1) * cornerG y3 y4| := abs_sub _ _
      _ ≤ 9 / 2 := by linarith
  unfold cornerC1
  rw [abs_neg, abs_mul, abs_of_nonneg (by linarith [hx.1] : (0 : ℝ) ≤ x / 4)]
  nlinarith [hx.1]

theorem abs_cornerC2_le : |cornerC2 x y3 y4| ≤ 7 / 4 * x * cornerG y3 y4 := by
  have hp := abs_cornerP2_le hx.1.le hx.2.le h3.le h4.le hY.le
  have hr := abs_cornerR_le hx.1.le hx.2.le h3.le (by linarith)
  have hg := cornerG_pos h3 hY
  have hrp : |cornerR x y3 + UnitSCReduce.cornerP2 x y3 y4| ≤ 7 := (abs_add_le _ _).trans (by linarith)
  unfold cornerC2
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hx.1] : (0 : ℝ) ≤ x / 4), abs_of_pos hg]
  have : 0 ≤ x / 4 * cornerG y3 y4 := by have := hx.1; positivity
  nlinarith

theorem abs_cornerC3_le : |cornerC3 x y3 y4| ≤ 3 / 4 * x * cornerG y3 y4 ^ 2 := by
  have hr := abs_cornerR_le hx.1.le hx.2.le h3.le (by linarith)
  unfold cornerC3
  rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (by linarith [hx.1] : (0 : ℝ) ≤ x / 4),
    abs_of_nonneg (sq_nonneg (cornerG y3 y4))]
  have : 0 ≤ x / 4 * cornerG y3 y4 ^ 2 := by have := hx.1; positivity
  nlinarith

omit h3 h4 hY in
theorem cornerC0_nonneg : 0 ≤ cornerC0 x := by
  unfold cornerC0
  have := hx.1; have := hx.2
  have : 0 ≤ 1 - x := by linarith
  positivity

end Coeff

end QED.TwoLoop.UnitSCCorner

end
