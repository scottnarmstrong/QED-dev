/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKOuterY
public import QED.TwoLoop.UnitLCloseBound

/-!
# Set (c), Stage K: a bound on the outer-placement integrand

Helper level (no frozen statement). For `x, Y ∈ (0, 1)` and `h > 0`,
`|G(Y, x; M = Y², h)| ≤ 4 (1 + 1/h)²` (`abs_outerG_le`). The proof uses the form
`G = P [c (q - 9ch)(u - log(1+u))/M² + 8c log(1+u)/M - log(M + ch)/h]`, `u = M/(ch)`, of
`QED.TwoLoop.UnitLLink.gForm_eq_phi` with its weight bounds, together with `x |q| ≤ 5/2`.
Since `h_t(x) = (x² + (1-x) t)/x ≥ (3/4) min(1, t)`, the bound is uniform on the unit square, which
gives the integrability needed for the `Y`-integration and for exchanging the order of
integration in the outer placement.
-/

@[expose] public section

namespace QED.ChainProof.SetCK

open Real Set QED.TwoLoop.UnitLLink

variable {x h Y : ℝ}

theorem mul_abs_outerQ_le (hx : x ∈ Ioo (0 : ℝ) 1) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    x * |outerQ x Y| ≤ 5 / 2 := by
  have hx0 := hx.1
  have hx1 : 0 ≤ 1 - x := by linarith [hx.2]
  unfold outerQ
  rw [ladderQ_eq hx0.ne']
  have hr := abs_ladderQr_le hY hx
  have hs : x * |ladderQs Y x| ≤ 1 / 2 := by
    unfold ladderQs
    rw [abs_neg, abs_of_nonneg (by have := hY.1; have := hY.2; positivity)]
    have hc := c_le_quarter Y
    have hc0 : 0 ≤ Y * (1 - Y) := mul_nonneg hY.1.le (by linarith [hY.2])
    have e : x * (2 * (Y * (1 - Y)) * (1 - x) ^ 2 / x) = 2 * (Y * (1 - Y)) * (1 - x) ^ 2 := by
      field_simp
    rw [e]
    have : (1 - x) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  calc x * |ladderQr Y x + ladderQs Y x| ≤ x * (|ladderQr Y x| + |ladderQs Y x|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) hx0.le
    _ = x * |ladderQr Y x| + x * |ladderQs Y x| := by ring
    _ ≤ 1 * 2 + 1 / 2 := by
        have : x * |ladderQr Y x| ≤ 1 * 2 :=
          mul_le_mul hx.2.le hr (abs_nonneg _) zero_le_one
        linarith
    _ = 5 / 2 := by norm_num

theorem abs_log_le_add_inv {A : ℝ} (hA : 0 < A) : |log A| ≤ A + 1 / A := by
  rw [abs_le]
  constructor
  · have h1 := log_le_sub_one_of_pos (inv_pos.2 hA)
    rw [log_inv] at h1
    have : 0 < A := hA
    rw [one_div]
    linarith
  · have := log_le_sub_one_of_pos hA
    have : 0 < 1 / A := by positivity
    linarith

/-- **The uniform bound** on the outer integrand. -/
theorem abs_outerG_le (hx : x ∈ Ioo (0 : ℝ) 1) (hh : 0 < h) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    |outerG x h Y| ≤ 4 * (1 + 1 / h) ^ 2 := by
  have hY0 := hY.1
  have hY1 : 0 < 1 - Y := by linarith [hY.2]
  have hx0 := hx.1
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hc : 0 < Y * (1 - Y) := mul_pos hY0 hY1
  have hM : 0 < Y ^ 2 := by positivity
  have hA := outer_mass_pos hh (Ioo_subset_Icc_self hY)
  set A := h + (1 - h) * Y with hA_def
  have hMc : Y ^ 2 + Y * (1 - Y) * h = Y * A := by rw [hA_def]; ring
  set r := 1 / h with hr_def
  have hr : 0 < r := by positivity
  have hinvA : 1 / A ≤ 1 + r := by
    rcases le_or_gt h 1 with h1 | h1
    · have : h ≤ A := by rw [hA_def]; nlinarith
      have : 1 / A ≤ 1 / h := one_div_le_one_div_of_le hh this
      linarith
    · have : 1 ≤ A := by rw [hA_def]; nlinarith
      have : 1 / A ≤ 1 := by rw [div_le_one hA]; exact this
      linarith
  have hAle : A ≤ h + 1 := by rw [hA_def]; rcases le_or_gt h 1 with h1 | h1 <;> nlinarith
  unfold outerG
  rw [gForm_eq_phi hM.ne' hh.ne' hc.ne']
  obtain ⟨hW0, hW1⟩ := phi_weight_bounds hc hh hM
  set u := Y ^ 2 / (Y * (1 - Y) * h) with hu_def
  have hu0 : 0 ≤ u := by positivity
  set B := log (1 + u) with hB_def
  have hB0 : 0 ≤ B := log_one_add_nonneg hu0
  have hBu : B ≤ u := log_one_add_le_self hu0
  set W := Y * (1 - Y) * (u - B) / (Y ^ 2) ^ 2 with hW_def
  have hW : W ≤ r / (Y * A) := by
    rw [hMc] at hW1
    have e : r / (Y * A) = (1 / (Y * A)) / h := by rw [hr_def]; field_simp
    rw [e, le_div_iff₀ hh, mul_comm]
    exact hW1
  have hq := mul_abs_outerQ_le hx hY
  have hlog : log (Y ^ 2 + Y * (1 - Y) * h) = log Y + log A := by
    rw [hMc, log_mul hY0.ne' hA.ne']
  rw [hlog]
  set P := Y * x * (1 - x) / 2 with hP_def
  have hP0 : 0 ≤ P := by positivity
  have hxx : x * (1 - x) ≤ 1 / 4 := c_le_quarter x
  have hcq : Y * (1 - Y) ≤ 1 / 4 := c_le_quarter Y
  have e : P * (Y * (1 - Y) * (outerQ x Y - 9 * (Y * (1 - Y)) * h) * (u - B) / (Y ^ 2) ^ 2 +
      8 * (Y * (1 - Y)) * B / Y ^ 2 - (log Y + log A) / h) =
      P * outerQ x Y * W - 9 * P * (Y * (1 - Y)) * (h * W) +
        4 * (x * (1 - x)) * ((1 - Y) * B) - P * r * log Y - P * r * log A := by
    rw [hW_def, hP_def, hr_def]
    field_simp
    ring
  rw [e]
  -- the four terms
  have t1 : |P * outerQ x Y * W| ≤ 5 / 4 * (r * (1 + r)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hP0, abs_of_nonneg hW0]
    calc P * |outerQ x Y| * W ≤ P * |outerQ x Y| * (r / (Y * A)) :=
          mul_le_mul_of_nonneg_left hW (by positivity)
      _ = (1 - x) / 2 * (x * |outerQ x Y|) * r * (1 / A) := by
          rw [hP_def]; field_simp
      _ ≤ 1 / 2 * (5 / 2) * r * (1 + r) := by
          have h1 : (1 - x) / 2 ≤ 1 / 2 := by linarith
          have h2 : 0 ≤ x * |outerQ x Y| := by positivity
          have h3 : 0 ≤ 1 / A := by positivity
          have := mul_le_mul h1 hq h2 (by norm_num)
          have := mul_le_mul this hinvA h3 (by positivity)
          nlinarith
      _ = 5 / 4 * (r * (1 + r)) := by ring
  have t2 : |9 * P * (Y * (1 - Y)) * (h * W)| ≤ 9 / 32 * (1 + r) := by
    have hhW : h * W ≤ 1 / (Y * A) := by
      have := mul_le_mul_of_nonneg_left hW hh.le
      calc h * W ≤ h * (r / (Y * A)) := this
        _ = 1 / (Y * A) := by rw [hr_def]; field_simp
    have hhW0 : 0 ≤ h * W := mul_nonneg hh.le hW0
    rw [abs_of_nonneg (by positivity)]
    calc 9 * P * (Y * (1 - Y)) * (h * W) ≤ 9 * P * (Y * (1 - Y)) * (1 / (Y * A)) :=
          mul_le_mul_of_nonneg_left hhW (by positivity)
      _ = 9 / 2 * (x * (1 - x)) * (Y * (1 - Y)) * (1 / A) := by rw [hP_def]; field_simp
      _ ≤ 9 / 2 * (1 / 4) * (1 / 4) * (1 + r) := by
          have h0 : 0 ≤ x * (1 - x) := by positivity
          gcongr
      _ = 9 / 32 * (1 + r) := by ring
  have t3 : |4 * (x * (1 - x)) * ((1 - Y) * B)| ≤ r := by
    have hB1 : (1 - Y) * B ≤ Y * r := by
      calc (1 - Y) * B ≤ (1 - Y) * u := mul_le_mul_of_nonneg_left hBu hY1.le
        _ = Y * r := by rw [hu_def, hr_def]; field_simp
    rw [abs_of_nonneg (by positivity)]
    have : Y * r ≤ r := by nlinarith
    have hB0' : 0 ≤ (1 - Y) * B := mul_nonneg hY1.le hB0
    have := mul_le_mul hxx (hB1.trans this) hB0' (by norm_num)
    linarith
  have t4 : |P * r * log Y| ≤ 1 / 8 * r := by
    have hYl : |log Y * Y| < 1 := abs_log_mul_self_lt Y hY0 hY.2.le
    rw [abs_mul, abs_mul, abs_of_nonneg hP0, abs_of_pos hr]
    have e2 : P * r * |log Y| = x * (1 - x) / 2 * r * |log Y * Y| := by
      rw [abs_mul (log Y) Y, abs_of_pos hY0, hP_def]; ring
    rw [e2]
    have h0 : 0 ≤ x * (1 - x) := by positivity
    have := mul_le_mul hxx hYl.le (abs_nonneg _) (by norm_num)
    calc x * (1 - x) / 2 * r * |log Y * Y| = r / 2 * (x * (1 - x) * |log Y * Y|) := by ring
      _ ≤ r / 2 * (1 / 4 * 1) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 / 8 * r := by ring
  have t5 : |P * r * log A| ≤ 1 / 8 * r * (h + 1 + (1 + r)) := by
    have hlA := abs_log_le_add_inv hA
    rw [abs_mul, abs_mul, abs_of_nonneg hP0, abs_of_pos hr]
    have hP : P ≤ 1 / 8 := by
      have h1 : Y * (x * (1 - x)) ≤ 1 * (1 / 4) :=
        mul_le_mul hY.2.le hxx (by positivity) zero_le_one
      calc P = Y * (x * (1 - x)) / 2 := by rw [hP_def]; ring
        _ ≤ 1 * (1 / 4) / 2 := div_le_div_of_nonneg_right h1 (by norm_num)
        _ = 1 / 8 := by norm_num
    have hlA' : |log A| ≤ h + 1 + (1 + r) := by linarith only [hlA, hAle, hinvA]
    have := mul_le_mul hP hlA' (abs_nonneg _) (by norm_num)
    calc P * r * |log A| = r * (P * |log A|) := by ring
      _ ≤ r * (1 / 8 * (h + 1 + (1 + r))) := mul_le_mul_of_nonneg_left this hr.le
      _ = 1 / 8 * r * (h + 1 + (1 + r)) := by ring
  have hrh : r * h = 1 := by rw [hr_def]; field_simp
  have habs := abs_sub (P * outerQ x Y * W - 9 * P * (Y * (1 - Y)) * (h * W) +
    4 * (x * (1 - x)) * ((1 - Y) * B) - P * r * log Y) (P * r * log A)
  have habs2 := abs_sub (P * outerQ x Y * W - 9 * P * (Y * (1 - Y)) * (h * W) +
    4 * (x * (1 - x)) * ((1 - Y) * B)) (P * r * log Y)
  have habs3 := abs_add_le (P * outerQ x Y * W - 9 * P * (Y * (1 - Y)) * (h * W))
    (4 * (x * (1 - x)) * ((1 - Y) * B))
  have habs4 := abs_sub (P * outerQ x Y * W) (9 * P * (Y * (1 - Y)) * (h * W))
  have e3 : (1 + 1 / h) = 1 + r := by rw [hr_def]
  rw [e3]
  have hsum : |P * outerQ x Y * W - 9 * P * (Y * (1 - Y)) * (h * W) +
      4 * (x * (1 - x)) * ((1 - Y) * B) - P * r * log Y - P * r * log A| ≤
      5 / 4 * (r * (1 + r)) + 9 / 32 * (1 + r) + r + 1 / 8 * r +
        1 / 8 * r * (h + 1 + (1 + r)) := by
    linarith only [t1, t2, t3, t4, t5, habs, habs2, habs3, habs4]
  have hfin : 5 / 4 * (r * (1 + r)) + 9 / 32 * (1 + r) + r + 1 / 8 * r +
      1 / 8 * r * (h + 1 + (1 + r)) ≤ 4 * (1 + r) ^ 2 := by
    have e4 : 1 / 8 * r * (h + 1 + (1 + r)) = 1 / 8 * (r * h) + 1 / 4 * r + 1 / 8 * r ^ 2 := by
      ring
    rw [e4, hrh]
    nlinarith only [sq_nonneg r, hr.le]
  linarith only [hsum, hfin]

end QED.ChainProof.SetCK
