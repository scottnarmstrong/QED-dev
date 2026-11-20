/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKRegLOut

/-!
# Set (c), Stage K: the inner ladder placement at outer photon mass `λ`, bounds

Helper level (no frozen statement). In the inner ladder placement the inner photon has mass²
`t > 0` (`M = M_t(Y) = Y² + (1-Y) t ≥ (3/4) min(1, t)`) and the outer photon mass `λ`
(`h = M_λ(x)/x ≥ x`). As `λ → 0` the outer photon becomes soft, and the soft region sits in the
term `T₁ = -Y c x(1-x)³/(M M_λ(x))` (`lT1`), `c = Y(1-Y)`. With `q = q_r + q_s`
(`QED.TwoLoop.UnitLLink.ladderQr`, `ladderQs`), `T₁ = P q_s/(h M)` is exactly the `q_s`-part of
the leading term `P c q u/M²`, `u = M/(ch)`, of `G = P[c(q - 9ch)(u - B)/M² + 8cB/M - log(M+ch)/h]`
(`gForm_sub_eq`), so the remainder `R = G - T₁` (`lInR`) has no `1/x` singularity:

* **`abs_lInR_le`**: `|R(λ; Y, x)| ≤ K(t) (1 + ℓ(Y, x))` for every `λ`, with
  `ℓ = log 2 - log Y - log(1-Y) - log x` (`QED.TwoLoop.UnitLLink.ladderEll`) and
  `K(t) = (1 + 1/m₀)² (3 + t)`, `m₀ = (3/4) min(1, t)` (`lInBd`);
* `continuous_lInR`: `R` is continuous in `λ`; `lInR_zero`: at `λ = 0` it is the integrand of the
  Stage K piece `QED.ChainProof.SetCK.lInner`, `G(0, √t) + Y c (1-x)³/(x M)`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink

/-- The soft-outer-photon term at outer mass `λ` and inner mass² `t`. -/
noncomputable def lT1 (t lam Y x : ℝ) : ℝ :=
  -(Y * (Y * (1 - Y)) * x * (1 - x) ^ 3 / (massIn t Y * ladderInnerMass 1 lam x))

/-- The remainder `R = G(λ, √t) - T₁` of the inner placement. -/
noncomputable def lInR (t lam Y x : ℝ) : ℝ := ladderGm lam (√t) Y x - lT1 t lam Y x

/-- The constant of the bound on `R`. -/
noncomputable def lInBd (t : ℝ) : ℝ := (1 + 1 / (3 / 4 * min 1 t)) ^ 2 * (3 + t)

theorem massIn_ge {t Y : ℝ} (ht : 0 < t) (hY : Y ∈ Icc (0 : ℝ) 1) :
    3 / 4 * min 1 t ≤ massIn t Y := by
  unfold massIn ladderInnerMass
  rw [sq_sqrt ht.le]
  have hY1 : 0 ≤ 1 - Y := by linarith [hY.2]
  have hm1 : min 1 t ≤ 1 := min_le_left _ _
  have hmt : min 1 t ≤ t := min_le_right _ _
  have hm0 : 0 < min 1 t := lt_min one_pos ht
  have : (1 - Y) * min 1 t ≤ (1 - Y) * t := mul_le_mul_of_nonneg_left hmt hY1
  have : Y ^ 2 * min 1 t ≤ Y ^ 2 := by nlinarith [sq_nonneg Y]
  nlinarith [sq_nonneg (Y - 1 / 2)]

theorem massIn_le {t Y : ℝ} (ht : 0 < t) (hY : Y ∈ Icc (0 : ℝ) 1) : massIn t Y ≤ 1 + t := by
  unfold massIn ladderInnerMass
  rw [sq_sqrt ht.le]
  have hY1 : 0 ≤ 1 - Y := by linarith [hY.2]
  nlinarith [mul_le_mul_of_nonneg_right hY1 ht.le, mul_nonneg hY.1 hY1]

/-- The remainder identity: `G - P q_s/(hM)` with the leading `q_s`-term removed. -/
theorem gForm_sub_eq {P c qr qs h M A B : ℝ} (hM : M ≠ 0) (hh : h ≠ 0) (hc : c ≠ 0) :
    gForm P c (qr + qs) h M A B - P * qs / (h * M) =
      P * c * (qr - 9 * c * h) * (M / (c * h) - B) / M ^ 2 - P * c * qs * B / M ^ 2 +
        8 * P * c * B / M - P * A / h := by
  rw [gForm_eq_phi hM hh hc]
  field_simp
  ring

/-- The final polynomial comparison of `abs_gForm_inner_le`. -/
theorem lInBd_poly {r N l : ℝ} (hr : 0 ≤ r) (hN : 0 ≤ N) (hl : 0 ≤ l) :
    r + 9 / 32 * r + (r ^ 2 / 16 + r / 4) * (N + l) + (N / 2 + 1 / 32) + r / 2 ≤
      (1 + r) ^ 2 * (2 + N) * (1 + l) := by
  have e : (1 + r) ^ 2 * (2 + N) * (1 + l) = (1 + 2 * r + r ^ 2) * (2 + N) +
      (1 + 2 * r + r ^ 2) * (2 + N) * l := by ring
  rw [e]
  have h1 : 0 ≤ r * N := mul_nonneg hr hN
  have h2 : 0 ≤ r ^ 2 * N := mul_nonneg (sq_nonneg r) hN
  have h3 : (r ^ 2 / 16 + r / 4) * l ≤ (1 + 2 * r + r ^ 2) * (2 + N) * l := by
    refine mul_le_mul_of_nonneg_right ?_ hl
    nlinarith [sq_nonneg r]
  nlinarith [sq_nonneg r]

/-- `log(1 + M/(c h)) ≤ M₁ + ℓ(Y, x)` for `M ≤ M₁`, `h ≥ x`. -/
theorem log_one_add_div_le_ell {x Y h M N : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hxh : x ≤ h) (hM : 0 < M) (hMN : M ≤ N) :
    log (1 + M / (Y * (1 - Y) * h)) ≤ N + ladderEll Y x := by
  have hY1 : 0 < 1 - Y := by linarith [hY.2]
  have hc : 0 < Y * (1 - Y) := mul_pos hY.1 hY1
  have hcx : 0 < Y * (1 - Y) * x := mul_pos hc hx.1
  have hcx1 : Y * (1 - Y) * x ≤ 1 := by
    have := c_le_quarter Y
    nlinarith [hx.2, hx.1]
  have hh : 0 < h := lt_of_lt_of_le hx.1 hxh
  have hN0 : 0 ≤ N := hM.le.trans hMN
  have h1 : 1 + M / (Y * (1 - Y) * h) ≤ (1 + N) * 2 / (Y * (1 - Y) * x) := by
    have : M / (Y * (1 - Y) * h) ≤ N / (Y * (1 - Y) * x) := by
      gcongr
    have h2 : 1 ≤ 1 / (Y * (1 - Y) * x) := by rw [le_div_iff₀ hcx]; linarith
    have e : (1 + N) * 2 / (Y * (1 - Y) * x) = 2 * (1 / (Y * (1 - Y) * x)) +
        2 * (N / (Y * (1 - Y) * x)) := by ring
    have hN : 0 ≤ N / (Y * (1 - Y) * x) := div_nonneg (hM.le.trans hMN) hcx.le
    rw [e]; linarith
  have hpos : 0 < 1 + M / (Y * (1 - Y) * h) := by positivity
  have hN : 0 < 1 + N := by linarith
  calc log (1 + M / (Y * (1 - Y) * h)) ≤ log ((1 + N) * 2 / (Y * (1 - Y) * x)) :=
        log_le_log hpos h1
    _ = log (1 + N) + ladderEll Y x := by
        unfold ladderEll
        rw [log_div (by positivity) hcx.ne', log_mul hN.ne' two_ne_zero,
          log_mul hc.ne' hx.1.ne', log_mul hY.1.ne' hY1.ne']
        ring
    _ ≤ N + ladderEll Y x := by
        have := log_le_sub_one_of_pos hN
        linarith

/-- **The bound on the remainder**, in the variables of `gForm`. -/
theorem abs_gForm_inner_le {x Y h M m N : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hxh : x ≤ h) (hm : 0 < m) (hmM : m ≤ M) (hMN : M ≤ N) :
    |gForm (Y * x * (1 - x) / 2) (Y * (1 - Y)) (ladderQr Y x + ladderQs Y x) h M
        (log (M + Y * (1 - Y) * h)) (log (1 + M / (Y * (1 - Y) * h))) -
      Y * x * (1 - x) / 2 * ladderQs Y x / (h * M)| ≤
      (1 + 1 / m) ^ 2 * (2 + N) * (1 + ladderEll Y x) := by
  have hY0 := hY.1
  have hY1 : 0 < 1 - Y := by linarith [hY.2]
  have hx0 := hx.1
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hc : 0 < Y * (1 - Y) := mul_pos hY0 hY1
  have hh : 0 < h := lt_of_lt_of_le hx0 hxh
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hN : 0 ≤ N := hM.le.trans hMN
  have hl := ladderEll_nonneg hY hx
  rw [gForm_sub_eq hM.ne' hh.ne' hc.ne']
  set c := Y * (1 - Y) with hc_def
  set P := Y * x * (1 - x) / 2 with hP_def
  set r := 1 / m with hr_def
  have hr : 0 < r := by positivity
  have hcq : c ≤ 1 / 4 := c_le_quarter Y
  have hP0 : 0 ≤ P := by positivity
  have hP8 : P ≤ 1 / 8 := by
    have h1 : Y * (x * (1 - x)) ≤ 1 * (1 / 4) :=
      mul_le_mul hY.2.le (c_le_quarter x) (by positivity) zero_le_one
    calc P = Y * (x * (1 - x)) / 2 := by rw [hP_def]; ring
      _ ≤ 1 * (1 / 4) / 2 := div_le_div_of_nonneg_right h1 (by norm_num)
      _ = 1 / 8 := by norm_num
  have hPh : P / h ≤ 1 / 2 := by
    rw [div_le_iff₀ hh]
    have : P ≤ x / 2 := by
      rw [hP_def]
      have : Y * (1 - x) ≤ 1 := by nlinarith
      nlinarith
    linarith
  have hiM : 1 / M ≤ r := one_div_le_one_div_of_le hm hmM
  have hiM0 : 0 ≤ 1 / M := by positivity
  set u := M / (c * h) with hu_def
  have hu0 : 0 ≤ u := by positivity
  set B := log (1 + u) with hB_def
  have hB0 : 0 ≤ B := log_one_add_nonneg hu0
  have hBu : B ≤ u := log_one_add_le_self hu0
  have hBl : B ≤ N + ladderEll Y x := log_one_add_div_le_ell hx hY hxh hM hMN
  set z := M + c * h with hz_def
  have hz : m ≤ z := by have : 0 ≤ c * h := by positivity
                        linarith
  have hz0 : 0 < z := lt_of_lt_of_le hm hz
  -- the four terms
  have ta : |P * c * (ladderQr Y x - 9 * c * h) * (u - B) / M ^ 2| ≤ r + 9 / 32 * r := by
    have hq := abs_ladderQr_le hY hx
    have huB : 0 ≤ u - B := by linarith
    have huB' : u - B ≤ u := by linarith
    have e1 : |P * c * (ladderQr Y x - 9 * c * h) * (u - B) / M ^ 2| =
        P * c * |ladderQr Y x - 9 * c * h| * (u - B) / M ^ 2 := by
      rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_nonneg hP0, abs_of_nonneg hc.le,
        abs_of_nonneg huB, abs_of_nonneg (by positivity : (0 : ℝ) ≤ M ^ 2)]
    rw [e1]
    have e2 : P * c * (|ladderQr Y x| + 9 * c * h) * u / M ^ 2 =
        (P / h) * |ladderQr Y x| * (1 / M) + 9 * P * c * (1 / M) := by
      rw [hu_def]; field_simp
    have hab : |ladderQr Y x - 9 * c * h| ≤ |ladderQr Y x| + 9 * c * h := by
      have := abs_sub (ladderQr Y x) (9 * c * h)
      rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 9 * c * h)] at this
    calc P * c * |ladderQr Y x - 9 * c * h| * (u - B) / M ^ 2
        ≤ P * c * (|ladderQr Y x| + 9 * c * h) * u / M ^ 2 := by gcongr
      _ = (P / h) * |ladderQr Y x| * (1 / M) + 9 * P * c * (1 / M) := e2
      _ ≤ 1 / 2 * 2 * r + 9 * (1 / 8) * (1 / 4) * r := by
          have hPh0 : 0 ≤ P / h := by positivity
          have a1 : P / h * |ladderQr Y x| ≤ 1 / 2 * 2 := mul_le_mul hPh hq (abs_nonneg _)
            (by norm_num)
          have a2 : 9 * P * c ≤ 9 * (1 / 8) * (1 / 4) := by
            have := mul_le_mul hP8 hcq hc.le (by norm_num)
            linarith
          have a3 := mul_le_mul a1 hiM hiM0 (by norm_num)
          have a4 := mul_le_mul a2 hiM hiM0 (by norm_num)
          linarith
      _ = r + 9 / 32 * r := by ring
  have tb : |P * c * ladderQs Y x * B / M ^ 2| ≤ r ^ 2 / 16 * (N + ladderEll Y x) := by
    have e1 : |P * c * ladderQs Y x| = Y * c ^ 2 * (1 - x) ^ 3 := by
      unfold ladderQs
      rw [hP_def, ← hc_def]
      have : Y * x * (1 - x) / 2 * c * -(2 * c * (1 - x) ^ 2 / x) =
          -(Y * c ^ 2 * (1 - x) ^ 3) := by field_simp
      rw [this, abs_neg, abs_of_nonneg (by positivity)]
    have e2 : Y * c ^ 2 * (1 - x) ^ 3 ≤ 1 / 16 := by
      have h1 : (1 - x) ^ 3 ≤ 1 := pow_le_one₀ hx1.le (by linarith)
      have h2 : c ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ hc.le hcq 2
      have := mul_le_mul (mul_le_mul hY.2.le h2 (by positivity) zero_le_one) h1
        (by positivity) (by positivity)
      linarith
    have hM2 : 1 / M ^ 2 ≤ r ^ 2 := by
      rw [one_div, ← inv_pow, ← one_div]; exact pow_le_pow_left₀ hiM0 hiM 2
    rw [abs_div, abs_mul, e1, abs_of_nonneg hB0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ M ^ 2)]
    calc Y * c ^ 2 * (1 - x) ^ 3 * B / M ^ 2 = Y * c ^ 2 * (1 - x) ^ 3 * B * (1 / M ^ 2) := by
          ring
      _ ≤ 1 / 16 * (N + ladderEll Y x) * r ^ 2 := by
          gcongr
      _ = r ^ 2 / 16 * (N + ladderEll Y x) := by ring
  have tc : |8 * P * c * B / M| ≤ r / 4 * (N + ladderEll Y x) := by
    rw [abs_of_nonneg (by positivity)]
    have a2 : 8 * P * c ≤ 8 * (1 / 8) * (1 / 4) := by
      have := mul_le_mul hP8 hcq hc.le (by norm_num)
      linarith
    calc 8 * P * c * B / M = (8 * P * c) * B * (1 / M) := by ring
      _ ≤ 8 * (1 / 8) * (1 / 4) * (N + ladderEll Y x) * r := by gcongr
      _ = r / 4 * (N + ladderEll Y x) := by ring
  have td : |P * log z / h| ≤ N / 2 + 1 / 32 + r / 2 := by
    have hlz := abs_log_le_add_inv hz0
    have hiz : 1 / z ≤ r := one_div_le_one_div_of_le hm hz
    rw [abs_div, abs_mul, abs_of_nonneg hP0, abs_of_pos hh]
    have e : P * (z + 1 / z) / h = (P / h) * M + P * c + (P / h) * (1 / z) := by
      rw [hz_def]; field_simp
    calc P * |log z| / h ≤ P * (z + 1 / z) / h := by gcongr
      _ = (P / h) * M + P * c + (P / h) * (1 / z) := e
      _ ≤ 1 / 2 * N + 1 / 8 * (1 / 4) + 1 / 2 * r := by
          have hPh0 : 0 ≤ P / h := by positivity
          have a1 := mul_le_mul hPh hMN hM.le (by norm_num)
          have a2 := mul_le_mul hP8 hcq hc.le (by norm_num)
          have a3 := mul_le_mul hPh hiz (by positivity) (by norm_num)
          linarith
      _ = N / 2 + 1 / 32 + r / 2 := by ring
  have hsum := lInBd_poly hr.le hN hl
  have e3 : (1 + 1 / m) = 1 + r := by rw [hr_def]
  rw [e3]
  have s1 := abs_add_le (P * c * (ladderQr Y x - 9 * c * h) * (u - B) / M ^ 2 -
    P * c * ladderQs Y x * B / M ^ 2 + 8 * P * c * B / M) (-(P * log z / h))
  have s2 := abs_add_le (P * c * (ladderQr Y x - 9 * c * h) * (u - B) / M ^ 2 -
    P * c * ladderQs Y x * B / M ^ 2) (8 * P * c * B / M)
  have s3 := abs_sub (P * c * (ladderQr Y x - 9 * c * h) * (u - B) / M ^ 2)
    (P * c * ladderQs Y x * B / M ^ 2)
  rw [abs_neg] at s1
  have e4 : P * c * (ladderQr Y x - 9 * c * h) * (u - B) / M ^ 2 -
      P * c * ladderQs Y x * B / M ^ 2 + 8 * P * c * B / M - P * log z / h =
      P * c * (ladderQr Y x - 9 * c * h) * (u - B) / M ^ 2 -
      P * c * ladderQs Y x * B / M ^ 2 + 8 * P * c * B / M + -(P * log z / h) := by ring
  rw [e4]
  have hfin : r + 9 / 32 * r + r ^ 2 / 16 * (N + ladderEll Y x) + r / 4 * (N + ladderEll Y x) +
      (N / 2 + 1 / 32 + r / 2) ≤ (1 + r) ^ 2 * (2 + N) * (1 + ladderEll Y x) := by
    linarith only [hsum]
  linarith only [ta, tb, tc, td, s1, s2, s3, hfin]

theorem lT1_eq {t lam Y x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    lT1 t lam Y x = Y * x * (1 - x) / 2 * ladderQs Y x /
      (ladderInnerMass 1 lam x / x * massIn t Y) := by
  have hM := massIn_pos ht (Ioo_subset_Icc_self hY)
  have hx0 := hx.1.ne'
  have hMx : 0 < ladderInnerMass 1 lam x := ladderInnerMass_pos_of_pos hx.1 hx.2.le
  unfold lT1 ladderQs
  field_simp

/-- **The uniform bound on the remainder of the inner placement**: for every outer mass `λ`,
`|R(λ; Y, x)| ≤ K(t) (1 + ℓ(Y, x))` on `(0, 1)²`. -/
theorem abs_lInR_le {t lam Y x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) : |lInR t lam Y x| ≤ lInBd t * (1 + ladderEll Y x) := by
  have hm : 0 < 3 / 4 * min 1 t := by have := lt_min one_pos ht; positivity
  have hxh : x ≤ ladderInnerMass 1 lam x / x := by
    rw [le_div_iff₀ hx.1]; unfold ladderInnerMass
    nlinarith [mul_nonneg (sub_nonneg.2 hx.2.le) (sq_nonneg lam)]
  have h := abs_gForm_inner_le hx hY hxh hm (massIn_ge ht (Ioo_subset_Icc_self hY))
    (massIn_le ht (Ioo_subset_Icc_self hY))
  have e : massIn t Y = ladderInnerMass 1 (√t) Y := rfl
  rw [e] at h
  rw [lInR, lT1_eq ht hY hx, e, ladderGm_eq_form, ladderQ_eq hx.1.ne']
  refine h.trans (le_of_eq ?_)
  unfold lInBd
  ring

/-- `R` is continuous in the outer mass `λ`. -/
theorem continuous_lInR {t Y x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) : Continuous fun lam => lInR t lam Y x := by
  have hc : 0 < Y * (1 - Y) := mul_pos hY.1 (by linarith [hY.2])
  have hM := massIn_pos ht (Ioo_subset_Icc_self hY)
  have hMx : ∀ lam, 0 < ladderInnerMass 1 lam x := fun lam =>
    ladderInnerMass_pos_of_pos hx.1 hx.2.le
  have hMc : Continuous fun lam => ladderInnerMass 1 lam x := by unfold ladderInnerMass; fun_prop
  have hh : ∀ lam, 0 < ladderInnerMass 1 lam x / x := fun lam => div_pos (hMx lam) hx.1
  simp only [lInR, lT1, ladderGm_eq_form, gForm]
  have hMs : massIn t Y = ladderInnerMass 1 (√t) Y := rfl
  rw [← hMs]
  have h1 : ∀ lam, massIn t Y * (ladderInnerMass 1 lam x / x) ≠ 0 := fun lam =>
    mul_ne_zero hM.ne' (hh lam).ne'
  have h2 : ∀ lam, ladderInnerMass 1 lam x / x ≠ 0 := fun lam => (hh lam).ne'
  have h3 : ∀ lam, massIn t Y + Y * (1 - Y) * (ladderInnerMass 1 lam x / x) ≠ 0 := fun lam => by
    have := hh lam; positivity
  have h4 : ∀ lam, 1 + massIn t Y / (Y * (1 - Y) * (ladderInnerMass 1 lam x / x)) ≠ 0 :=
    fun lam => by have := hh lam; positivity
  have h5 : ∀ lam, massIn t Y * ladderInnerMass 1 lam x ≠ 0 := fun lam =>
    mul_ne_zero hM.ne' (hMx lam).ne'
  have h6 : massIn t Y ^ 2 ≠ 0 := pow_ne_zero 2 hM.ne'
  have h7 : massIn t Y ≠ 0 := hM.ne'
  have h8 : ∀ _ : ℝ, x ≠ 0 := fun _ => hx.1.ne'
  have h9 : ∀ lam, Y * (1 - Y) * (ladderInnerMass 1 lam x / x) ≠ 0 := fun lam =>
    mul_ne_zero hc.ne' (hh lam).ne'
  have h10 : ∀ lam, ladderInnerMass 1 lam x ≠ 0 := fun lam => (hMx lam).ne'
  fun_prop (disch := assumption)

/-- At `λ = 0` the remainder is the integrand of `lInner`. -/
theorem lInR_zero {t Y x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    lInR t 0 Y x = ladderGm 0 (√t) Y x + Y * (Y * (1 - Y)) * (1 - x) ^ 3 / (x * massIn t Y) := by
  have hM := massIn_pos ht (Ioo_subset_Icc_self hY)
  have hx0 := hx.1.ne'
  unfold lInR lT1 ladderInnerMass
  field_simp
  ring

end QED.ChainProof.SetCK
