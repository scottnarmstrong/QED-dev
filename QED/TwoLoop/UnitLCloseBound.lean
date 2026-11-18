/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLCloseMasters
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The ladder unit L: bounds for the limit `Λ → ∞`, uniform in the photon mass

Section 2.3 of `docs/TWO-LOOP-UNITS.md`, stage (2) of the L link, step 2. After the
`a`-integration the graph half is `∬ G_Σ`, `G_Σ = G(λ,λ) - G(λ,Λ) - G(Λ,λ) + G(Λ,Λ)` (outer photon
mass first; `QED.TwoLoop.UnitLLink.sixteen_pi_pow_four_mul_graphHalf_eq_gsum`). Of these terms,

* the terms with the **outer** photon at mass `Λ` are `O((1 + log Λ)/Λ²)`:
  `|G(Λ, μ; Y, x)| ≤ (12 + log Λ + ℓ(Y, x))/Λ²` for `0 < μ ≤ Λ`, `Λ ≥ 1` (`abs_ladderGm_outer_le`),
  with `ℓ(Y, x) = log 2 - log Y - log(1 - Y) - log x` (`ladderEll`);
* the term with the **inner** photon at mass `Λ` carries the large logarithm `log M_Λ` of the inner
  subdivergence (`M_Λ = Y² + (1-Y)Λ²`) and the soft-outer-photon term `T₁` at inner mass `Λ`;
  with both removed, `e₁ = G(λ, Λ) + E(λ, Λ)` (`ladderE1`, `E` = `ladderE1Explicit`, the
  logarithm and `-T₁`) satisfies `|e₁(λ, Λ; Y, x)| ≤ 6 (1 + ℓ(Y, x))/√M_Λ(Y)` for every `λ > 0`
  and `Λ ≥ 1` (`abs_ladderE1_le`).

Both bounds are uniform in the photon mass `λ`, which is what the joint limit
`(λ, Λ) → (0, ∞)` needs. The key identity is
`G = P [c (q - 9ch)(u - log(1+u))/M² + 8c log(1+u)/M - log(M + ch)/h]`, `u = M/(ch)`
(`gForm_eq_phi`), with `0 ≤ u - log(1+u) ≤ u²/(1+u)`.
-/

@[expose] public section

open Real Set

namespace QED.TwoLoop.UnitLLink

/-! ### Elementary inequalities -/

theorem sub_log_one_add_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ u - log (1 + u) := by
  have := log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + u)
  linarith

theorem sub_log_one_add_le {u : ℝ} (hu : 0 ≤ u) : u - log (1 + u) ≤ u ^ 2 / (1 + u) := by
  have h := one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < 1 + u)
  have e : u ^ 2 / (1 + u) = u - (1 - (1 + u)⁻¹) := by
    field_simp
    ring
  rw [e]
  linarith

theorem log_one_add_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ log (1 + u) :=
  log_nonneg (by linarith)

theorem log_one_add_le_self {u : ℝ} (hu : 0 ≤ u) : log (1 + u) ≤ u := by
  have := log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + u)
  linarith

/-- `log(1 + s²) ≤ 2s` for `s ≥ 0`. -/
theorem log_one_add_sq_le {s : ℝ} (hs : 0 ≤ s) : log (1 + s ^ 2) ≤ 2 * s := by
  have h1 : log (1 + s ^ 2) ≤ log ((1 + s) ^ 2) :=
    log_le_log (by positivity) (by nlinarith)
  rw [log_pow] at h1
  have h2 := log_one_add_le_self hs
  push_cast at h1
  linarith

/-- With `u = M/(ch)` and `B = log(1 + u)`: `0 ≤ c (u - B)/M²` and `h · c (u - B)/M² ≤ 1/(M + ch)`. -/
theorem phi_weight_bounds {c h M : ℝ} (hc : 0 < c) (hh : 0 < h) (hM : 0 < M) :
    0 ≤ c * (M / (c * h) - log (1 + M / (c * h))) / M ^ 2 ∧
      h * (c * (M / (c * h) - log (1 + M / (c * h))) / M ^ 2) ≤ 1 / (M + c * h) := by
  have hu : 0 ≤ M / (c * h) := by positivity
  refine ⟨by have := sub_log_one_add_nonneg hu; positivity, ?_⟩
  have h1 := sub_log_one_add_le hu
  calc h * (c * (M / (c * h) - log (1 + M / (c * h))) / M ^ 2)
      ≤ h * (c * ((M / (c * h)) ^ 2 / (1 + M / (c * h))) / M ^ 2) := by gcongr
    _ = 1 / (M + c * h) := by
      field_simp
      ring

/-- **The identity behind the bounds**:
`gForm P c q h M A B = P [c (q - 9ch)(M/(ch) - B)/M² + 8cB/M - A/h]`. -/
theorem gForm_eq_phi {P c q h M A B : ℝ} (hM : M ≠ 0) (hh : h ≠ 0) (hc : c ≠ 0) :
    gForm P c q h M A B =
      P * (c * (q - 9 * c * h) * (M / (c * h) - B) / M ^ 2 + 8 * c * B / M - A / h) := by
  unfold gForm
  field_simp
  ring

/-! ### The logarithmic weight -/

/-- `ℓ(Y, x) = log 2 - log Y - log(1 - Y) - log x`, nonnegative on `(0, 1)²`. -/
noncomputable def ladderEll (Y x : ℝ) : ℝ := log 2 - log Y - log (1 - Y) - log x

theorem log_nonpos_of_mem {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : log t ≤ 0 :=
  log_nonpos ht.1.le ht.2.le

theorem ladderEll_nonneg {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 ≤ ladderEll Y x := by
  have h1 := log_nonpos_of_mem hY
  have h2 := log_nonpos_of_mem (⟨by linarith [hY.2], by linarith [hY.1]⟩ : 1 - Y ∈ Ioo (0 : ℝ) 1)
  have h3 := log_nonpos_of_mem hx
  have h4 : 0 ≤ log 2 := log_nonneg (by norm_num)
  unfold ladderEll
  linarith

/-! ### Common facts on `(0, 1)²` -/

theorem abs_three_mul_sub_two_le {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) : |3 * Y - 2| ≤ 2 := by
  rw [abs_le]; constructor <;> linarith [hY.1, hY.2]

theorem abs_four_mul_sub_sq_sub_two_le {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    |4 * Y - Y ^ 2 - 2| ≤ 2 := by
  rw [abs_le]; constructor <;> nlinarith [hY.1, hY.2]

theorem c_le_quarter (Y : ℝ) : Y * (1 - Y) ≤ 1 / 4 := by nlinarith [sq_nonneg (Y - 1 / 2)]

/-- The regular part `q_r = x(3Y-2) + (1-x)(4Y - Y² - 2)` of `q = x q₀`. -/
noncomputable def ladderQr (Y x : ℝ) : ℝ := x * (3 * Y - 2) + (1 - x) * (4 * Y - Y ^ 2 - 2)

/-- The singular part `q_s = -2c(1-x)²/x` of `q = x q₀`. -/
noncomputable def ladderQs (Y x : ℝ) : ℝ := -(2 * (Y * (1 - Y)) * (1 - x) ^ 2 / x)

theorem ladderQ_eq {Y x : ℝ} (hx : x ≠ 0) :
    x * ((3 * Y - 2) + (4 * Y - Y ^ 2 - 2) * ((1 - x) / x) -
        2 * (Y * (1 - Y)) * ((1 - x) / x) ^ 2) = ladderQr Y x + ladderQs Y x := by
  unfold ladderQr ladderQs
  field_simp
  ring

theorem abs_ladderQr_le {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |ladderQr Y x| ≤ 2 := by
  unfold ladderQr
  have h1 := abs_three_mul_sub_two_le hY
  have h2 := abs_four_mul_sub_sq_sub_two_le hY
  have hx1 : 0 ≤ 1 - x := by linarith [hx.2]
  have hx0 : 0 ≤ x := hx.1.le
  calc |x * (3 * Y - 2) + (1 - x) * (4 * Y - Y ^ 2 - 2)|
      ≤ |x * (3 * Y - 2)| + |(1 - x) * (4 * Y - Y ^ 2 - 2)| := abs_add_le _ _
    _ = x * |3 * Y - 2| + (1 - x) * |4 * Y - Y ^ 2 - 2| := by
      rw [abs_mul, abs_mul, abs_of_pos hx.1, abs_of_nonneg hx1]
    _ ≤ x * 2 + (1 - x) * 2 := by gcongr
    _ = 2 := by ring

/-- `x² |q| ≤ 3x` for `q = q_r + q_s`. -/
theorem sq_mul_abs_ladderQ_le {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    x ^ 2 * |ladderQr Y x + ladderQs Y x| ≤ 3 * x := by
  have h1 := abs_ladderQr_le hY hx
  have hc := c_le_quarter Y
  have hc0 : 0 < Y * (1 - Y) := mul_pos hY.1 (by linarith [hY.2])
  have hx0 := hx.1
  have hx1 : 0 ≤ 1 - x := by linarith [hx.2]
  have hs : |ladderQs Y x| = 2 * (Y * (1 - Y)) * (1 - x) ^ 2 / x := by
    unfold ladderQs; rw [abs_neg, abs_of_nonneg (by positivity)]
  have e : x ^ 2 * (2 * (Y * (1 - Y)) * (1 - x) ^ 2 / x) = 2 * (Y * (1 - Y)) * (1 - x) ^ 2 * x := by
    field_simp
  calc x ^ 2 * |ladderQr Y x + ladderQs Y x|
      ≤ x ^ 2 * (|ladderQr Y x| + |ladderQs Y x|) := by gcongr; exact abs_add_le _ _
    _ = x ^ 2 * |ladderQr Y x| + 2 * (Y * (1 - Y)) * (1 - x) ^ 2 * x := by rw [hs, mul_add, e]
    _ ≤ x ^ 2 * 2 + 2 * (1 / 4) * 1 * x := by
      gcongr
      · nlinarith
    _ ≤ 3 * x := by nlinarith

/-! ### The three terms of `gForm_eq_phi` -/

section Terms

variable {r c h M q : ℝ}

/-- The first term: `|r h · c (q - 9ch)(u - B)/M²| ≤ r (|q| + 9ch)/(M + ch)`. -/
theorem abs_phi_first_le (hr : 0 ≤ r) (hc : 0 < c) (hh : 0 < h) (hM : 0 < M) :
    |r * h * (c * (q - 9 * c * h) * (M / (c * h) - log (1 + M / (c * h))) / M ^ 2)| ≤
      r * (|q| + 9 * c * h) / (M + c * h) := by
  obtain ⟨hw0, hw1⟩ := phi_weight_bounds hc hh hM
  set w := c * (M / (c * h) - log (1 + M / (c * h))) / M ^ 2 with hw
  have e : r * h * (c * (q - 9 * c * h) * (M / (c * h) - log (1 + M / (c * h))) / M ^ 2) =
      r * (q - 9 * c * h) * (h * w) := by rw [hw]; ring
  rw [e, abs_mul, abs_mul, abs_of_nonneg hr, abs_of_nonneg (by positivity : 0 ≤ h * w)]
  have hq : |q - 9 * c * h| ≤ |q| + 9 * c * h := by
    have := abs_sub (q) (9 * c * h)
    rw [abs_of_pos (by positivity : 0 < 9 * c * h)] at this
    exact this
  calc r * |q - 9 * c * h| * (h * w) ≤ r * (|q| + 9 * c * h) * (1 / (M + c * h)) := by
        gcongr
    _ = r * (|q| + 9 * c * h) / (M + c * h) := by ring

/-- The second term: `0 ≤ h c B/M ≤ 1` for `B = log(1 + M/(ch))`. -/
theorem phi_second_bounds (hc : 0 < c) (hh : 0 < h) (hM : 0 < M) :
    0 ≤ h * c * log (1 + M / (c * h)) / M ∧ h * c * log (1 + M / (c * h)) / M ≤ 1 := by
  have hu : 0 ≤ M / (c * h) := by positivity
  have h0 := log_one_add_nonneg hu
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hM]
  have h1 := log_one_add_le_self hu
  calc h * c * log (1 + M / (c * h)) ≤ h * c * (M / (c * h)) := by gcongr
    _ = M := by field_simp

end Terms

/-! ### The terms with the outer photon at mass `Λ` -/

theorem outer_mass_bounds {Λ Y x c h M : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hc : 0 < c) (hcY : c = Y * (1 - Y)) (hh : 0 < h)
    (hxh1 : 3 / 4 ≤ x * h) (hxhΛ : x * h ≤ Λ ^ 2) (hMY : Y ^ 2 ≤ M) (hMΛ : M ≤ Λ ^ 2) :
    3 / 4 * Y ≤ M + c * h ∧ M + c * h ≤ 2 * Λ ^ 2 / x := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hx0, hx1⟩ := hx
  have hcq : c ≤ 1 / 4 := hcY ▸ c_le_quarter Y
  have hh34 : 3 / 4 ≤ h := hxh1.trans (mul_le_of_le_one_left hh.le hx1.le)
  have h1 : c * (3 / 4) ≤ c * h := mul_le_mul_of_nonneg_left hh34 hc.le
  have h2 : 3 / 4 * Y ≤ Y ^ 2 + 3 / 4 * c := by rw [hcY]; nlinarith [sq_nonneg Y]
  refine ⟨by linarith, ?_⟩
  have hΛ2 : 0 ≤ Λ ^ 2 := sq_nonneg Λ
  have h3 : c * h ≤ Λ ^ 2 / x := by
    rw [le_div_iff₀ hx0]
    calc c * h * x = c * (x * h) := by ring
      _ ≤ 1 / 4 * Λ ^ 2 := by gcongr
      _ ≤ Λ ^ 2 := by linarith
  have h4 : Λ ^ 2 ≤ Λ ^ 2 / x := by
    rw [le_div_iff₀ hx0]; exact mul_le_of_le_one_right hΛ2 hx1.le
  calc M + c * h ≤ Λ ^ 2 / x + Λ ^ 2 / x := by linarith
    _ = 2 * Λ ^ 2 / x := by ring

theorem abs_log_outer_le {Λ Y x z : ℝ} (hΛ : 1 ≤ Λ) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hlow : 3 / 4 * Y ≤ z) (hup : z ≤ 2 * Λ ^ 2 / x) :
    |log z| ≤ 1 + 2 * log Λ - log Y - log x := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hx0, hx1⟩ := hx
  have hlY := log_nonpos hY0.le hY1.le
  have hlx := log_nonpos hx0.le hx1.le
  have hlΛ := log_nonneg hΛ
  have hz : 0 < z := lt_of_lt_of_le (by positivity) hlow
  have hl1 : log (3 / 4 * Y) ≤ log z := log_le_log (by positivity) hlow
  rw [log_mul (by norm_num) hY0.ne'] at hl1
  have h34 : -1 ≤ log (3 / 4 : ℝ) := by
    have := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 4)
    norm_num at this ⊢; linarith
  have hl2 : log z ≤ log 2 + 2 * log Λ - log x := by
    have := log_le_log hz hup
    rw [log_div (by positivity) hx0.ne', log_mul (by norm_num) (by positivity), log_pow] at this
    push_cast at this
    linarith
  have hl2' : log 2 ≤ 1 := by
    have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  rw [abs_le]; constructor <;> linarith

theorem outer_first_le {Λ Y x r q c h M : ℝ} (hΛ : 1 ≤ Λ) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hc : 0 < c) (hh : 0 < h) (hM : 0 < M)
    (hr : r * Λ ^ 2 ≤ Y * x ^ 2 / 2) (hr' : r * Λ ^ 2 ≤ 1 / 2) (hq : x ^ 2 * |q| ≤ 3 * x)
    (hMc : 3 / 4 * Y ≤ M + c * h) :
    r * (|q| + 9 * c * h) / (M + c * h) ≤ (2 + 9 / 2) / Λ ^ 2 := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hx0, hx1⟩ := hx
  have hMc0 : 0 < M + c * h := lt_of_lt_of_le (by positivity) hMc
  have hΛ0 : 0 < Λ := by linarith
  rw [div_le_iff₀ hMc0, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have k1 : r * Λ ^ 2 * (x ^ 2 * |q|) ≤ Y * x ^ 2 / 2 * (3 * x) :=
    mul_le_mul hr hq (by positivity) (by positivity)
  have k1' : r * |q| * Λ ^ 2 ≤ 3 * x * Y / 2 := by
    have hx2 : 0 < x ^ 2 := by positivity
    have e1 : r * Λ ^ 2 * (x ^ 2 * |q|) = x ^ 2 * (r * |q| * Λ ^ 2) := by ring
    have e2 : Y * x ^ 2 / 2 * (3 * x) = x ^ 2 * (3 * x * Y / 2) := by ring
    rw [e1, e2] at k1
    exact le_of_mul_le_mul_left k1 hx2
  have k2 : r * Λ ^ 2 * (9 * c * h) ≤ 1 / 2 * (9 * c * h) :=
    mul_le_mul_of_nonneg_right hr' (by positivity)
  have hxY : x * Y ≤ Y := mul_le_of_le_one_left hY0.le hx1.le
  have hch : 9 * c * h ≤ 9 * (M + c * h) := by linarith
  have e : r * (|q| + 9 * c * h) * Λ ^ 2 = r * |q| * Λ ^ 2 + r * Λ ^ 2 * (9 * c * h) := by ring
  rw [e]
  nlinarith

/-- The abstract form of the outer-photon bound: the hypotheses are what `x h = x² + (1-x)Λ²`,
`M = Y² + (1-Y)μ²` with `μ ≤ Λ`, and `P = Y x(1-x)/2` give. -/
theorem abs_gForm_outer_le {Λ Y x P c q h M : ℝ} (hΛ : 1 ≤ Λ) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hc : 0 < c) (hcY : c = Y * (1 - Y)) (hM : 0 < M) (hh : 0 < h)
    (hP0 : 0 ≤ P) (hP : P * Λ ^ 2 ≤ Y * x ^ 2 / 2 * h) (hxh1 : 3 / 4 ≤ x * h)
    (hxhΛ : x * h ≤ Λ ^ 2) (hMY : Y ^ 2 ≤ M) (hMΛ : M ≤ Λ ^ 2) (hq : x ^ 2 * |q| ≤ 3 * x) :
    |gForm P c q h M (log (M + c * h)) (log (1 + M / (c * h)))| ≤
      (12 + log Λ + ladderEll Y x) / Λ ^ 2 := by
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨hMc, hup⟩ := outer_mass_bounds hY hx hc hcY hh hxh1 hxhΛ hMY hMΛ
  have hA := abs_log_outer_le hΛ hY hx hMc hup
  obtain ⟨r, rfl⟩ : ∃ r, P = r * h := ⟨P / h, by field_simp⟩
  have hr0 : 0 ≤ r := nonneg_of_mul_nonneg_left hP0 hh
  have hr : r * Λ ^ 2 ≤ Y * x ^ 2 / 2 := by
    have : r * Λ ^ 2 * h ≤ Y * x ^ 2 / 2 * h := by linarith
    exact le_of_mul_le_mul_right this hh
  have hr' : r * Λ ^ 2 ≤ 1 / 2 := by
    have h1 : x ^ 2 ≤ 1 := pow_le_one₀ hx.1.le hx.2.le
    have h2 : Y * x ^ 2 ≤ 1 * 1 := mul_le_mul hY.2.le h1 (sq_nonneg x) zero_le_one
    linarith
  have t1' := outer_first_le hΛ hY hx hc hh hM hr hr' hq hMc
  rw [gForm_eq_phi hM.ne' hh.ne' hc.ne']
  have e : r * h * (c * (q - 9 * c * h) * (M / (c * h) - log (1 + M / (c * h))) / M ^ 2 +
      8 * c * log (1 + M / (c * h)) / M - log (M + c * h) / h) =
      r * h * (c * (q - 9 * c * h) * (M / (c * h) - log (1 + M / (c * h))) / M ^ 2) +
        8 * r * (h * c * log (1 + M / (c * h)) / M) - r * log (M + c * h) := by
    field_simp
  rw [e]
  have t1 := abs_phi_first_le (q := q) hr0 hc hh hM
  obtain ⟨t20, t21⟩ := phi_second_bounds hc hh hM
  have hlY := log_nonpos hY.1.le hY.2.le
  have hlx := log_nonpos hx.1.le hx.2.le
  have hlΛ := log_nonneg hΛ
  have hEll : -log Y - log x ≤ ladderEll Y x := by
    unfold ladderEll
    have : log (1 - Y) ≤ 0 := log_nonpos (by linarith [hY.2]) (by linarith [hY.1])
    have : 0 ≤ log 2 := log_nonneg (by norm_num)
    linarith
  calc |r * h * (c * (q - 9 * c * h) * (M / (c * h) - log (1 + M / (c * h))) / M ^ 2) +
        8 * r * (h * c * log (1 + M / (c * h)) / M) - r * log (M + c * h)|
      ≤ |r * h * (c * (q - 9 * c * h) * (M / (c * h) - log (1 + M / (c * h))) / M ^ 2)| +
        |8 * r * (h * c * log (1 + M / (c * h)) / M)| + |r * log (M + c * h)| :=
        le_trans (abs_sub _ _) (add_le_add_left (abs_add_le _ _) _)
    _ ≤ (2 + 9 / 2) / Λ ^ 2 + 8 * r * 1 + r * (1 + 2 * log Λ - log Y - log x) := by
      gcongr
      · exact t1.trans t1'
      · rw [abs_of_nonneg (by positivity)]; gcongr
      · rw [abs_mul, abs_of_nonneg hr0]; gcongr
    _ ≤ (12 + log Λ + ladderEll Y x) / Λ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have e2 : ((2 + 9 / 2) / Λ ^ 2 + 8 * r * 1 + r * (1 + 2 * log Λ - log Y - log x)) * Λ ^ 2 =
          (2 + 9 / 2) + (r * Λ ^ 2) * (9 + 2 * log Λ - log Y - log x) := by
        field_simp; ring
      rw [e2]
      have : 0 ≤ 9 + 2 * log Λ - log Y - log x := by linarith
      have := mul_le_mul_of_nonneg_right hr' this
      linarith

/-- **The terms with the outer photon at mass `Λ` are `O((1 + log Λ)/Λ²)`**, uniformly in the inner
photon mass `μ ∈ (0, Λ]`: `|G(Λ, μ; Y, x)| ≤ (12 + log Λ + ℓ(Y, x))/Λ²`. -/
theorem abs_ladderGm_outer_le {Λ μ Y x : ℝ} (hΛ : 1 ≤ Λ) (hμ : 0 < μ) (hμΛ : μ ≤ Λ)
    (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |ladderGm Λ μ Y x| ≤ (12 + log Λ + ladderEll Y x) / Λ ^ 2 := by
  have hΛ0 : 0 < Λ := by linarith
  have hY0 := hY.1
  have hY1 := hY.2
  have hx0 := hx.1
  have hx1 := hx.2
  rw [ladderGm_eq_form, ladderQ_eq hx0.ne']
  have hΛ2 : 1 ≤ Λ ^ 2 := by nlinarith
  have hxh : x * (ladderInnerMass 1 Λ x / x) = x ^ 2 + (1 - x) * Λ ^ 2 := by
    unfold ladderInnerMass; field_simp
  refine abs_gForm_outer_le hΛ hY hx (mul_pos hY0 (by linarith)) rfl
    (ladderInnerMass_pos one_pos hμ ⟨hY0.le, hY1.le⟩) (ladderH_pos hΛ0 hx)
    (by have : 0 < 1 - x := by linarith
        positivity) ?_ ?_ ?_ ?_ ?_ (sq_mul_abs_ladderQ_le hY hx)
  · have e : Y * x ^ 2 / 2 * (ladderInnerMass 1 Λ x / x) =
        Y * x / 2 * (x ^ 2 + (1 - x) * Λ ^ 2) := by
      unfold ladderInnerMass; field_simp
    rw [e]
    have : 0 ≤ Y * x / 2 * x ^ 2 := by positivity
    nlinarith
  · rw [hxh]; nlinarith [sq_nonneg (x - 1 / 2), mul_le_mul_of_nonneg_left hΛ2 (by linarith : (0 : ℝ) ≤ 1 - x)]
  · rw [hxh]; nlinarith [mul_le_mul_of_nonneg_left hΛ2 (by linarith : (0 : ℝ) ≤ x)]
  · unfold ladderInnerMass; nlinarith [sq_nonneg μ]
  · unfold ladderInnerMass
    have : μ ^ 2 ≤ Λ ^ 2 := by nlinarith
    nlinarith

/-! ### The term with the inner photon at mass `Λ` -/

/-- **The explicit part of `G(λ, Λ)`** that is removed before the limit `Λ → ∞`: the inner
logarithm `(Y/2) log M_Λ · x²(1-x)/M_λ(x)` (which cancels against the counterterm) and `-T₁` at inner
mass `Λ`, `(Y²(1-Y)/M_Λ) · x(1-x)³/M_λ(x)` (whose integral is `F₂⁽²⁾(Λ) J(λ)`). -/
noncomputable def ladderE1Explicit (lam Lam Y x : ℝ) : ℝ :=
  Y / 2 * log (ladderInnerMass 1 Lam Y) * (x ^ 2 * (1 - x) * 1 ^ 2 / ladderInnerMass 1 lam x) +
    Y ^ 2 * (1 - Y) * 1 ^ 2 / ladderInnerMass 1 Lam Y * (x * (1 - x) ^ 3 / ladderInnerMass 1 lam x)

/-- **The term with the inner photon at mass `Λ`, with the explicit part added back**:
`e₁ = G(λ, Λ) + E(λ, Λ)`. -/
noncomputable def ladderE1 (lam Lam Y x : ℝ) : ℝ :=
  ladderGm lam Lam Y x + ladderE1Explicit lam Lam Y x

/-- The four terms of `e₁`. -/
theorem gForm_add_e1_eq {P c qr qs h M B : ℝ} (hM : 0 < M) (hh : 0 < h) (hc : 0 < c) :
    gForm P c (qr + qs) h M (log (M + c * h)) B + (P * log M / h - P * qs / (h * M)) =
      P * (c * (qr - 9 * c * h) * (M / (c * h) - B) / M ^ 2) - P * c * qs * B / M ^ 2 +
        8 * P * c * B / M - P * log (1 + c * h / M) / h := by
  have e : log (1 + c * h / M) = log (M + c * h) - log M := by
    rw [← log_div (by positivity) hM.ne']
    congr 1
    field_simp
  rw [gForm_eq_phi hM.ne' hh.ne' hc.ne', e]
  field_simp
  ring

/-- `2/s² + (2s + ℓ)/(16 s⁴) + (2s + ℓ)/(4s²) + 1/(32 s²) ≤ 6(1 + ℓ)/s` for `s ≥ 1/2`, `ℓ ≥ 0`. -/
theorem e1_numeric_le {s ℓ : ℝ} (hs : 1 / 2 ≤ s) (hℓ : 0 ≤ ℓ) :
    2 / s ^ 2 + (2 * s + ℓ) / (16 * (s ^ 2) ^ 2) + (2 * s + ℓ) / (4 * s ^ 2) + 1 / (32 * s ^ 2) ≤
      6 * (1 + ℓ) / s := by
  have hs0 : 0 < s := by linarith
  have t : 1 / s ≤ 2 := by rw [div_le_iff₀ hs0]; linarith
  have t0 : 0 < 1 / s := by positivity
  have e1 : 2 / s ^ 2 = 2 * (1 / s) * (1 / s) := by field_simp
  have e2 : (2 * s + ℓ) / (16 * (s ^ 2) ^ 2) =
      (1 / s) ^ 3 / 8 + ℓ * (1 / s) ^ 4 / 16 := by field_simp; ring
  have e3 : (2 * s + ℓ) / (4 * s ^ 2) = (1 / s) / 2 + ℓ * (1 / s) ^ 2 / 4 := by field_simp; ring
  have e4 : 1 / (32 * s ^ 2) = (1 / s) ^ 2 / 32 := by field_simp
  have e5 : 6 * (1 + ℓ) / s = 6 * (1 / s) + 6 * ℓ * (1 / s) := by field_simp
  rw [e1, e2, e3, e4, e5]
  set t' := 1 / s
  have a2 : t' ^ 2 ≤ 2 * t' := by nlinarith
  have a3 : t' ^ 3 ≤ 4 * t' := by nlinarith
  have a4 : t' ^ 4 ≤ 8 * t' := by nlinarith
  have b2 : ℓ * t' ^ 2 ≤ ℓ * (2 * t') := mul_le_mul_of_nonneg_left a2 hℓ
  have b4 : ℓ * t' ^ 4 ≤ ℓ * (8 * t') := mul_le_mul_of_nonneg_left a4 hℓ
  nlinarith

theorem e1_terms_le {P c qr qs h M B : ℝ} (hc : 0 < c) (hcq : c ≤ 1 / 4) (hh : 0 < h)
    (hM : 0 < M) (hP0 : 0 ≤ P) (hP8 : P ≤ 1 / 8) (hPh : P ≤ h / 2) (hqr : |qr| ≤ 2)
    (hPcqs : |P * c * qs| ≤ 1 / 16) (hBdef : B = log (1 + M / (c * h))) :
    |P * (c * (qr - 9 * c * h) * (M / (c * h) - B) / M ^ 2) - P * c * qs * B / M ^ 2 +
        8 * P * c * B / M - P * log (1 + c * h / M) / h| ≤
      2 / M + B / (16 * M ^ 2) + B / (4 * M) + 1 / (32 * M) := by
  have hB0 : 0 ≤ B := hBdef ▸ log_one_add_nonneg (by positivity)
  obtain ⟨r, rfl⟩ : ∃ r, P = r * h := ⟨P / h, by field_simp⟩
  have hr0 : 0 ≤ r := nonneg_of_mul_nonneg_left hP0 hh
  have hr : r ≤ 1 / 2 := by
    have : r * h ≤ 1 / 2 * h := by linarith
    exact le_of_mul_le_mul_right this hh
  -- the first term
  have t1 : |r * h * (c * (qr - 9 * c * h) * (M / (c * h) - B) / M ^ 2)| ≤ 2 / M := by
    rw [hBdef]
    refine (abs_phi_first_le hr0 hc hh hM).trans ?_
    rw [div_le_div_iff₀ (by positivity) hM]
    have k1 : r * |qr| ≤ 1 := by nlinarith [abs_nonneg qr]
    have k2 : r * (9 * c * h) ≤ 9 / 32 := by
      have : r * h * c ≤ 1 / 8 * (1 / 4) := mul_le_mul hP8 hcq hc.le (by norm_num)
      nlinarith
    have k3 : 0 ≤ c * h := by positivity
    nlinarith
  -- the second term
  have t2 : |r * h * c * qs * B / M ^ 2| ≤ B / (16 * M ^ 2) := by
    rw [abs_div, abs_mul, abs_of_nonneg hB0, abs_of_pos (by positivity : 0 < M ^ 2)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_right hPcqs hB0
    nlinarith [sq_nonneg M]
  -- the third term
  have t3 : |8 * (r * h) * c * B / M| ≤ B / (4 * M) := by
    rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    have : r * h * c ≤ 1 / 8 * (1 / 4) := mul_le_mul hP8 hcq hc.le (by norm_num)
    have := mul_le_mul_of_nonneg_right this hB0
    nlinarith
  -- the fourth term
  have t4 : |r * h * log (1 + c * h / M) / h| ≤ 1 / (32 * M) := by
    have hu : 0 ≤ c * h / M := by positivity
    have l0 := log_one_add_nonneg hu
    have l1 := log_one_add_le_self hu
    have e : r * h * log (1 + c * h / M) / h = r * log (1 + c * h / M) := by field_simp
    rw [e, abs_of_nonneg (by positivity)]
    calc r * log (1 + c * h / M) ≤ r * (c * h / M) := by gcongr
      _ = r * h * c / M := by ring
      _ ≤ (1 / 8 * (1 / 4)) / M := by
        gcongr
      _ = 1 / (32 * M) := by field_simp; norm_num
  calc _ ≤ |r * h * (c * (qr - 9 * c * h) * (M / (c * h) - B) / M ^ 2)| +
        |r * h * c * qs * B / M ^ 2| + |8 * (r * h) * c * B / M| +
        |r * h * log (1 + c * h / M) / h| := by
        have := abs_sub (r * h * (c * (qr - 9 * c * h) * (M / (c * h) - B) / M ^ 2) -
          r * h * c * qs * B / M ^ 2 + 8 * (r * h) * c * B / M) (r * h * log (1 + c * h / M) / h)
        have := abs_add_le (r * h * (c * (qr - 9 * c * h) * (M / (c * h) - B) / M ^ 2) -
          r * h * c * qs * B / M ^ 2) (8 * (r * h) * c * B / M)
        have := abs_sub (r * h * (c * (qr - 9 * c * h) * (M / (c * h) - B) / M ^ 2))
          (r * h * c * qs * B / M ^ 2)
        have e : 8 * (r * h) * c * B / M = 8 * (r * h) * c * B / M := rfl
        linarith
    _ ≤ 2 / M + B / (16 * M ^ 2) + B / (4 * M) + 1 / (32 * M) := by linarith

/-- The abstract form of the bound on `e₁`. -/
theorem abs_e1_abstract {P c qr qs h M s ℓ : ℝ} (hc : 0 < c) (hcq : c ≤ 1 / 4) (hh : 0 < h)
    (hMs : M = s ^ 2) (hs : 1 / 2 ≤ s) (hP0 : 0 ≤ P) (hP8 : P ≤ 1 / 8) (hPh : P ≤ h / 2)
    (hqr : |qr| ≤ 2) (hPcqs : |P * c * qs| ≤ 1 / 16) (hB : log (1 + M / (c * h)) ≤ 2 * s + ℓ)
    (hℓ : 0 ≤ ℓ) :
    |gForm P c (qr + qs) h M (log (M + c * h)) (log (1 + M / (c * h))) +
        (P * log M / h - P * qs / (h * M))| ≤ 6 * (1 + ℓ) / s := by
  have hs0 : 0 < s := by linarith
  have hM : 0 < M := by rw [hMs]; positivity
  rw [gForm_add_e1_eq hM hh hc]
  refine (e1_terms_le hc hcq hh hM hP0 hP8 hPh hqr hPcqs rfl).trans ?_
  have hB0 : 0 ≤ log (1 + M / (c * h)) := log_one_add_nonneg (by positivity)
  calc 2 / M + log (1 + M / (c * h)) / (16 * M ^ 2) + log (1 + M / (c * h)) / (4 * M) +
        1 / (32 * M)
      ≤ 2 / M + (2 * s + ℓ) / (16 * M ^ 2) + (2 * s + ℓ) / (4 * M) + 1 / (32 * M) := by
        gcongr
    _ ≤ 6 * (1 + ℓ) / s := by rw [hMs]; exact e1_numeric_le hs hℓ

/-- `log(1 + M/(ch)) ≤ 2√M + ℓ(Y, x)` when `h ≥ x`. -/
theorem log_one_add_div_le {Y x h M : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hxh : x ≤ h) (hM : 0 ≤ M) :
    log (1 + M / (Y * (1 - Y) * h)) ≤ 2 * √M + ladderEll Y x := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hx0, hx1⟩ := hx
  have hc : 0 < Y * (1 - Y) := mul_pos hY0 (by linarith)
  have hcq := c_le_quarter Y
  have hh : 0 < h := hx0.trans_le hxh
  have hch : 0 < Y * (1 - Y) * h := by positivity
  have hcx : 0 < Y * (1 - Y) * x := by positivity
  have h1 : 1 + M / (Y * (1 - Y) * h) ≤ (1 + M) * (1 + 1 / (Y * (1 - Y) * h)) := by
    have : 0 ≤ 1 / (Y * (1 - Y) * h) := by positivity
    have e : (1 + M) * (1 + 1 / (Y * (1 - Y) * h)) =
        1 + M / (Y * (1 - Y) * h) + (M + 1 / (Y * (1 - Y) * h)) := by ring
    rw [e]; linarith
  have h2 : 1 + 1 / (Y * (1 - Y) * h) ≤ 2 / (Y * (1 - Y) * x) := by
    have a1 : 1 / (Y * (1 - Y) * h) ≤ 1 / (Y * (1 - Y) * x) := by gcongr
    have a2 : 1 ≤ 1 / (Y * (1 - Y) * x) := by
      rw [le_div_iff₀ hcx, one_mul]
      calc Y * (1 - Y) * x ≤ 1 / 4 * 1 := by gcongr
        _ ≤ 1 := by norm_num
    calc 1 + 1 / (Y * (1 - Y) * h) ≤ 1 / (Y * (1 - Y) * x) + 1 / (Y * (1 - Y) * x) := by
          linarith
      _ = 2 / (Y * (1 - Y) * x) := by ring
  have h3 : log (1 + M / (Y * (1 - Y) * h)) ≤
      log (1 + M) + log (1 + 1 / (Y * (1 - Y) * h)) := by
    rw [← log_mul (by positivity) (by positivity)]
    exact log_le_log (by positivity) h1
  have h4 : log (1 + M) ≤ 2 * √M := by
    have := log_one_add_sq_le (Real.sqrt_nonneg M)
    rwa [Real.sq_sqrt hM] at this
  have h5 : log (1 + 1 / (Y * (1 - Y) * h)) ≤ ladderEll Y x := by
    have := log_le_log (by positivity) h2
    rw [log_div (by norm_num) hcx.ne', log_mul hc.ne' hx0.ne', log_mul hY0.ne' (by linarith)]
      at this
    unfold ladderEll
    linarith
  linarith

/-- **The bound on `e₁`, uniform in the photon mass**: for `λ > 0`, `Λ ≥ 1` and `0 < Y, x < 1`,
`|e₁(λ, Λ; Y, x)| ≤ 6 (1 + ℓ(Y, x))/√M_Λ(Y)`. -/
theorem abs_ladderE1_le {lam Lam Y x : ℝ} (hlam : 0 < lam) (hLam : 1 ≤ Lam)
    (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |ladderE1 lam Lam Y x| ≤ 6 * (1 + ladderEll Y x) / √(ladderInnerMass 1 Lam Y) := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hx0, hx1⟩ := hx
  have hLam0 : 0 < Lam := by linarith
  have hc : 0 < Y * (1 - Y) := mul_pos hY0 (by linarith)
  have hM := ladderInnerMass_pos one_pos hLam0 ⟨hY0.le, hY1.le⟩
  have hMx := ladderInnerMass_pos one_pos hlam ⟨hx0.le, hx1.le⟩
  have hh := ladderH_pos hlam ⟨hx0, hx1⟩
  have hx2M : x ^ 2 ≤ ladderInnerMass 1 lam x := by
    unfold ladderInnerMass
    have : 0 ≤ (1 - x) * lam ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  have hM4 : 1 / 4 ≤ ladderInnerMass 1 Lam Y := by
    unfold ladderInnerMass
    have : (1 - Y) * 1 ≤ (1 - Y) * Lam ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    nlinarith [sq_nonneg (Y - 1 / 2)]
  have hs : 1 / 2 ≤ √(ladderInnerMass 1 Lam Y) := by
    have := Real.sqrt_le_sqrt hM4
    rwa [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
  have hE : ladderE1Explicit lam Lam Y x =
      Y * x * (1 - x) / 2 * log (ladderInnerMass 1 Lam Y) / (ladderInnerMass 1 lam x / x) -
        Y * x * (1 - x) / 2 * ladderQs Y x /
          ((ladderInnerMass 1 lam x / x) * ladderInnerMass 1 Lam Y) := by
    unfold ladderE1Explicit ladderQs
    field_simp
    ring
  unfold ladderE1
  rw [ladderGm_eq_form, ladderQ_eq hx0.ne', hE]
  refine abs_e1_abstract hc (c_le_quarter Y) hh (Real.sq_sqrt hM.le).symm hs
    (by have : 0 < 1 - x := by linarith
        positivity) ?_ ?_ (abs_ladderQr_le ⟨hY0, hY1⟩ ⟨hx0, hx1⟩) ?_
    (log_one_add_div_le ⟨hY0, hY1⟩ ⟨hx0, hx1⟩ ?_ hM.le) (ladderEll_nonneg ⟨hY0, hY1⟩ ⟨hx0, hx1⟩)
  · have : x * (1 - x) ≤ 1 / 4 := c_le_quarter x
    have : Y * (x * (1 - x)) ≤ 1 * (1 / 4) :=
      mul_le_mul hY1.le this (by nlinarith) zero_le_one
    nlinarith
  · rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), div_mul_cancel₀ _ (two_ne_zero),
      le_div_iff₀ hx0]
    have : Y * x ^ 2 * (1 - x) ≤ x ^ 2 := by
      have : Y * (1 - x) ≤ 1 := by nlinarith
      nlinarith [sq_nonneg x]
    nlinarith
  · have e : Y * x * (1 - x) / 2 * (Y * (1 - Y)) * ladderQs Y x =
        -(Y * (Y * (1 - Y)) ^ 2 * (1 - x) ^ 3) := by
      unfold ladderQs; field_simp
    rw [e, abs_neg, abs_of_nonneg (by have : 0 < 1 - x := by linarith
                                      positivity)]
    have hcq := c_le_quarter Y
    have h1 : (1 - x) ^ 3 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have h2 : (Y * (1 - Y)) ^ 2 ≤ 1 / 16 := by nlinarith
    have h3 : Y * (1 - x) ^ 3 ≤ 1 := by nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - x) 3]
    nlinarith [sq_nonneg (Y * (1 - Y)), pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - x) 3]
  · rw [le_div_iff₀ hx0]; nlinarith

end QED.TwoLoop.UnitLLink

end
