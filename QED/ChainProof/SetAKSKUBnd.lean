/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUElem

/-!
# Set (a), stage D: sign splitting and a global bound for the `VA` antiderivative

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification), step D3 (the photon-mass integral). The interchange of the
photon-mass integral with the node integrals of the `VA` class is done by Tonelli on the two
sign-definite pieces of `ksDLin`, and needs a bound on the antiderivative `ksUPhi` that is
integrable over the nodes. This file provides:

* `ksU_ksDLin_split`: `ksDLin A b Y a₀ a₁ = a₀ ksDLin A b Y 1 0 + a₁ ksDLin A b Y 0 1`;
* `ksU_ksDLin_nonneg`: `ksDLin ≥ 0` for `a₀, a₁ ≥ 0` (its integrand is nonnegative);
* `ksU_ksUK_le_log`: `K z ≤ log(1 + z)²/2 + 2` for `z ≥ 0`;
* **`ksU_abs_ksUPhi_le`**: for `A > 0`, `0 < Y ≤ 1`, `b > 0`,
  `|ksUPhi A b Y a₀ a₁| ≤ 10 (|a₀| + |a₁|) W² (1 + log(1 + b))²`, `W = 2 + A + A⁻¹`;
* `ksU_one_add_log_sq_le`: `(1 + log(1 + b))² ≤ 16(1 + √b)`.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral

namespace QED.ChainProof.SetAKS

theorem ksU_ksDLin_split (A b Y a₀ a₁ : ℝ) :
    ksDLin A b Y a₀ a₁ = a₀ * ksDLin A b Y 1 0 + a₁ * ksDLin A b Y 0 1 := by
  simp only [ksDLin]
  ring

theorem ksU_ksDLin_nonneg {A b Y a₀ a₁ : ℝ} (hA : 0 < A) (hb : 0 < b) (hY : 0 ≤ Y)
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) : 0 ≤ ksDLin A b Y a₀ a₁ := by
  rw [← ksD_integral_lin a₀ a₁ hA hb hY]
  refine intervalIntegral.integral_nonneg hY fun r hr => ?_
  have hD := ksD_den_pos hA hb hr.2
  exact mul_nonneg hr.1 (add_nonneg (div_nonneg ha₀ (by positivity))
    (div_nonneg (by positivity) hD.le))

theorem ksU_ksUK_one_le : ksUK 1 ≤ 1 := by simpa using ksU_ksUK_le zero_le_one

theorem ksU_ksUK_le_log {z : ℝ} (hz : 0 ≤ z) : ksUK z ≤ Real.log (1 + z) ^ 2 / 2 + 2 := by
  have hsq : 0 ≤ Real.log (1 + z) ^ 2 / 2 := by positivity
  rcases le_or_gt z 1 with h | h
  · linarith [ksU_ksUK_le hz]
  · have hz0 : 0 < z := by linarith
    have hinv := ksU_ksUK_inv hz0
    have hK0 := ksU_ksUK_nonneg (inv_pos.2 hz0).le
    have hl0 : 0 ≤ Real.log z := Real.log_nonneg h.le
    have hl1 : Real.log z ≤ Real.log (1 + z) := Real.log_le_log hz0 (by linarith)
    have : Real.log z ^ 2 ≤ Real.log (1 + z) ^ 2 := pow_le_pow_left₀ hl0 hl1 2
    linarith [ksU_ksUK_one_le]

/-- The arithmetic of the final constant in `ksU_abs_ksUPhi_le` (`w = W(1 + λ)`). -/
theorem ksU_bound_aux2 {a c Ai W lam : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hAi : 0 ≤ Ai)
    (hAW : Ai ≤ W) (hW : 2 ≤ W) (hlam : 0 ≤ lam) :
    a * (Ai + Ai * (W + lam)) + 2 * c * (1 + (W + lam) + (W + lam) ^ 2 / 2 + 2) ≤
      10 * (a + c) * W ^ 2 * (1 + lam) ^ 2 := by
  set w := W * (1 + lam) with hw
  have hw2 : 2 ≤ w := by nlinarith
  have hWl : W + lam ≤ w := by nlinarith
  have hWw : W ≤ w := by nlinarith
  have hWl0 : 0 ≤ W + lam := by linarith
  have h1 : Ai + Ai * (W + lam) ≤ W + W * w := by
    have := mul_le_mul hAW hWl hWl0 (by linarith)
    linarith
  have h2 : W + W * w ≤ 10 * w ^ 2 := by nlinarith
  have h3 : 1 + (W + lam) + (W + lam) ^ 2 / 2 + 2 ≤ 5 * w ^ 2 := by
    have : (W + lam) ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ hWl0 hWl 2
    nlinarith
  have hfin : 10 * (a + c) * W ^ 2 * (1 + lam) ^ 2 = 10 * a * w ^ 2 + 10 * c * w ^ 2 := by
    rw [hw]
    ring
  rw [hfin]
  have := mul_le_mul_of_nonneg_left (h1.trans h2) ha
  have := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 2 * c)
  nlinarith

/-- **A global bound for the `VA` antiderivative**: for `A > 0`, `0 < Y ≤ 1`, `b > 0`,
`|ksUPhi A b Y a₀ a₁| ≤ 10 (|a₀| + |a₁|) W² (1 + log(1 + b))²` with `W = 2 + A + A⁻¹`. -/
theorem ksU_abs_ksUPhi_le {A b Y : ℝ} (a₀ a₁ : ℝ) (hA : 0 < A) (hb : 0 < b) (hY : 0 < Y)
    (hY1 : Y ≤ 1) :
    |ksUPhi A b Y a₀ a₁| ≤
      10 * (|a₀| + |a₁|) * (2 + A + A⁻¹) ^ 2 * (1 + Real.log (1 + b)) ^ 2 := by
  set W := 2 + A + A⁻¹ with hW
  set lam := Real.log (1 + b) with hlam
  have hAi : 0 < A⁻¹ := inv_pos.2 hA
  have hlam0 : 0 ≤ lam := Real.log_nonneg (by linarith)
  have hP : 0 < A + b * Y := by positivity
  set L := Real.log ((A + b * Y) / A) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hA]; nlinarith)
  have hLle : L ≤ b * Y / A := by
    have h := Real.log_le_sub_one_of_pos (div_pos hP hA)
    have : (A + b * Y) / A - 1 = b * Y / A := by field_simp; ring
    linarith
  -- `L/b ≤ A⁻¹` and `A L / b ≤ 1`
  have hLb : L / b ≤ A⁻¹ := by
    rw [div_le_iff₀ hb]
    have : b * Y / A ≤ A⁻¹ * b := by
      rw [div_le_iff₀ hA]
      have : A⁻¹ * b * A = b := by field_simp
      rw [this]
      nlinarith
    linarith
  have hALb : A * L / b ≤ 1 := by
    rw [div_le_iff₀ hb]
    have : A * (b * Y / A) = b * Y := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hLle hA.le]
  -- `|log(A + bY)| ≤ W + λ`
  have hlogA : -A⁻¹ ≤ Real.log A := by
    have := Real.log_le_sub_one_of_pos hAi
    rw [Real.log_inv] at this
    linarith
  have hlogA' : Real.log A ≤ A := by linarith [Real.log_le_sub_one_of_pos hA]
  have hup : Real.log (A + b * Y) ≤ Real.log (A + 1) + lam := by
    rw [hlam, ← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_le_log hP (by nlinarith [mul_le_mul_of_nonneg_left hY1 hb.le])
  have hA1 : Real.log (A + 1) ≤ A := by linarith [Real.log_le_sub_one_of_pos (by linarith :
    (0 : ℝ) < A + 1)]
  have hlogP : |Real.log (A + b * Y)| ≤ W + lam := by
    have hlo : Real.log A ≤ Real.log (A + b * Y) :=
      Real.log_le_log hA (by nlinarith [mul_pos hb hY])
    rw [abs_le]
    constructor <;> linarith
  -- `K(bY/A) ≤ (W + λ)²/2 + 2`
  have hz0 : 0 ≤ b * Y / A := by positivity
  have hK := ksU_ksUK_le_log hz0
  have hK0 := ksU_ksUK_nonneg hz0
  have hLeq : Real.log (1 + b * Y / A) = L := by
    rw [hL]
    congr 1
    field_simp
  rw [hLeq] at hK
  have hLW : L ≤ W + lam := by
    have : L = Real.log (A + b * Y) - Real.log A := by
      rw [hL, Real.log_div hP.ne' hA.ne']
    rw [this]
    linarith
  have hKW : ksUK (b * Y / A) ≤ (W + lam) ^ 2 / 2 + 2 := by
    have : L ^ 2 ≤ (W + lam) ^ 2 := pow_le_pow_left₀ hL0 hLW 2
    linarith
  -- the two brackets
  have hYA : Y / A ≤ A⁻¹ := by
    rw [div_eq_mul_inv]
    nlinarith
  have hB₀ : |L / b + Y / A * Real.log (A + b * Y)| ≤ A⁻¹ + A⁻¹ * (W + lam) := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_of_nonneg (div_nonneg hL0 hb.le)]
      exact hLb
    · rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul hYA hlogP (abs_nonneg _) hAi.le
  have hB₁ : |-(A * L / b) - Y * Real.log (A + b * Y) + Y * ksUK (b * Y / A)| ≤
      1 + (W + lam) + (W + lam) ^ 2 / 2 + 2 := by
    have h1 : |A * L / b| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; exact hALb
    have h2 : |Y * Real.log (A + b * Y)| ≤ W + lam := by
      rw [abs_mul, abs_of_pos hY]
      nlinarith [abs_nonneg (Real.log (A + b * Y))]
    have h3 : |Y * ksUK (b * Y / A)| ≤ (W + lam) ^ 2 / 2 + 2 := by
      rw [abs_mul, abs_of_pos hY, abs_of_nonneg hK0]
      nlinarith
    calc |-(A * L / b) - Y * Real.log (A + b * Y) + Y * ksUK (b * Y / A)|
        ≤ |A * L / b| + |Y * Real.log (A + b * Y)| + |Y * ksUK (b * Y / A)| := by
          refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
          refine (abs_sub _ _).trans (add_le_add_left ?_ _)
          rw [abs_neg]
      _ ≤ 1 + (W + lam) + ((W + lam) ^ 2 / 2 + 2) := add_le_add (add_le_add h1 h2) h3
      _ = 1 + (W + lam) + (W + lam) ^ 2 / 2 + 2 := by ring
  have hsplit : |ksUPhi A b Y a₀ a₁| ≤
      |a₀| * (A⁻¹ + A⁻¹ * (W + lam)) + 2 * |a₁| * (1 + (W + lam) + (W + lam) ^ 2 / 2 + 2) := by
    simp only [ksUPhi]
    rw [← hL]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hB₀ (abs_nonneg _)
    · rw [abs_mul, abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left hB₁ (by positivity)
  exact hsplit.trans (ksU_bound_aux2 (abs_nonneg _) (abs_nonneg _) hAi.le
    (by rw [hW]; linarith) (by rw [hW]; linarith) hlam0)

/-- `(1 + log(1 + b))² ≤ 16(1 + √b)` for `b ≥ 0`: the node bound of `ksU_abs_ksUPhi_le` is
dominated by square roots (integrable against `x^{-1/2}`, `(1 - x)^{-1/2}` on the nodes). -/
theorem ksU_one_add_log_sq_le {b : ℝ} (hb : 0 ≤ b) :
    (1 + Real.log (1 + b)) ^ 2 ≤ 16 * (1 + Real.sqrt b) := by
  have hy : 0 < 1 + b := by linarith
  set q := Real.sqrt (Real.sqrt (1 + b)) with hq
  have hsy : 1 ≤ Real.sqrt (1 + b) := by simpa using Real.sqrt_le_sqrt (by linarith : 1 ≤ 1 + b)
  have hq1 : 1 ≤ q := by
    rw [hq, Real.le_sqrt zero_le_one (Real.sqrt_nonneg _), one_pow]
    exact hsy
  have hlog : Real.log (1 + b) = 4 * Real.log q := by
    rw [hq, Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hy.le]
    ring
  have hlq := Real.log_le_sub_one_of_pos (by linarith : 0 < q)
  have hl0 : 0 ≤ Real.log (1 + b) := Real.log_nonneg (by linarith)
  have hq2 : q ^ 2 = Real.sqrt (1 + b) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have h1 : (1 + Real.log (1 + b)) ^ 2 ≤ 16 * q ^ 2 := by nlinarith
  have h2 : Real.sqrt (1 + b) ≤ 1 + Real.sqrt b := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hb, Real.sqrt_nonneg b]
  rw [hq2] at h1
  linarith

end QED.ChainProof.SetAKS

end
