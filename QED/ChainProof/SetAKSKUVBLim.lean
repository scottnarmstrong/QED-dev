/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUVBDec

/-!
# Set (a), stage D: the pointwise large-cutoff limits of the `VB` pieces

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification), step D3 (the photon-mass integral of the `VB` class). The
elementary limits, as the cutoff `Λ → ∞`, of the pieces of the split `ksU_ksUDB_split`:

* `ksU_tendsto_J1_zero`: `J1₀(A, b₀ + Λ/ρ, Y) → 0`;
* `ksU_tendsto_log_sub`: `log(1 + Λa) - log Λ → log a`;
* `ksU_tendsto_log_ratio`: `log((1 + Λa)/(1 + Λb)) → log(a/b)`;
* `ksU_tendsto_K_sub`: `K((t + Λ)a) - (log Λ)²/2 - log a log Λ → (log a)²/2 + 2K(1)`.
-/

@[expose] public section

open Filter Topology MeasureTheory Set

namespace QED.ChainProof.SetAKS

theorem ksU_J1_zero_le {A b Y : ℝ} (hA : 0 < A) (hb : 0 < b) (hY : 0 ≤ Y) :
    ksDJ1 A b Y 0 ≤ 2 * Real.sqrt (Y / A) * (Real.sqrt b)⁻¹ := by
  simp only [ksDJ1]
  have e : (A + b * Y) / A = 1 + b * Y / A := by field_simp
  rw [e]
  have hl := ksU_log_one_add_le (by positivity : 0 ≤ b * Y / A)
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have e2 : Real.sqrt (b * Y / A) = Real.sqrt b * Real.sqrt (Y / A) := by
    rw [mul_div_assoc, Real.sqrt_mul hb.le]
  rw [e2] at hl
  rw [div_le_iff₀ hb]
  have hbb : b = Real.sqrt b * Real.sqrt b := (Real.mul_self_sqrt hb.le).symm
  calc Real.log (1 + b * Y / A) ≤ 2 * (Real.sqrt b * Real.sqrt (Y / A)) := hl
    _ = 2 * Real.sqrt (Y / A) * (Real.sqrt b)⁻¹ * (Real.sqrt b * Real.sqrt b) := by
      field_simp
    _ = _ := by rw [← hbb]

theorem ksU_tendsto_J1_zero {A Y b₀ ρ : ℝ} (hA : 0 < A) (hY : 0 ≤ Y) (hb₀ : 0 < b₀)
    (hρ : 0 < ρ) : Tendsto (fun Λ => ksDJ1 A (b₀ + Λ / ρ) Y 0) atTop (𝓝 0) := by
  have hb : Tendsto (fun Λ : ℝ => b₀ + Λ / ρ) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_div_const hρ)
  have hs : Tendsto (fun Λ : ℝ => 2 * Real.sqrt (Y / A) * (Real.sqrt (b₀ + Λ / ρ))⁻¹) atTop
      (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hb)).const_mul
      (2 * Real.sqrt (Y / A))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with Λ hΛ
    exact ksU_J1_nonneg hA (by have := div_nonneg hΛ hρ.le; linarith) hY 0
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with Λ hΛ
    exact ksU_J1_zero_le hA (by have := div_nonneg hΛ hρ.le; linarith) hY

theorem ksU_tendsto_log_sub {a : ℝ} (ha : 0 < a) :
    Tendsto (fun Λ => Real.log (1 + Λ * a) - Real.log Λ) atTop (𝓝 (Real.log a)) := by
  have h : Tendsto (fun Λ : ℝ => Real.log (Λ⁻¹ + a)) atTop (𝓝 (Real.log a)) := by
    have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).add_const a
    rw [zero_add] at this
    exact ((Real.continuousAt_log ha.ne').tendsto).comp this
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
  rw [← Real.log_div (by positivity) hΛ.ne']
  congr 1
  field_simp

theorem ksU_tendsto_log_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun Λ => Real.log ((1 + Λ * a) / (1 + Λ * b))) atTop (𝓝 (Real.log (a / b))) := by
  have h : Tendsto (fun Λ : ℝ => Real.log ((Λ⁻¹ + a) / (Λ⁻¹ + b))) atTop
      (𝓝 (Real.log (a / b))) := by
    have h1 := (tendsto_inv_atTop_zero (𝕜 := ℝ)).add_const a
    have h2 := (tendsto_inv_atTop_zero (𝕜 := ℝ)).add_const b
    rw [zero_add] at h1 h2
    exact ((Real.continuousAt_log (div_pos ha hb).ne').tendsto).comp (h1.div h2 hb.ne')
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
  congr 1
  field_simp

theorem ksU_ksUK_mono {z₁ z₂ : ℝ} (h0 : 0 ≤ z₁) (h : z₁ ≤ z₂) : ksUK z₁ ≤ ksUK z₂ := by
  unfold ksUK
  have e := intervalIntegral.integral_interval_sub_left
    (ksU_intervalIntegrable_ksUKer (h0.trans h)) (ksU_intervalIntegrable_ksUKer h0)
  have : 0 ≤ ∫ t in z₁..z₂, ksUKer t :=
    intervalIntegral.integral_nonneg h fun t ht => ksU_ksUKer_nonneg (h0.trans ht.1)
  linarith

/-- **The dilogarithm at large argument**: for `a > 0`, `t ≥ 0`,
`K((t + Λ)a) - (log Λ)²/2 - log a log Λ → (log a)²/2 + 2K(1)`. -/
theorem ksU_tendsto_K_sub {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    Tendsto (fun Λ => ksUK ((t + Λ) * a) - Real.log Λ ^ 2 / 2 - Real.log a * Real.log Λ)
      atTop (𝓝 (Real.log a ^ 2 / 2 + 2 * ksUK 1)) := by
  set η : ℝ → ℝ := fun Λ => Real.log (1 + t / Λ) with hη
  have hη0 : Tendsto η atTop (𝓝 0) := by
    have h := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul t).const_add 1
    simp only [mul_zero, add_zero] at h
    have := ((Real.continuousAt_log one_ne_zero).tendsto).comp h
    rw [Real.log_one] at this
    refine this.congr' (Eventually.of_forall fun Λ => ?_)
    simp [hη, div_eq_mul_inv]
  have hηL : Tendsto (fun Λ => η Λ * Real.log Λ) atTop (𝓝 0) := by
    have hL := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).const_mul t
    simp only [pow_one, one_mul, add_zero, mul_zero] at hL
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hL ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with Λ hΛ
      have h1 : 0 ≤ t / Λ := div_nonneg ht (by linarith)
      exact mul_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg hΛ)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with Λ hΛ
      have hl : η Λ ≤ t / Λ := by
        have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + t / Λ)
        simp only [hη]; linarith
      have hL0 := Real.log_nonneg hΛ
      calc η Λ * Real.log Λ ≤ t / Λ * Real.log Λ := mul_le_mul_of_nonneg_right hl hL0
        _ = t * (Real.log Λ / Λ) := by ring
  have hz : Tendsto (fun Λ => ((t + Λ) * a)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Tendsto.atTop_mul_const ha
      (tendsto_atTop_add_const_left _ _ tendsto_id))
  have hKz : Tendsto (fun Λ => ksUK ((t + Λ) * a)⁻¹) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hz ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
      exact ksU_ksUK_nonneg (by positivity)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
      exact ksU_ksUK_le (by positivity)
  have hlim : Tendsto (fun Λ => Real.log a ^ 2 / 2 + η Λ * Real.log Λ + Real.log a * η Λ +
      η Λ ^ 2 / 2 + 2 * ksUK 1 - ksUK ((t + Λ) * a)⁻¹) atTop
      (𝓝 (Real.log a ^ 2 / 2 + 0 + Real.log a * 0 + 0 ^ 2 / 2 + 2 * ksUK 1 - 0)) :=
    (((((tendsto_const_nhds.add hηL).add (hη0.const_mul _)).add
      ((hη0.pow 2).div_const 2)).add tendsto_const_nhds).sub hKz)
  simp only [add_zero, mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
  have hz0 : 0 < (t + Λ) * a := by positivity
  have hinv := ksU_ksUK_inv hz0
  have hlog : Real.log ((t + Λ) * a) = Real.log Λ + Real.log a + η Λ := by
    simp only [hη]
    rw [show (t + Λ) * a = Λ * a * (1 + t / Λ) by field_simp; ring,
      Real.log_mul (by positivity) (by positivity), Real.log_mul hΛ.ne' ha.ne']
  rw [hlog] at hinv
  linarith [hinv]

end QED.ChainProof.SetAKS

end
