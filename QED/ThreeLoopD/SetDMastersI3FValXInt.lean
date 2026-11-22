/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.LogLiDiv
public import QED.Polylog.LogLogSq
public import QED.Polylog.LiLimits
public import QED.TwoLoop.UnitXCloseDilog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import QED.Polylog.LiCalculus
import QED.Polylog.ExtraIntegrals

/-!
# Set (d), master `I₃`: weight-four integrals and the Landen identity for `dilogI`

Ingredients of the last integration of `i3FInt 0`:

* `∫₀¹ log (1 - x) Li₂ x / x = -π⁴/72`, with antiderivative `-Li₂(x)²/2`;
* `∫₀¹ log³ (1 - x) / x = -6 ζ(4) = -π⁴/15`, with antiderivative
  `log³ (1 - x) log x + 3 log² (1 - x) Li₂ (1 - x) + 6 (Li₄ (1 - x) - log (1 - x) Li₃ (1 - x))`;
* `∫₀¹ F = π⁴/30` for `F(x) = (log x - log (1 - x)) (Li₂ x + log² (1 - x)/2)/x`, from these and
  `∫₀¹ log x Li₂ x / x = -π⁴/90`, `∫₀¹ log x log² (1 - x) / x = -π⁴/180`;
* Landen's identity `dilogI (-x/(1 - x)) = -dilogI x - log² (1 - x)/2` on `(0, 1)`.

Each integrand has constant sign, so integrability comes with the value
(`QED.Polylog.intervalIntegrable_and_integral_eq_of_nonneg'`).

## Main results

* `QED.ThreeLoopD.i3X_integral_log_one_sub_mul_Li_two_div`
* `QED.ThreeLoopD.i3X_integral_log_one_sub_cube_div`
* `QED.ThreeLoopD.i3X_integral_F`: `∫₀¹ F = π⁴/30`.
* `QED.ThreeLoopD.i3X_dilogI_landen`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology
open QED.Polylog QED.TwoLoop.UnitXClose

namespace QED.ThreeLoopD

/-! ### `∫₀¹ log (1 - x) Li₂ x / x` -/

theorem i3X_integral_log_one_sub_mul_Li_two_div :
    IntervalIntegrable (fun x => log (1 - x) * Li 2 x / x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, log (1 - x) * Li 2 x / x = -(π ^ 4 / 72) := by
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun y => -(Li 2 y ^ 2 / 2))
      (log (1 - x) * Li 2 x / x) x := by
    intro x hx
    have h1 : |x| < 1 := by rw [abs_of_pos hx.1]; exact hx.2
    have h := hasDerivAt_Li_two_comp (hasDerivAt_id' x) h1 hx.1.ne'
    have := ((h.pow 2).div_const 2).neg
    refine this.congr_deriv ?_
    field_simp
    ring
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1, log (1 - x) * Li 2 x / x ≤ 0 := by
    intro x hx
    have hl : log (1 - x) < 0 := log_neg (by linarith [hx.2]) (by linarith [hx.1])
    have hL : 0 ≤ Li 2 x := Li₂_nonneg hx.1.le
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hl.le hL) hx.1.le
  have hs : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact ⟨by linarith [hx.1], hx.2.le⟩
  have hs' : ∀ᶠ x in 𝓝[<] (1 : ℝ), x ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact ⟨by linarith [hx.1], hx.2.le⟩
  have h0 : Tendsto (fun y => -(Li 2 y ^ 2 / 2)) (𝓝[>] 0) (𝓝 (-(Li 2 0 ^ 2 / 2))) :=
    (((tendsto_Li_comp (le_refl 2) (by norm_num)
      ((continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds) hs).pow 2).div_const 2).neg
  have h1 : Tendsto (fun y => -(Li 2 y ^ 2 / 2)) (𝓝[<] 1) (𝓝 (-(Li 2 1 ^ 2 / 2))) :=
    (((tendsto_Li_comp (le_refl 2) (by norm_num)
      ((continuous_id.tendsto 1).mono_left nhdsWithin_le_nhds) hs').pow 2).div_const 2).neg
  obtain ⟨hi, hv⟩ := intervalIntegrable_and_integral_eq_of_nonpos' one_pos hd hf h0 h1
  refine ⟨hi, ?_⟩
  rw [hv, Li_zero, Li_two, Li₂_one]
  ring

/-! ### `∫₀¹ log³ (1 - x) / x` -/

theorem i3X_tendsto_mul_log_cube : Tendsto (fun s : ℝ => s * log s ^ 3) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_log_mul_rpow_nhdsGT_zero (r := 1 / 3) (by norm_num)).pow 3
  rw [zero_pow (by norm_num)] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  rw [mul_pow, ← Real.rpow_natCast (s ^ (1 / 3 : ℝ)), ← Real.rpow_mul hs.le]
  norm_num
  ring

theorem i3X_tendsto_log_one_sub_mul_log :
    Tendsto (fun t : ℝ => log (1 - t) * log t) (𝓝[>] 0) (𝓝 0) := by
  have hm : Tendsto (fun t : ℝ => 2 * |t * log t|) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_mul_log_comp ((continuous_id.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0)))).abs.const_mul 2)
  refine squeeze_zero_norm' ?_ hm
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with t ht
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos ht.1]
  have := abs_log_one_sub_le ht.1.le ht.2.le
  calc |log (1 - t)| * |log t| ≤ 2 * t * |log t| :=
        mul_le_mul_of_nonneg_right this (abs_nonneg _)
    _ = 2 * (t * |log t|) := by ring

/-- The antiderivative of `log³ (1 - x) / x`. -/
noncomputable def i3XQ (t : ℝ) : ℝ :=
  log (1 - t) ^ 3 * log t + 3 * (log (1 - t) ^ 2 * Li 2 (1 - t)) +
    6 * (Li 4 (1 - t) - log (1 - t) * Li 3 (1 - t))

theorem i3X_integral_log_one_sub_cube_div :
    IntervalIntegrable (fun x => log (1 - x) ^ 3 / x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, log (1 - x) ^ 3 / x = -(π ^ 4 / 15) := by
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt i3XQ (log (1 - x) ^ 3 / x) x := by
    intro x hx
    obtain ⟨h0, h1⟩ := hx
    have hy : 0 < 1 - x := by linarith
    have hf : HasDerivAt (fun y => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id' x).const_sub 1
    have ha : |1 - x| < 1 := by rw [abs_of_pos hy]; linarith
    have hL := hf.log hy.ne'
    have h2 := hasDerivAt_Li_two_comp hf ha hy.ne'
    have h4 := hasDerivAt_Li_four_sub_comp hf ha hy.ne'
    have hlx := hasDerivAt_log h0.ne'
    have := ((hL.pow 3).mul hlx).add (((hL.pow 2).mul h2).const_mul 3) |>.add (h4.const_mul 6)
    refine this.congr_deriv ?_
    simp only [Pi.pow_apply]
    rw [show 1 - (1 - x) = x by ring]
    field_simp
    ring
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1, log (1 - x) ^ 3 / x ≤ 0 := by
    intro x hx
    have hl : log (1 - x) < 0 := log_neg (by linarith [hx.2]) (by linarith [hx.1])
    have : log (1 - x) ^ 3 ≤ 0 := by
      have := pow_pos (neg_pos.2 hl) 3
      nlinarith [this]
    exact div_nonpos_of_nonpos_of_nonneg this hx.1.le
  -- the limit at `0⁺`
  have hl0 : Tendsto (fun t : ℝ => log (1 - t)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => log (1 - t)) 0 :=
      (continuousAt_const.sub continuousAt_id).log (by norm_num)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hone : Tendsto (fun t : ℝ => 1 - t) (𝓝[>] 0) (𝓝 1) := by
    have hc : ContinuousAt (fun t : ℝ => 1 - t) 0 := continuousAt_const.sub continuousAt_id
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hs0 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 1 - t ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hA : Tendsto i3XQ (𝓝[>] 0) (𝓝 (π ^ 4 / 15)) := by
    have e1 := (hl0.pow 2).mul i3X_tendsto_log_one_sub_mul_log
    have e2 := ((hl0.pow 2).mul (tendsto_Li_comp (le_refl 2) (by norm_num) hone hs0)).const_mul 3
    have e3 := (tendsto_Li_sub_log_mul_Li_comp (k := 4) (j := 3) (by norm_num) (by norm_num)
      (by norm_num) one_ne_zero hone hs0).const_mul 6
    have := (e1.add e2).add e3
    rw [log_one, Li_four_one] at this
    convert this using 2
    · simp only [i3XQ]; ring
    · ring
  -- the limit at `1⁻`
  have hT := tendsto_one_sub_nhdsLT_one
  have hT0 : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] 1) (𝓝 0) := hT.mono_right nhdsWithin_le_nhds
  have hs1 : ∀ᶠ t in 𝓝[<] (1 : ℝ), 1 - t ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hB : Tendsto i3XQ (𝓝[<] 1) (𝓝 0) := by
    have c1 : Tendsto (fun s : ℝ => log s ^ 3 * log (1 - s)) (𝓝[>] 0) (𝓝 0) := by
      have hm := (i3X_tendsto_mul_log_cube.abs).const_mul 2
      rw [abs_zero, mul_zero] at hm
      refine squeeze_zero_norm' ?_ hm
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with s hs
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hs.1]
      have := abs_log_one_sub_le hs.1.le hs.2.le
      calc |log s ^ 3| * |log (1 - s)| ≤ |log s ^ 3| * (2 * s) :=
            mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = 2 * (s * |log s ^ 3|) := by ring
    have c2 : Tendsto (fun s : ℝ => Li 2 s * log s ^ 2) (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_mul_log_sq_of_abs_le (C := π ^ 2 / 6) ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
      have := abs_Li_le (k := 2) le_rfl (show |s| ≤ 1 by rw [abs_of_pos hs.1]; exact hs.2.le)
      rwa [abs_of_pos hs.1] at this
    have c3 := tendsto_Li_sub_log_mul_Li_comp_zero (k := 4) (j := 3) (by norm_num) (by norm_num)
      hT0 hs1
    have := ((c1.comp hT).add ((c2.comp hT).const_mul 3)).add (c3.const_mul 6)
    simp only [mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards with t
    simp only [Function.comp, i3XQ, sub_sub_cancel]
    ring
  obtain ⟨hi, hv⟩ := intervalIntegrable_and_integral_eq_of_nonpos' one_pos hd hf hA hB
  exact ⟨hi, by rw [hv]; ring⟩

/-! ### `∫₀¹ F` -/

/-- `F(x) = (log x - log (1 - x)) (Li₂ x + log² (1 - x)/2) / x`. -/
noncomputable def i3XF (x : ℝ) : ℝ := (log x - log (1 - x)) * (Li 2 x + log (1 - x) ^ 2 / 2) / x

theorem i3X_integral_F :
    IntervalIntegrable i3XF volume 0 1 ∧ ∫ x in (0 : ℝ)..1, i3XF x = π ^ 4 / 30 := by
  obtain ⟨i1, v1⟩ := intervalIntegrable_and_integral_log_mul_Li_two_div
  obtain ⟨i2, v2⟩ := i3X_integral_log_one_sub_mul_Li_two_div
  obtain ⟨i3, v3⟩ := intervalIntegrable_and_integral_log_mul_log_one_sub_sq_div
  obtain ⟨i4, v4⟩ := i3X_integral_log_one_sub_cube_div
  have e : i3XF = fun x => log x * Li 2 x / x - log (1 - x) * Li 2 x / x +
      (1 / 2) * (log x * log (1 - x) ^ 2 / x) - (1 / 2) * (log (1 - x) ^ 3 / x) := by
    funext x
    simp only [i3XF]
    ring
  have i12 := i1.sub i2
  have i123 := i12.add (i3.const_mul (1 / 2))
  have i1234 := i123.sub (i4.const_mul (1 / 2))
  rw [e]
  refine ⟨i1234, ?_⟩
  rw [intervalIntegral.integral_sub i123 (i4.const_mul (1 / 2)),
    intervalIntegral.integral_add i12 (i3.const_mul (1 / 2)),
    intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, v1, v2, v3, v4]
  ring

/-! ### Landen's identity for `dilogI` -/

theorem i3X_dilogI_landen {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    dilogI (-(x / (1 - x))) = -dilogI x - log (1 - x) ^ 2 / 2 := by
  have hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun t => dilogI (-(t / (1 - t))) + dilogI t + log (1 - t) ^ 2 / 2) 0 t := by
    intro t ht
    obtain ⟨h0, h1⟩ := ht
    have hy : 0 < 1 - t := by linarith
    have hf : HasDerivAt (fun t => -(t / (1 - t))) (-(1 / (1 - t) ^ 2)) t := by
      have := ((hasDerivAt_id' t).div ((hasDerivAt_id' t).const_sub 1) hy.ne').neg
      refine this.congr_deriv ?_
      field_simp
      ring
    have hne : -(t / (1 - t)) ≠ 0 := neg_ne_zero.2 (div_pos h0 hy).ne'
    have hlt : -(t / (1 - t)) < 1 := by
      have : 0 < t / (1 - t) := div_pos h0 hy
      linarith
    have d1 := (hasDerivAt_dilogI hlt).comp t hf
    have d2 := hasDerivAt_dilogI (show t < 1 from h1)
    have hL := (((hasDerivAt_id' t).const_sub 1).log hy.ne').pow 2 |>.div_const 2
    refine ((d1.add d2).add hL).congr_deriv ?_
    have e : 1 - -(t / (1 - t)) = 1 / (1 - t) := by field_simp; ring
    simp only [dilogKer, hne, h0.ne', ite_false, e, one_div, log_inv]
    field_simp
    ring
  have hlim : Tendsto (fun t => dilogI (-(t / (1 - t))) + dilogI t + log (1 - t) ^ 2 / 2)
      (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t => dilogI (-(t / (1 - t))) + dilogI t + log (1 - t) ^ 2 / 2)
        0 := by
      have g1 : ContinuousAt (fun t : ℝ => -(t / (1 - t))) 0 :=
        (continuousAt_id.div (continuousAt_const.sub continuousAt_id) (by norm_num)).neg
      have a1 : ContinuousAt (fun t => dilogI (-(t / (1 - t)))) 0 :=
        ContinuousAt.comp (g := dilogI) (by
          simpa using (hasDerivAt_dilogI (show (-(0 / (1 - 0)) : ℝ) < 1 by norm_num)).continuousAt)
          g1
      have a2 : ContinuousAt dilogI 0 := (hasDerivAt_dilogI (by norm_num)).continuousAt
      have a3 : ContinuousAt (fun t : ℝ => log (1 - t) ^ 2 / 2) 0 :=
        (((continuousAt_const.sub continuousAt_id).log (by norm_num)).pow 2).div_const 2
      exact (a1.add a2).add a3
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have := eq_of_hasDerivAt_zero_of_tendsto one_pos hd hlim x hx
  linarith

end QED.ThreeLoopD
