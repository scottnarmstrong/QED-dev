/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.ExtraIntegrals
import QED.Polylog.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Endpoint estimates and two integrals for the corner unit

Facts about `Li₂` and `log (1 - x)` near `x = 0`, used in the exact evaluation of the corner
unit C (section 6.6 of `docs/TWO-LOOP-UNITS.md`). Its one-dimensional kernel has poles of order
two at `Y = 0`, which cancel between `Li₂ Y`, `log Y log (1 - Y)`, `log (1 - Y)` and rational
terms. The cancellation is organised through the three functions
`(Li₂ x + log (1 - x))/x²`, `(log (1 - x) + x)/x²` and `log x (log (1 - x) + x)/x²`.

## Main results

* `QED.Polylog.Li₂_le_neg_log_one_sub`: `Li₂ x ≤ -log (1 - x)` on `[0, 1)` (compare the series
  term by term).
* `QED.Polylog.abs_log_one_sub_add_le`: `|log (1 - x) + x| ≤ x²/(1 - x)` on `[0, 1)`.
* `QED.Polylog.tendsto_Li₂_div_zero`: `Li₂ x / x → 1` as `x → 0⁺`.
* `QED.Polylog.intervalIntegrable_and_integral_Li₂_add_log_one_sub_div_sq`:
  `∫₀¹ (Li₂ x + log (1 - x))/x² = 1 - π²/6`, with antiderivative `-Li₂ x / x`.
* `QED.Polylog.intervalIntegrable_and_integral_log_one_sub_add_div_sq`:
  `∫₀¹ (log (1 - x) + x)/x² = -1`.
* `QED.Polylog.intervalIntegrable_log_mul_log_one_sub_add_div_sq`: `log x (log (1 - x) + x)/x²`
  is integrable on `[0, 1]` (it is dominated by `log x/(x - 1)`).
* `QED.Polylog.tendsto_log_mul_log_one_sub_add_div_zero`: `log x (log (1 - x) + x)/x → 0` as
  `x → 0⁺`.
-/

public section

open Real Set Filter Topology MeasureTheory

namespace QED.Polylog

/-- `Li₂ x ≤ -log (1 - x)` for `0 ≤ x < 1`: the series `∑ xⁿ/n²` and `∑ xⁿ/n`, term by term. -/
theorem Li₂_le_neg_log_one_sub {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) : Li₂ x ≤ -log (1 - x) := by
  have ha : |x| < 1 := by rw [abs_of_nonneg h0]; exact h1
  refine hasSum_le (fun n => ?_) (hasSum_Li₂ ha.le) (hasSum_pow_div_log_of_abs_lt_one ha)
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [n.cast_nonneg (α := ℝ)]
  have hp : 0 ≤ x ^ (n + 1) := pow_nonneg h0 _
  exact div_le_div_of_nonneg_left hp (by positivity) (by nlinarith)

/-- `|log (1 - x) + x| ≤ x²/(1 - x)` for `0 ≤ x < 1`. -/
theorem abs_log_one_sub_add_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    |log (1 - x) + x| ≤ x ^ 2 / (1 - x) := by
  have ha : |x| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have h := Real.abs_log_sub_add_sum_range_le ha 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
    div_one, abs_of_nonneg h0] at h
  rwa [add_comm] at h

/-- `Li₂ x / x → 1` as `x → 0⁺` (`Li₂' 0 = 1`). -/
theorem tendsto_Li₂_div_zero : Tendsto (fun x => Li₂ x / x) (𝓝[>] 0) (𝓝 1) := by
  refine hasDerivAt_Li₂_zero.tendsto_slope_zero_right.congr fun t => ?_
  simp only [zero_add, Li₂_zero, sub_zero, smul_eq_mul]
  ring

/-- `∫₀¹ (Li₂ x + log (1 - x))/x² = 1 - π²/6`. The integrand is nonpositive
(`Li₂_le_neg_log_one_sub`) and `-Li₂ x / x` is an antiderivative. -/
theorem intervalIntegrable_and_integral_Li₂_add_log_one_sub_div_sq :
    IntervalIntegrable (fun x => (Li₂ x + log (1 - x)) / x ^ 2) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (Li₂ x + log (1 - x)) / x ^ 2 = 1 - π ^ 2 / 6 := by
  have h := intervalIntegrable_and_integral_eq_of_nonpos (F := fun x => -(Li₂ x / x))
    (f := fun x => (Li₂ x + log (1 - x)) / x ^ 2) (A := -1) (B := -(π ^ 2 / 6 / 1)) ?_ ?_ ?_ ?_
  · rwa [div_one, show -(π ^ 2 / 6) - -1 = 1 - π ^ 2 / 6 by ring] at h
  · intro x hx
    have := ((hasDerivAt_Li₂' hx).div (hasDerivAt_id' x) hx.1.ne').neg
    refine this.congr_deriv ?_
    have := hx.1.ne'
    field_simp
    ring
  · intro x hx
    have := Li₂_le_neg_log_one_sub hx.1.le hx.2
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg x)
  · exact tendsto_Li₂_div_zero.neg
  · exact (tendsto_Li₂_one_left.div ((tendsto_id (x := 𝓝[<] (1 : ℝ))).mono_right
      nhdsWithin_le_nhds) one_ne_zero).neg

/-- `x ↦ log x/(x - 1)` is integrable on `[0, 1]` (reflection of `∫₀¹ log (1 - x)/x`). -/
theorem intervalIntegrable_log_div_sub_one' :
    IntervalIntegrable (fun x => log x / (x - 1)) volume 0 1 := by
  have h := (intervalIntegrable_and_integral_log_one_sub_div.1.comp_sub_left 1).neg
  rw [sub_zero, sub_self] at h
  refine h.symm.congr_uIoo ?_
  intro x hx
  rw [uIoo_of_le zero_le_one] at hx
  have : x - 1 ≠ 0 := by linarith [hx.2]
  have : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
  simp only [Pi.neg_apply, sub_sub_cancel]
  field_simp
  ring

/-- `log x (log (1 - x) + x)/x²` is integrable on `[0, 1]`: by `abs_log_one_sub_add_le` it is
bounded in absolute value by `log x/(x - 1)`. -/
theorem intervalIntegrable_log_mul_log_one_sub_add_div_sq :
    IntervalIntegrable (fun x => log x * (log (1 - x) + x) / x ^ 2) volume 0 1 := by
  refine intervalIntegrable_log_div_sub_one'.mono_fun' ?_ ?_
  · exact (by fun_prop : Measurable fun x : ℝ => log x * (log (1 - x) + x) / x ^ 2)
      |>.aestronglyMeasurable
  · rw [uIoc_of_le zero_le_one]
    have hae : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)), x ≠ 1 := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      have : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
        simpa using measure_eq_zero_iff_ae_notMem.1
          ((Set.countable_singleton (1 : ℝ)).measure_zero volume)
      filter_upwards [this] with x hx _ using hx
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioc] with x hx1 hx
    have h0 : 0 < x := hx.1
    have h1 : x < 1 := lt_of_le_of_ne hx.2 hx1
    have hb := abs_log_one_sub_add_le h0.le h1
    have hl : log x ≤ 0 := log_nonpos h0.le h1.le
    have h1x : 0 < 1 - x := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonpos hl,
      abs_of_pos (by positivity : 0 < x ^ 2),
      show log x / (x - 1) = -log x / (1 - x) by
        rw [show x - 1 = -(1 - x) by ring, div_neg, neg_div]]
    rw [div_le_div_iff₀ (by positivity) h1x]
    have := mul_le_mul_of_nonneg_left hb (neg_nonneg.2 hl)
    calc -log x * |log (1 - x) + x| * (1 - x) ≤ -log x * (x ^ 2 / (1 - x)) * (1 - x) :=
          mul_le_mul_of_nonneg_right this h1x.le
      _ = -log x * x ^ 2 := by field_simp

/-- `log x (log (1 - x) + x)/x → 0` as `x → 0⁺`. -/
theorem tendsto_log_mul_log_one_sub_add_div_zero :
    Tendsto (fun x => log x * (log (1 - x) + x) / x) (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun x : ℝ => |x * log x| / (1 - x)) (𝓝[>] 0) (𝓝 0) := by
    have h2 : Tendsto (fun x : ℝ => 1 - x) (𝓝[>] 0) (𝓝 (1 - 0)) :=
      (tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds
    have := tendsto_mul_log_zero.abs.div h2 (by norm_num)
    rw [abs_zero, zero_div] at this
    exact this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
  have hb := abs_log_one_sub_add_le hx.1.le hx.2
  have h1x : 0 < 1 - x := by linarith [hx.2]
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hx.1, abs_mul, abs_of_pos hx.1,
    div_le_div_iff₀ hx.1 h1x]
  calc |log x| * |log (1 - x) + x| * (1 - x) ≤ |log x| * (x ^ 2 / (1 - x)) * (1 - x) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (abs_nonneg _)) h1x.le
    _ = x * |log x| * x := by field_simp

/-- `∫₀¹ (log (1 - x) + x)/x² = -1`, with antiderivative `-(1 - x) log (1 - x)/x` (the same
statement as `QED.TwoLoop.Units.hasIntegralOnUnit_log_one_sub_add_div_sq`, in the form of this
file). -/
theorem intervalIntegrable_and_integral_log_one_sub_add_div_sq :
    IntervalIntegrable (fun x => (log (1 - x) + x) / x ^ 2) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (log (1 - x) + x) / x ^ 2 = -1 := by
  have h := intervalIntegrable_and_integral_eq_of_nonpos
    (F := fun x => -((1 - x) * log (1 - x)) / x) (f := fun x => (log (1 - x) + x) / x ^ 2)
    (A := 1) (B := -0 / 1) ?_ ?_ ?_ ?_
  · rwa [neg_zero, zero_div, zero_sub] at h
  · intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hne : (1 : ℝ) - x ≠ 0 := by linarith
    have hs : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id' x).const_sub 1
    have := (hs.mul (hs.log hne)).neg.div (hasDerivAt_id' x) hx0.ne'
    refine this.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.neg_apply]
    field_simp
    ring
  · intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have := log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 - x)
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg x)
  · have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_id (x := 𝓝[>] (0 : ℝ))).mono_right nhdsWithin_le_nhds)).mul
        tendsto_log_one_sub_div_zero'
    refine (h.neg.congr' ?_).trans ?_
    · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
      simp only [id]
      ring
    · norm_num
  · have hL : Continuous fun y : ℝ => (1 - y) * log (1 - y) :=
      continuous_mul_log.comp (continuous_const.sub continuous_id)
    have h := ((hL.neg.continuousAt (x := 1)).div continuousAt_id one_ne_zero).tendsto
    have := h.mono_left (nhdsWithin_le_nhds (s := Iio 1))
    convert this using 2
    simp only [Pi.div_apply, Pi.neg_apply, id]
    norm_num

end QED.Polylog
