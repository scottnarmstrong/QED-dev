/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.LiN
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import QED.Polylog.ConstBounds
import QED.Polylog.ExtraIntegrals
import QED.Polylog.Reflection
import QED.TwoLoop.UnitXKernel
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Set (c): second-order expansions of the atoms at the endpoints

Helper analysis for the sixth-order set (c) of `docs/HIGHER-LOOP-PLAN.md`. It is **not** frozen.

The set (c) integrand and the rational-coefficient antiderivative are polynomials in the atoms
`log x, log (1 - x), log (1 + x), Li 2 x, Li 2 (-x)` with rational coefficients that have poles
at `x = 0` and `x = 1`. The poles cancel against second-order expansions of the atoms, with
third-order remainders

* `remA t = (log (1 - t) + t + t²/2)/t³`, `remB t = (log (1 + t) - t + t²/2)/t³`,
* `remC t = (Li 2 t - t - t²/4)/t³`, `remD t = (Li 2 (-t) + t - t²/4)/t³`,

bounded on `(0, 1/2)` (`remC` on `(0, 3/4)`). Near `x = 1`, with `y = 1 - x`, the atoms are
`log (1 - y)`, `log y`, `log (2 - y) = log 2 + log (1 - y/2)`, `Li 2 (1 - y)` (Euler
reflection) and `Li 2 (-(1 - y))` (duplication and reflection at `(1 - y)²`, with
`1 - (1 - y)² = y (2 - y)`).

## Main statements

* `abs_remA_le`, `abs_remB_le`, `abs_remC_le`, `abs_remD_le`.
* `Li_two_one_sub_eq`, `Li_two_neg_one_sub_eq`: the atoms `Li 2 (±(1 - y))` near `y = 0`.
* `LogSqBound`: `|f x| ≤ C (1 + log² x)` on `(0, 1/2)`, with `tendsto_of_eq_add_mul` (limits)
  and `intervalIntegrable_of_logSqBound` (integrability).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog

namespace QED.Chain.SetCRem

/-- `(log (1 - t) + t + t²/2)/t³`. -/
noncomputable def remA (t : ℝ) : ℝ := (log (1 - t) + t + t ^ 2 / 2) / t ^ 3

/-- `(log (1 + t) - t + t²/2)/t³`. -/
noncomputable def remB (t : ℝ) : ℝ := (log (1 + t) - t + t ^ 2 / 2) / t ^ 3

/-- `(Li 2 t - t - t²/4)/t³`. -/
noncomputable def remC (t : ℝ) : ℝ := (Li 2 t - t - t ^ 2 / 4) / t ^ 3

/-- `(Li 2 (-t) + t - t²/4)/t³`. -/
noncomputable def remD (t : ℝ) : ℝ := (Li 2 (-t) + t - t ^ 2 / 4) / t ^ 3

private theorem cube_div_le {x : ℝ} (h0 : 0 < x) (h1 : x < 1 / 2) :
    x ^ 3 / (1 - x) ≤ 3 * x ^ 3 := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith [pow_pos h0 3]

theorem abs_remA_le {x : ℝ} (h0 : 0 < x) (h1 : x < 1 / 2) : |remA x| ≤ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by rw [abs_of_pos h0]; linarith) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_of_pos h0] at h
  norm_num at h
  have hx3 : 0 < x ^ 3 := pow_pos h0 3
  rw [remA, abs_div, abs_of_pos hx3, div_le_iff₀ hx3,
    show log (1 - x) + x + x ^ 2 / 2 = x + x ^ 2 / 2 + log (1 - x) by ring]
  linarith [cube_div_le h0 h1]

theorem abs_remB_le {x : ℝ} (h0 : 0 < x) (h1 : x < 1 / 2) : |remB x| ≤ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |-x| < 1 by rw [abs_neg, abs_of_pos h0]; linarith) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, abs_of_pos h0] at h
  norm_num at h
  have hx3 : 0 < x ^ 3 := pow_pos h0 3
  rw [remB, abs_div, abs_of_pos hx3, div_le_iff₀ hx3,
    show log (1 + x) - x + x ^ 2 / 2 = -x + x ^ 2 / 2 + log (1 + x) by ring]
  linarith [cube_div_le h0 h1]

private theorem Li_two_bounds {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    x + x ^ 2 / 4 ≤ Li 2 x ∧ Li 2 x ≤ x + x ^ 2 / 4 + x ^ 3 / (9 * (1 - x)) := by
  have h := Li_mem_partial 2 2 h0 h1
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem Li_two_bounds_one {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    x ≤ Li 2 x ∧ Li 2 x ≤ x + x ^ 2 / (4 * (1 - x)) := by
  have h := Li_mem_partial 2 1 h0 h1
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem abs_remC_le {x : ℝ} (h0 : 0 < x) (h1 : x < 3 / 4) : |remC x| ≤ 1 := by
  obtain ⟨l, r⟩ := Li_two_bounds h0.le (by linarith)
  have hx3 : 0 < x ^ 3 := pow_pos h0 3
  have hq : x ^ 3 / (9 * (1 - x)) ≤ x ^ 3 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  rw [remC, abs_div, abs_of_pos hx3, div_le_iff₀ hx3, abs_le]
  constructor <;> linarith

theorem abs_remD_le {x : ℝ} (h0 : 0 < x) (h1 : x < 1 / 2) : |remD x| ≤ 1 := by
  have hd := Li_add_Li_neg (k := 2) le_rfl (x := x) (by rw [abs_of_pos h0]; linarith)
  obtain ⟨l, r⟩ := Li_two_bounds h0.le (by linarith)
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  obtain ⟨l2, r2⟩ := Li_two_bounds_one hx2 (by nlinarith)
  have hx3 : 0 < x ^ 3 := pow_pos h0 3
  have hq : x ^ 3 / (9 * (1 - x)) ≤ x ^ 3 / 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hq2 : (x ^ 2) ^ 2 / (4 * (1 - x ^ 2)) ≤ x ^ 3 := by
    rw [div_le_iff₀ (by nlinarith)]; nlinarith [pow_pos h0 4]
  rw [remD, abs_div, abs_of_pos hx3, div_le_iff₀ hx3, abs_le]
  norm_num at hd
  constructor <;> nlinarith

theorem log_one_sub_eq {t : ℝ} (h0 : 0 < t) :
    log (1 - t) = -t - t ^ 2 / 2 + t ^ 3 * remA t := by
  unfold remA; field_simp; ring

theorem log_one_add_eq {t : ℝ} (h0 : 0 < t) :
    log (1 + t) = t - t ^ 2 / 2 + t ^ 3 * remB t := by
  unfold remB; field_simp; ring

theorem Li_two_eq {t : ℝ} (h0 : 0 < t) : Li 2 t = t + t ^ 2 / 4 + t ^ 3 * remC t := by
  unfold remC; field_simp; ring

theorem Li_two_neg_eq {t : ℝ} (h0 : 0 < t) : Li 2 (-t) = -t + t ^ 2 / 4 + t ^ 3 * remD t := by
  unfold remD; field_simp; ring

/-- `log (1 + (1 - y)) = log 2 - y/2 - y²/8 + (y/2)³ remA (y/2)` for `0 < y < 1`. -/
theorem log_two_sub_eq {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    log (1 + (1 - y)) = log 2 - y / 2 - y ^ 2 / 8 + (y / 2) ^ 3 * remA (y / 2) := by
  have e : 1 + (1 - y) = 2 * (1 - y / 2) := by ring
  rw [e, log_mul two_ne_zero (by linarith), log_one_sub_eq (by positivity)]
  ring

/-- Euler reflection near `y = 0`: `Li 2 (1 - y) = π²/6 - log y log (1 - y) - Li 2 y`. -/
theorem Li_two_one_sub_eq {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    Li 2 (1 - y) = π ^ 2 / 6 - log y * log (1 - y) - Li 2 y := by
  have h := Li₂_add_Li₂_one_sub h0.le h1.le
  rw [Li_two]
  linarith

/-- `Li 2 (-(1 - y)) = -π²/12 - log (1 - y) log (1 + (1 - y)) - Li 2 (y(2 - y))/2 + Li 2 y`. -/
theorem Li_two_neg_one_sub_eq {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    Li 2 (-(1 - y)) = -(π ^ 2 / 12) - log (1 - y) * log (1 + (1 - y)) -
      Li 2 (y * (2 - y)) / 2 + Li 2 y := by
  have hd := Li_add_Li_neg (k := 2) le_rfl (x := 1 - y)
    (by rw [abs_of_pos (by linarith)]; linarith)
  have hw0 : 0 ≤ (1 - y) ^ 2 := sq_nonneg _
  have hw1 : (1 - y) ^ 2 ≤ 1 := by nlinarith
  have hr := Li₂_add_Li₂_one_sub hw0 hw1
  have hr1 := Li_two_one_sub_eq h0 h1
  have e1 : 1 - (1 - y) ^ 2 = y * (2 - y) := by ring
  have e2 : log ((1 - y) ^ 2) = 2 * log (1 - y) := by
    rw [log_pow]; push_cast; ring
  have e3 : log (y * (2 - y)) = log y + log (1 + (1 - y)) := by
    rw [log_mul h0.ne' (by linarith), show 2 - y = 1 + (1 - y) by ring]
  rw [e1, e2, e3] at hr
  have hr' : Li 2 ((1 - y) ^ 2) + Li 2 (y * (2 - y)) =
      π ^ 2 / 6 - 2 * log (1 - y) * (log y + log (1 + (1 - y))) := hr
  rw [show (2 : ℝ) / 2 ^ 2 = 1 / 2 by norm_num] at hd
  linarith

/-! ### Bounds of the form `C (1 + log² x)` on `(0, 1/2)` -/

/-- `f` is bounded on `(0, 1/2)`. -/
def Bdd (f : ℝ → ℝ) : Prop := ∃ M, ∀ x ∈ Ioo (0 : ℝ) (1 / 2), |f x| ≤ M

/-- `|f x| ≤ C (1 + log² x)` on `(0, 1/2)`. -/
def LogSqBound (f : ℝ → ℝ) : Prop := ∃ C, ∀ x ∈ Ioo (0 : ℝ) (1 / 2), |f x| ≤ C * (1 + log x ^ 2)

theorem bdd_one : Bdd fun _ => 1 := ⟨1, fun _ _ => by norm_num⟩

theorem Bdd.mul {f g : ℝ → ℝ} (hf : Bdd f) (hg : Bdd g) : Bdd fun x => f x * g x := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨M * N, fun x hx => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hM x hx) (hN x hx) (abs_nonneg _) ((abs_nonneg _).trans (hM x hx))

theorem Bdd.of_continuousAt {f : ℝ → ℝ} (h : ∀ x ∈ Icc (0 : ℝ) (1 / 2), ContinuousAt f x) :
    Bdd f := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (fun x hx => (h x hx).continuousWithinAt)
  exact ⟨M, fun x hx => by simpa using hM x (Ioo_subset_Icc_self hx)⟩

theorem bdd_remA : Bdd remA := ⟨3, fun _ hx => abs_remA_le hx.1 hx.2⟩

theorem bdd_remB : Bdd remB := ⟨3, fun _ hx => abs_remB_le hx.1 hx.2⟩

theorem bdd_remC : Bdd remC := ⟨1, fun _ hx => abs_remC_le hx.1 (by linarith [hx.2])⟩

theorem bdd_remD : Bdd remD := ⟨1, fun _ hx => abs_remD_le hx.1 hx.2⟩

theorem bdd_remA_half : Bdd fun y => remA (y / 2) :=
  ⟨3, fun _ hx => abs_remA_le (by linarith [hx.1]) (by linarith [hx.2])⟩

theorem bdd_remC_w : Bdd fun y => remC (y * (2 - y)) :=
  ⟨1, fun _ hx => abs_remC_le (by nlinarith [hx.1, hx.2]) (by nlinarith [hx.1, hx.2])⟩

theorem LogSqBound.add {f g : ℝ → ℝ} (hf : LogSqBound f) (hg : LogSqBound g) :
    LogSqBound fun x => f x + g x := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  exact ⟨C + D, fun x hx => (abs_add_le _ _).trans (by linarith [hC x hx, hD x hx])⟩

theorem LogSqBound.congr {f g : ℝ → ℝ} (hf : LogSqBound f)
    (he : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), g x = f x) : LogSqBound g := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun x hx => by rw [he x hx]; exact hC x hx⟩

/-- A term `d(x) logʲ x r(x)` with `d, r` bounded and `j ≤ 2`. -/
theorem logSqBound_term {d r : ℝ → ℝ} (hd : Bdd d) (hr : Bdd r) {j : ℕ} (hj : j ≤ 2) :
    LogSqBound fun x => d x * log x ^ j * r x := by
  obtain ⟨M, hM⟩ := hd.mul hr
  refine ⟨|M|, fun x hx => ?_⟩
  have hl : |log x| ^ j ≤ 1 + log x ^ 2 := by
    have h2 : |log x| ^ 2 = log x ^ 2 := sq_abs _
    interval_cases j
    · simp; positivity
    · nlinarith [abs_nonneg (log x)]
    · simp only [h2]; linarith
  have hM' : |d x * r x| ≤ M := hM x hx
  show |d x * log x ^ j * r x| ≤ _
  rw [show d x * log x ^ j * r x = (d x * r x) * log x ^ j by ring, abs_mul, abs_pow]
  exact mul_le_mul (hM'.trans (le_abs_self M)) hl (by positivity) (abs_nonneg _)

/-- If `f x = c + x S(x)` on `(0, 1/2)` with `S = O(1 + log² x)`, then `f → c` at `0⁺`. -/
theorem tendsto_of_eq_add_mul {f S : ℝ → ℝ} {c : ℝ} (hS : LogSqBound S)
    (he : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), f x = c + x * S x) : Tendsto f (𝓝[>] 0) (𝓝 c) := by
  obtain ⟨C, hC⟩ := hS
  have ev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) (1 / 2) := Ioo_mem_nhdsGT (by norm_num)
  have hx : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hg : Tendsto (fun x : ℝ => |C| * (x + x * log x ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hx.add tendsto_mul_log_sq_zero).const_mul |C|
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hg
  filter_upwards [ev] with x hx'
  rw [he x hx', Real.norm_eq_abs, add_sub_cancel_left, abs_mul, abs_of_pos hx'.1]
  have := (hC x hx').trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  nlinarith [hx'.1]

/-- A function continuous on `(0, 1/2)` with `|f x| ≤ C (1 + log² x)` there is integrable. -/
theorem intervalIntegrable_of_logSqBound {f : ℝ → ℝ} (hS : LogSqBound f)
    (hc : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), ContinuousAt f x) :
    IntervalIntegrable f volume 0 (1 / 2) := by
  obtain ⟨C, hC⟩ := hS
  have hg : IntervalIntegrable (fun x : ℝ => C * (1 + log x ^ 2)) volume 0 (1 / 2) := by
    refine ((intervalIntegrable_const.add QED.TwoLoop.Units.intervalIntegrable_log_sq_unit).mono_set
      ?_).const_mul C
    rw [uIcc_of_le (by norm_num), uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl (by norm_num)
  refine hg.mono_fun' ?_ ?_
  · rw [uIoc_of_le (by norm_num), ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact ContinuousOn.aestronglyMeasurable (fun x hx => (hc x hx).continuousWithinAt)
      measurableSet_Ioo
  · rw [uIoc_of_le (by norm_num), EventuallyLE, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs]
    exact hC x hx

end QED.Chain.SetCRem
