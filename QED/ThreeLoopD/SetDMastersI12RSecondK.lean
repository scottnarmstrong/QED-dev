/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RPrim
import QED.Polylog.ExtraIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Set (d), master `I₁₂`: the weight-two function `K` and its inversion pairing

For `m > 0` let

  `K(m) = ∫₀¹ Φ(m u / (1 - u)) du`   (`QED.ThreeLoopD.i12RK`),

with `Φ = QED.ThreeLoopD.i12RPhi` the antiderivative of `g(r) / r`. Equivalently
`K(m) = ∫₀^∞ g(r) m / (r (r + m)) dr`, a weight-two function of `m` whose closed form involves
`Li₂ (1 - m)`; the power-series `Li₂` of `QED.Polylog` is not the dilogarithm beyond `[-1, 1]`, so
`K` is defined as an integral and its inversion law is proved by integration alone.

**Integrability.** On `(0, ∞)`, `|Φ(r)| ≤ 9 + π² + 3 log² (1 + r)` (each of
`log (1 + r) / r`, `r log (1 + 1/r)` lies in `[0, 1]` and `Li₂` in `[0, π²/6]` on `[0, 1]`), and
`log (1 + m u / (1 - u)) ≤ log (1 + m) - log (1 - u)`, so the integrand is dominated by
`const + 6 log² (1 - u)`.

**Pairing.** Substituting `u ↦ 1 - u` in `K(1/m)` turns its argument into `1 / k`,
`k = m u / (1 - u)`, and `Φ(k) + Φ(1/k) = -6 - π² - 3 log² k`
(`QED.ThreeLoopD.i12RPhi_add_i12RPhi_inv`). With `∫₀¹ log² (m u / (1 - u)) du = log² m + π²/3`,

  `K(m) + K(1/m) = -6 - 2π² - 3 log² m`.

## Main results

* `QED.ThreeLoopD.abs_i12RPhi_le`, `QED.ThreeLoopD.intervalIntegrable_i12RK`.
* `QED.ThreeLoopD.intervalIntegrable_and_integral_i12_log_sq_mul`.
* `QED.ThreeLoopD.i12RK_add_i12RK_inv`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- `K(m) = ∫₀¹ Φ(m u / (1 - u)) du`. -/
noncomputable def i12RK (m : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, i12RPhi (m * u / (1 - u))

/-- **The size of `Φ`**: `|Φ(r)| ≤ 9 + π² + 3 log² (1 + r)` for `r > 0`. -/
theorem abs_i12RPhi_le {r : ℝ} (hr : 0 < r) :
    |i12RPhi r| ≤ 9 + π ^ 2 + 3 * log (1 + r) ^ 2 := by
  have h1 : 0 < 1 + r := by linarith
  have hw := i12_div_one_add_mem hr
  have hA0 : 0 ≤ log (1 + r) / r := div_nonneg (log_nonneg (by linarith)) hr.le
  have hA1 : log (1 + r) / r ≤ 1 := by
    rw [div_le_one hr]
    linarith [log_le_sub_one_of_pos h1]
  have hB : r * log (1 + r) - r * log r = r * log ((1 + r) / r) := by
    rw [log_div h1.ne' hr.ne']; ring
  have hB0 : 0 ≤ r * log ((1 + r) / r) :=
    mul_nonneg hr.le (log_nonneg (by rw [le_div_iff₀ hr]; linarith))
  have hB1 : r * log ((1 + r) / r) ≤ 1 := by
    have := log_le_sub_one_of_pos (div_pos h1 hr)
    have e : r * ((1 + r) / r - 1) = 1 := by field_simp; ring
    nlinarith
  have hQ0 := Li₂_nonneg hw.1.le
  have hQ1 := Li₂_le_pi_sq_div_six (y := r / (1 + r)) ⟨by linarith [hw.1], hw.2.le⟩
  have hL := sq_nonneg (log (1 + r))
  have hπ := sq_nonneg π
  have e : i12RPhi r = 3 * (log (1 + r) / r) - 3 * (r * log ((1 + r) / r)) -
      6 * Li₂ (r / (1 + r)) - 3 * log (1 + r) ^ 2 - 3 := by
    rw [← hB]; simp only [i12RPhi]; ring
  rw [e, abs_le]
  constructor <;> nlinarith

theorem i12_log_one_add_le {m u : ℝ} (hm : 0 < m) (hu : u ∈ Ioo (0 : ℝ) 1) :
    0 ≤ log (1 + m * u / (1 - u)) ∧
      log (1 + m * u / (1 - u)) ≤ log (1 + m) - log (1 - u) := by
  have h1 : 0 < 1 - u := by linarith [hu.2]
  have hr : 0 < m * u / (1 - u) := div_pos (mul_pos hm hu.1) h1
  refine ⟨log_nonneg (by linarith), ?_⟩
  rw [← log_div (by linarith) h1.ne']
  refine log_le_log (by linarith) ?_
  rw [le_div_iff₀ h1, add_mul, one_mul, div_mul_cancel₀ _ h1.ne']
  nlinarith [hu.1, hu.2]

theorem integrableOn_log_one_sub_sq : IntegrableOn (fun u : ℝ => log (1 - u) ^ 2) (Ioo 0 1) := by
  have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1
    intervalIntegrable_and_integral_log_one_sub_sq_div.1
  refine h.mono' (by fun_prop : Measurable fun u : ℝ => log (1 - u) ^ 2).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioo fun u hu => ?_
  rw [norm_of_nonneg (sq_nonneg _)]
  exact le_div_self (sq_nonneg _) hu.1 hu.2.le

theorem continuousOn_i12RK_integrand {m : ℝ} (hm : 0 < m) :
    ContinuousOn (fun u => i12RPhi (m * u / (1 - u))) (Ioo 0 1) := by
  intro u hu
  have h1 : 1 - u ≠ 0 := by linarith [hu.2]
  have hr : 0 < m * u / (1 - u) := div_pos (mul_pos hm hu.1) (by linarith [hu.2])
  have hc : ContinuousAt (fun u : ℝ => m * u / (1 - u)) u :=
    (continuousAt_const.mul continuousAt_id).div (continuousAt_const.sub continuousAt_id) h1
  exact (ContinuousAt.comp (x := u) (g := i12RPhi) (f := fun u : ℝ => m * u / (1 - u))
    (hasDerivAt_i12RPhi hr).continuousAt hc).continuousWithinAt

/-- The integrand of `K(m)` is integrable on `(0, 1)`. -/
theorem integrableOn_i12RK {m : ℝ} (hm : 0 < m) :
    IntegrableOn (fun u => i12RPhi (m * u / (1 - u))) (Ioo 0 1) := by
  have hb : IntegrableOn (fun u : ℝ => (9 + π ^ 2 + 6 * log (1 + m) ^ 2) +
      6 * log (1 - u) ^ 2) (Ioo 0 1) :=
    (integrableOn_const (by simp)).add (integrableOn_log_one_sub_sq.const_mul 6)
  refine hb.mono' ((continuousOn_i12RK_integrand hm).aestronglyMeasurable measurableSet_Ioo) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioo fun u hu => ?_
  have hr : 0 < m * u / (1 - u) := div_pos (mul_pos hm hu.1) (by linarith [hu.2])
  have h := abs_i12RPhi_le hr
  obtain ⟨hl0, hl1⟩ := i12_log_one_add_le hm hu
  have hm0 : 0 ≤ log (1 + m) := log_nonneg (by linarith)
  have hu0 : log (1 - u) ≤ 0 := log_nonpos (by linarith [hu.2]) (by linarith [hu.1])
  rw [Real.norm_eq_abs]
  have : log (1 + m * u / (1 - u)) ^ 2 ≤ 2 * log (1 + m) ^ 2 + 2 * log (1 - u) ^ 2 := by
    nlinarith [sq_nonneg (log (1 + m) + log (1 - u))]
  linarith

theorem intervalIntegrable_i12RK {m : ℝ} (hm : 0 < m) :
    IntervalIntegrable (fun u => i12RPhi (m * u / (1 - u))) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 (integrableOn_i12RK hm)

/-- An interval integral over `[0, 1]` depends only on the values on `(0, 1)`. -/
theorem i12_integral_congr_Ioo {f g : ℝ → ℝ} (h : ∀ u ∈ Ioo (0 : ℝ) 1, f u = g u) :
    ∫ u in (0 : ℝ)..1, f u = ∫ u in (0 : ℝ)..1, g u := by
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

theorem i12_intervalIntegrable_congr_Ioo {f g : ℝ → ℝ} (h : ∀ u ∈ Ioo (0 : ℝ) 1, f u = g u)
    (hf : IntervalIntegrable f volume 0 1) : IntervalIntegrable g volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at hf ⊢
  exact hf.congr_fun h measurableSet_Ioo

/-- `∫₀¹ log (2u / (1 - u)) du = log 2`. -/
theorem intervalIntegrable_and_integral_i12_log :
    IntervalIntegrable (fun u : ℝ => log (2 * u / (1 - u))) volume 0 1 ∧
      ∫ u in (0 : ℝ)..1, log (2 * u / (1 - u)) = log 2 := by
  have hpt : ∀ u ∈ Ioo (0 : ℝ) 1, log 2 + log u - log (1 - u) = log (2 * u / (1 - u)) := by
    intro u hu
    rw [log_div (by linarith [hu.1]) (by linarith [hu.2]), log_mul (by norm_num) hu.1.ne']
  have hl1 : IntervalIntegrable (fun u : ℝ => log (1 - u)) volume 0 1 := by
    have := (intervalIntegral.intervalIntegrable_log' (a := 1) (b := 0)).comp_sub_left 1
    simpa using this
  have hi : IntervalIntegrable (fun u : ℝ => log 2 + log u - log (1 - u)) volume 0 1 :=
    (intervalIntegrable_const.add intervalIntegral.intervalIntegrable_log').sub hl1
  refine ⟨i12_intervalIntegrable_congr_Ioo hpt hi, ?_⟩
  rw [← i12_integral_congr_Ioo hpt, intervalIntegral.integral_sub
    (intervalIntegrable_const.add intervalIntegral.intervalIntegrable_log') hl1,
    intervalIntegral.integral_add intervalIntegrable_const
      intervalIntegral.intervalIntegrable_log', integral_log,
    intervalIntegral.integral_comp_sub_left (fun u => log u) 1, integral_log]
  simp

/-- **`∫₀¹ log² (m u / (1 - u)) du = log² m + π² / 3`** for `m > 0`. -/
theorem intervalIntegrable_and_integral_i12_log_sq_mul {m : ℝ} (hm : 0 < m) :
    IntervalIntegrable (fun u : ℝ => log (m * u / (1 - u)) ^ 2) volume 0 1 ∧
      ∫ u in (0 : ℝ)..1, log (m * u / (1 - u)) ^ 2 = log m ^ 2 + π ^ 2 / 3 := by
  obtain ⟨hA, hAv⟩ := intervalIntegrable_and_integral_i12_log
  obtain ⟨hS, hSv⟩ := intervalIntegrable_and_integral_i12_log_sq
  set c := log (m / 2) with hc
  have hpt : ∀ u ∈ Ioo (0 : ℝ) 1, log (2 * u / (1 - u)) ^ 2 + 2 * c * log (2 * u / (1 - u)) +
      c ^ 2 = log (m * u / (1 - u)) ^ 2 := by
    intro u hu
    have h1 : 0 < 2 * u / (1 - u) := div_pos (by linarith [hu.1]) (by linarith [hu.2])
    have e : m * u / (1 - u) = m / 2 * (2 * u / (1 - u)) := by ring
    rw [e, log_mul (by positivity) h1.ne', hc]
    ring
  have hi : IntervalIntegrable (fun u : ℝ => log (2 * u / (1 - u)) ^ 2 +
      2 * c * log (2 * u / (1 - u)) + c ^ 2) volume 0 1 :=
    (hS.add (hA.const_mul _)).add intervalIntegrable_const
  refine ⟨i12_intervalIntegrable_congr_Ioo hpt hi, ?_⟩
  rw [← i12_integral_congr_Ioo hpt, intervalIntegral.integral_add (hS.add (hA.const_mul _))
    intervalIntegrable_const, intervalIntegral.integral_add hS (hA.const_mul _),
    intervalIntegral.integral_const_mul, hSv, hAv, hc, log_div hm.ne' (by norm_num)]
  simp
  ring

/-- **The inversion pairing**: `K(m) + K(1/m) = -6 - 2π² - 3 log² m` for `m > 0`. -/
theorem i12RK_add_i12RK_inv {m : ℝ} (hm : 0 < m) :
    i12RK m + i12RK (1 / m) = -6 - 2 * π ^ 2 - 3 * log m ^ 2 := by
  have hflip : i12RK (1 / m) = ∫ u in (0 : ℝ)..1, i12RPhi (1 / m * (1 - u) / (1 - (1 - u))) := by
    rw [i12RK, intervalIntegral.integral_comp_sub_left
      (fun u => i12RPhi (1 / m * u / (1 - u))) 1]
    simp
  have hi2 : IntervalIntegrable (fun u => i12RPhi (1 / m * (1 - u) / (1 - (1 - u))))
      volume 0 1 := by
    have := (intervalIntegrable_i12RK (one_div_pos.2 hm)).symm.comp_sub_left 1
    simpa using this
  have hpt : ∀ u ∈ Ioo (0 : ℝ) 1,
      i12RPhi (m * u / (1 - u)) + i12RPhi (1 / m * (1 - u) / (1 - (1 - u))) =
        -6 - π ^ 2 - 3 * log (m * u / (1 - u)) ^ 2 := by
    intro u hu
    have hk : 0 < m * u / (1 - u) := div_pos (mul_pos hm hu.1) (by linarith [hu.2])
    have e : 1 / m * (1 - u) / (1 - (1 - u)) = 1 / (m * u / (1 - u)) := by
      have hu0 : u ≠ 0 := hu.1.ne'
      have hu1 : 1 - u ≠ 0 := by linarith [hu.2]
      rw [sub_sub_cancel]
      field_simp
    rw [e, i12RPhi_add_i12RPhi_inv hk]
  obtain ⟨hL, hLv⟩ := intervalIntegrable_and_integral_i12_log_sq_mul hm
  rw [hflip, i12RK, ← intervalIntegral.integral_add (intervalIntegrable_i12RK hm) hi2,
    i12_integral_congr_Ioo hpt, intervalIntegral.integral_sub intervalIntegrable_const
      (hL.const_mul 3), intervalIntegral.integral_const_mul, hLv]
  simp
  ring

end QED.ThreeLoopD
