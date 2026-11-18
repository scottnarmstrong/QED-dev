/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The dilogarithm on `(-∞, 1)` as an integral

The power series `QED.Polylog.Li₂` is the dilogarithm only on `[-1, 1]`. For the `ξ`-integration
of the crossed-ladder unit (section 4.5.2 of `docs/TWO-LOOP-UNITS.md`), whose antiderivatives
contain `Li₂` at arguments below `-1`, this file defines

`dilogI x = -∫₀ˣ log (1 - t)/t dt` for `x < 1`,

with the integrand extended by `-1` at `t = 0` (`dilogKer`), and proves:

* `continuousOn_dilogKer`: the extended integrand is continuous on `(-∞, 1)`;
* `hasDerivAt_dilogI`: `dilogI' x = -dilogKer x`, i.e. `-log (1 - x)/x` for `x ≠ 0`, on `(-∞, 1)`;
* `dilogI_eq_Li₂`: `dilogI = Li₂` on `(-1, 1)`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.TwoLoop.UnitXClose

/-- `log (1 - t)/t`, extended by its limit `-1` at `t = 0`. -/
noncomputable def dilogKer (t : ℝ) : ℝ := if t = 0 then -1 else log (1 - t) / t

/-- The dilogarithm on `(-∞, 1)`: `-∫₀ˣ log (1 - t)/t dt`. -/
noncomputable def dilogI (x : ℝ) : ℝ := -∫ t in (0 : ℝ)..x, dilogKer t

theorem tendsto_log_one_sub_div : Tendsto (fun t : ℝ => log (1 - t) / t) (𝓝[≠] 0) (𝓝 (-1)) := by
  have h : HasDerivAt (fun t : ℝ => log (1 - t)) (-1) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_sub 1).log (by norm_num)
    simpa using this
  have := h.tendsto_slope_zero
  simp only [zero_add, sub_zero, log_one, smul_eq_mul] at this
  refine this.congr fun t => ?_
  rw [inv_mul_eq_div]

theorem continuousOn_dilogKer : ContinuousOn dilogKer (Iio 1) := by
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · refine ContinuousAt.continuousWithinAt ?_
    have h0 : dilogKer 0 = -1 := by simp [dilogKer]
    rw [ContinuousAt, ← nhdsNE_sup_pure (0 : ℝ), tendsto_sup]
    refine ⟨?_, tendsto_pure_nhds dilogKer 0⟩
    rw [h0]
    refine (tendsto_log_one_sub_div.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    simp [dilogKer, ht']
  · have hx1 : 1 - x ≠ 0 := by have : x < 1 := hx; linarith
    refine ContinuousAt.continuousWithinAt ?_
    have hc : ContinuousAt (fun t : ℝ => log (1 - t) / t) x :=
      ((continuousAt_const.sub continuousAt_id).log hx1).div continuousAt_id hx0
    refine hc.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hx0] with t ht
    simp [dilogKer, ht]

theorem intervalIntegrable_dilogKer {x y : ℝ} (hx : x < 1) (hy : y < 1) :
    IntervalIntegrable dilogKer volume x y :=
  (continuousOn_dilogKer.mono fun t ht => by
    rcases (mem_uIcc.mp ht) with h | h
    · exact lt_of_le_of_lt h.2 hy
    · exact lt_of_le_of_lt h.2 hx).intervalIntegrable

/-- **The derivative of `dilogI`** on `(-∞, 1)`. -/
theorem hasDerivAt_dilogI {x : ℝ} (hx : x < 1) : HasDerivAt dilogI (-dilogKer x) x := by
  have hc : ContinuousAt dilogKer x :=
    continuousOn_dilogKer.continuousAt (Iio_mem_nhds hx)
  have := intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_dilogKer (x := 0) (by norm_num) hx)
    (continuousOn_dilogKer.stronglyMeasurableAtFilter isOpen_Iio x hx) hc
  exact this.neg

theorem hasDerivAt_dilogI_of_ne {x : ℝ} (hx : x < 1) (hx0 : x ≠ 0) :
    HasDerivAt dilogI (-log (1 - x) / x) x := by
  have := hasDerivAt_dilogI hx
  simp only [dilogKer, hx0, ite_false] at this
  rwa [neg_div]

@[simp] theorem dilogI_zero : dilogI 0 = 0 := by simp [dilogI]

/-- **`dilogI = Li₂` on `(-1, 1)`.** -/
theorem dilogI_eq_Li₂ {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : dilogI x = QED.Polylog.Li₂ x := by
  have hd : ∀ y ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun y => dilogI y - QED.Polylog.Li₂ y) 0 y := by
    intro y hy
    have hy1 : |y| < 1 := abs_lt.mpr hy
    rcases eq_or_ne y 0 with rfl | hy0
    · have := (hasDerivAt_dilogI (by norm_num : (0 : ℝ) < 1)).sub QED.Polylog.hasDerivAt_Li₂_zero
      convert this using 1
      simp [dilogKer]
    · have := (hasDerivAt_dilogI_of_ne hy.2 hy0).sub (QED.Polylog.hasDerivAt_Li₂ hy1 hy0)
      convert this using 1
      ring
  have key := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hd y hy).deriv) hx (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 by norm_num)
  simp only [dilogI_zero, QED.Polylog.Li₂_zero, sub_zero] at key
  linarith

end QED.TwoLoop.UnitXClose

end
