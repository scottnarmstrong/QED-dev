/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.SetAConst
public import QED.Chain.SetASubst
import QED.Chain.SetAW1Lim
import QED.Chain.SetAW3
import QED.Chain.SetAW4
import QED.Polylog.LogLogSq
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Set (a): the value

Helper analysis for the sixth-order set (a) of `docs/HIGHER-LOOP-PLAN.md`. It is **not** frozen.

On `(0, 1)` the function `G = G₁ + G₃ - (8/3) G₄` (`QED.Chain.setAG1`, `QED.Chain.setAG3`,
`QED.Chain.setAG4`) has derivative `setAJ + (8/3) R`, with the remainder
`R = log u log² (1 - u²)/u - log u log² (1 - u)/u` (`QED.Chain.setARem`), whose integral is
`-π⁴/720 + π⁴/180 = π⁴/240` (`QED.Polylog.LogLogSq`). The fundamental theorem of calculus with
the endpoint limits of `G₁, G₃, G₄` gives the value of `∫₀¹ setAJ`, and
`QED.Chain.integral_setA_eq_setAJ` turns it into the set (a) integral.

## Main statements

* `QED.Chain.integral_setAJ`: `∫₀¹ setAJ u du = aSetA`.
* `QED.Chain.integral_setA_eq_aSetA`: `∫₀¹ (1 - x) Π̂⁽⁴⁾(x²/(1-x)) dx = aSetA`.
-/

public section

open Real Set Filter Topology MeasureTheory QED.Polylog

namespace QED.Chain

/-- `∫₀¹ setAJ u du = aSetA`. -/
theorem integral_setAJ : ∫ u in (0 : ℝ)..1, setAJ u = aSetA := by
  obtain ⟨iA, vA⟩ := intervalIntegrable_and_integral_log_mul_log_one_sub_sq_sq_div
  obtain ⟨iB, vB⟩ := intervalIntegrable_and_integral_log_mul_log_one_sub_sq_div
  have iR : IntervalIntegrable setARem volume 0 1 := iA.sub iB
  have vR : ∫ u in (0 : ℝ)..1, setARem u = π ^ 4 / 240 := by
    unfold setARem
    rw [intervalIntegral.integral_sub iA iB, vA, vB]
    ring
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun u => setAG1 u + setAG3 u - 8 / 3 * setAG4 u)
      (setAJ x + 8 / 3 * setARem x) x := by
    intro x hx
    have h := ((hasDerivAt_setAG1 hx).add (hasDerivAt_setAG3 hx)).sub
      ((hasDerivAt_setAG4 hx).const_mul (8 / 3))
    refine h.congr_deriv ?_
    unfold setAg1
    ring
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one hd
    (intervalIntegrable_setAJ.add (iR.const_mul (8 / 3)))
    ((tendsto_setAG1_zero.add tendsto_setAG3_zero).sub (tendsto_setAG4_zero.const_mul (8 / 3)))
    ((tendsto_setAG1_one.add tendsto_setAG3_one).sub (tendsto_setAG4_one.const_mul (8 / 3)))
  rw [intervalIntegral.integral_add intervalIntegrable_setAJ (iR.const_mul (8 / 3)),
    intervalIntegral.integral_const_mul, vR] at hF
  unfold aSetA
  linarith

/-- **The set (a) value**: `∫₀¹ (1 - x) Π̂⁽⁴⁾(x²/(1-x)) dx = aSetA`. -/
theorem integral_setA_eq_aSetA :
    ∫ x in (0 : ℝ)..1, (1 - x) * piHat4 (x ^ 2 / (1 - x)) = aSetA := by
  rw [integral_setA_eq_setAJ, integral_setAJ]

end QED.Chain
