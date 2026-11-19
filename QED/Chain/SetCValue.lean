/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.SetCConst
public import QED.Chain.SetCKernel
import QED.Chain.SetCJInt
import QED.Chain.SetCW1Lim
import QED.Chain.SetCW3
import QED.Polylog.LogLiDiv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Set (c): the value

Helper analysis for the sixth-order set (c) of `docs/HIGHER-LOOP-PLAN.md`. It is **not** frozen.

On `(0, 1)` the function `G₁ + G₃` (`QED.Chain.setCG1`, `QED.Chain.setCG3`) has derivative
`setCJ - w₄`, where `w₄ = (5/3) log u Φ(u)/u` (`QED.Chain.setCw4`) has integral
`(5/3) π⁴/30 = π⁴/18` (the four integrals of `QED.Polylog.LogLiDiv`). The fundamental theorem of
calculus with the endpoint limits `G₁(0⁺) = 2147/432`, `G₁(1⁻) = 3509/432 - (8/9) log 2`,
`G₃(0⁺) = ζ(3)/3 - (8/9) log³ 2`, `G₃(1⁻) = -(97/24) ζ(3) - (8/9) log³ 2 - (4/3) π² log 2 +
(31/54) π² + (8/9) log 2` gives `∫₀¹ setCJ = aSetC`, and `QED.Chain.integral_setC_eq_setCJ`
turns it into the set (c) integral of Balzani–Laporta–Passera (arXiv:2112.05704), eq. (38).

## Main statements

* `QED.Chain.integral_setCJ`: `∫₀¹ setCJ u du = aSetC`.
* `QED.Chain.integral_setC_eq_aSetC`: `∫₀¹ λ⁽⁴⁾(x) Δα(x) dx = aSetC`.
-/

public section

open Real Set Filter Topology MeasureTheory QED.Polylog

namespace QED.Chain

/-- `∫₀¹ setCJ u du = aSetC`. -/
theorem integral_setCJ : ∫ u in (0 : ℝ)..1, setCJ u = aSetC := by
  obtain ⟨i1, v1⟩ := intervalIntegrable_and_integral_log_sq_mul_log_one_sub_div
  obtain ⟨i2, v2⟩ := intervalIntegrable_and_integral_log_sq_mul_log_one_add_div
  obtain ⟨i3, v3⟩ := intervalIntegrable_and_integral_log_mul_Li_two_div
  obtain ⟨i4, v4⟩ := intervalIntegrable_and_integral_log_mul_Li_two_neg_div
  have i12 := i1.add (i2.const_mul 2)
  have i123 := i12.add (i3.const_mul 2)
  have i1234 := i123.add (i4.const_mul 4)
  have iW4 : IntervalIntegrable setCw4 volume 0 1 := i1234.const_mul (5 / 3)
  have vW4 : ∫ u in (0 : ℝ)..1, setCw4 u = π ^ 4 / 18 := by
    unfold setCw4
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add i123 (i4.const_mul 4),
      intervalIntegral.integral_add i12 (i3.const_mul 2),
      intervalIntegral.integral_add i1 (i2.const_mul 2), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, v1, v2, v3, v4]
    ring
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun u => setCG1 u + setCG3 u)
      (setCJ x - setCw4 x) x := by
    intro x hx
    refine ((hasDerivAt_setCG1 hx).add (hasDerivAt_setCG3 hx)).congr_deriv ?_
    ring
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one hd
    (intervalIntegrable_setCJ.sub iW4) (tendsto_setCG1_zero.add tendsto_setCG3_zero)
    (tendsto_setCG1_one.add tendsto_setCG3_one)
  rw [intervalIntegral.integral_sub intervalIntegrable_setCJ iW4, vW4] at hF
  unfold aSetC
  linarith

/-- **The set (c) value** (BLP eq. (38), Barbieri–Remiddi 1974 eq. (3)):
`∫₀¹ λ⁽⁴⁾(x) Δα(x) dx = aSetC`. -/
theorem integral_setC_eq_aSetC :
    ∫ x in (0 : ℝ)..1, setCLambda x * setCDeltaAlpha x = aSetC := by
  rw [integral_setC_eq_setCJ, integral_setCJ]

/-- The set (c) integrand is integrable on `[0, 1]`. -/
theorem intervalIntegrable_setC :
    IntervalIntegrable (fun x => setCLambda x * setCDeltaAlpha x) volume 0 1 :=
  intervalIntegrable_setC_of_setCJ intervalIntegrable_setCJ

end QED.Chain
