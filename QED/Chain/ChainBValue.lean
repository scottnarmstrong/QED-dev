/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.VPChainSetB
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The first moment `∫₀¹ x² Π̂(x²/(1-x)) dx = 41/18 - 2π²/9` (constant of O3-12)

Helper-level evaluation for obligation O3-12 of `docs/HIGHER-LOOP-PLAN.md`. It is **not** frozen.

The leading regulator-fermion offset of the set (b) chain (task T1,
`scripts/numerics/phase5_chains.py` section C.5) is `κ (M₁⁻² + M₂⁻²)` with
`κ = -(2/15) ∫₀¹ x² Π̂(x²/(1-x)) dx`. This file evaluates the integral, so
`κ = (4π² - 41)/135 ≈ -0.0112710`.

## Route

On `0 < x < 1`, `x² Π̂(x²/(1-x)) = x² piHatX x` (`QED.Chain.piHat_photonVar`), with the
antiderivative `F = -2x³/9 - 13x²/18 + 29x/9 + (17 - x - x²)/9 · (1-x) log(1-x) - (4/3) Li₂(x)`
(checked with sympy); `F(0⁺) = 0` and `F(1⁻) = 41/18 - 2π²/9`. The integrand is nonnegative.

## Main statements

* `intervalIntegrable_piHatMoment`: `x ↦ x² Π̂(x²/(1-x))` is interval integrable on `[0,1]`.
* `integral_piHatMoment`: `∫₀¹ x² Π̂(x²/(1-x)) dx = 41/18 - 2π²/9`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology QED.Polylog

namespace QED.Chain.ChainB

open QED.Chain

/-- The antiderivative of `x² piHatX x` on `(0,1)`. -/
noncomputable def momentPrim (x : ℝ) : ℝ :=
  -2 / 9 * x ^ 3 - 13 / 18 * x ^ 2 + 29 / 9 * x +
    (17 - x - x ^ 2) / 9 * ((1 - x) * log (1 - x)) - 4 / 3 * Li₂ x

theorem hasDerivAt_momentPrim {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt momentPrim (x ^ 2 * piHatX x) x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hx' : x ≠ 0 := hx0.ne'
  have hx1' : (1 : ℝ) - x ≠ 0 := by linarith
  have hA := hasDerivAt_poly7 0 (29 / 9) (-13 / 18) (-2 / 9) 0 0 0 0 x
  have hC := hasDerivAt_poly7 (17 / 9) (-1 / 9) (-1 / 9) 0 0 0 0 0 x
  have h := (hA.add (hC.mul (hasDerivAt_one_sub_mul_log hx1))).sub
    ((hasDerivAt_Li₂' ⟨hx0, hx1⟩).const_mul (4 / 3))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · simp only [piHatX]
    field_simp
    ring
  · simp only [momentPrim, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring

theorem tendsto_momentPrim_zero : Tendsto momentPrim (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt (fun x : ℝ => -2 / 9 * x ^ 3 - 13 / 18 * x ^ 2 + 29 / 9 * x +
      (17 - x - x ^ 2) / 9 * ((1 - x) * log (1 - x))) 0 := by
    have : ContinuousAt (fun x : ℝ => log (1 - x)) 0 :=
      (continuousAt_log (by norm_num)).comp (by fun_prop)
    fun_prop
  have h := (hc.tendsto.mono_left nhdsWithin_le_nhds).sub (tendsto_Li₂_zero_right.const_mul (4 / 3))
  simp only [sub_zero, log_one, mul_zero, add_zero, zero_pow two_ne_zero,
    zero_pow (by norm_num : (3 : ℕ) ≠ 0), mul_zero] at h
  exact h

theorem tendsto_momentPrim_one :
    Tendsto momentPrim (𝓝[<] 1) (𝓝 (41 / 18 - 2 * π ^ 2 / 9)) := by
  have hc : ∀ {f : ℝ → ℝ}, ContinuousAt f 1 → Tendsto f (𝓝[<] 1) (𝓝 (f 1)) := fun hf =>
    hf.tendsto.mono_left nhdsWithin_le_nhds
  have h0 := hc (f := fun x : ℝ => -2 / 9 * x ^ 3 - 13 / 18 * x ^ 2 + 29 / 9 * x) (by fun_prop)
  have h1 := hc (f := fun x : ℝ => (17 - x - x ^ 2) / 9) (by fun_prop)
  have h := (h0.add (h1.mul tendsto_one_sub_mul_log_one)).sub
    (tendsto_Li₂_one_left.const_mul (4 / 3))
  have hv : -2 / 9 * 1 ^ 3 - 13 / 18 * 1 ^ 2 + 29 / 9 * 1 + (17 - 1 - 1 ^ 2) / 9 * 0 -
      4 / 3 * (π ^ 2 / 6) = (41 / 18 - 2 * π ^ 2 / 9 : ℝ) := by ring
  rw [hv] at h
  exact h

theorem intervalIntegrable_and_integral_moment_closed :
    IntervalIntegrable (fun x => x ^ 2 * piHatX x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, x ^ 2 * piHatX x = 41 / 18 - 2 * π ^ 2 / 9 := by
  have h := intervalIntegrable_and_integral_eq_of_nonneg
    (fun x hx => hasDerivAt_momentPrim hx) (fun x hx => ?_) tendsto_momentPrim_zero
    tendsto_momentPrim_one
  · refine ⟨h.1, ?_⟩
    rw [h.2, sub_zero]
  · rw [← piHat_photonVar hx]
    exact mul_nonneg (sq_nonneg x) (piHat_nonneg (div_nonneg (sq_nonneg x) (by linarith [hx.2])))

theorem moment_integrand_ae :
    (fun x => x ^ 2 * piHat (x ^ 2 / (1 - x))) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun x => x ^ 2 * piHatX x := by
  filter_upwards [QED.TwoLoop.VPUnit.ae_mem_Ioo] with x hx
  rw [piHat_photonVar hx]

/-- The moment integrand `x² Π̂(x²/(1-x))` is interval integrable on `[0,1]`. -/
theorem intervalIntegrable_piHatMoment :
    IntervalIntegrable (fun x => x ^ 2 * piHat (x ^ 2 / (1 - x))) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
    intervalIntegrable_and_integral_moment_closed.1).congr moment_integrand_ae.symm

/-- **The first moment.** `∫₀¹ x² Π̂(x²/(1-x)) dx = 41/18 - 2π²/9`. -/
theorem integral_piHatMoment :
    ∫ x in (0 : ℝ)..1, x ^ 2 * piHat (x ^ 2 / (1 - x)) = 41 / 18 - 2 * π ^ 2 / 9 := by
  rw [← intervalIntegrable_and_integral_moment_closed.2,
    intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  exact integral_congr_ae moment_integrand_ae

end QED.Chain.ChainB
