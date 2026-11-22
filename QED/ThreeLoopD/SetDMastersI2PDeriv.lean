/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI2Analytic
public import QED.ThreeLoopD.SetDMastersI9KTaylor

/-!
# Set (d), master `I₂`: the derivatives of `P` at `ε = 0` as real integrals

On the domain, `𝒰 ^ (-2 + 4ε) ℱ ^ (-3ε) = exp (-2 log 𝒰 + ε L)` with
`L = 4 log 𝒰 - 3 log ℱ` (`QED.ThreeLoopD.i2PL`), so the `k`-th `ε`-derivative of the integrand
is `(1 - w) Lᵏ exp (-2 log 𝒰 + ε L)` (`QED.ThreeLoopD.i2PD`). All of them are dominated by
multiples of the majorant `QED.ThreeLoopD.i2Maj` of `QED.ThreeLoopD.SetDMastersI2Analytic`
(Cauchy estimates, `QED.ThreeLoopD.iteratedDeriv_integral_of_chain`, radii `1/20` and
`ρ = 1/60`), which gives, for `k ≤ 2`,

  `P⁽ᵏ⁾(0) = ∫ (1 - w) Lᵏ / 𝒰²` (`QED.ThreeLoopD.iteratedDeriv_i2PInt`).

## Main results

* `QED.ThreeLoopD.iteratedDeriv_i2PInt`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.ThreeLoopD

/-- `L = 4 log 𝒰 - 3 log ℱ`, the coefficient of `ε` in the exponent of the integrand. -/
noncomputable def i2PL (z : ℝ × ℝ × ℝ × ℝ × ℝ) : ℝ :=
  4 * Real.log (i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) -
    3 * Real.log (i2F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)

/-- **The `k`-th `ε`-derivative of the integrand**: `(1 - w) Lᵏ exp (-2 log 𝒰 + ε L)`. -/
noncomputable def i2PD (k : ℕ) (ε : ℂ) (z : ℝ × ℝ × ℝ × ℝ × ℝ) : ℂ :=
  ((1 - z.2.1 : ℝ) : ℂ) *
    i9KExp k (-2 * Real.log (i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)) (i2PL z) ε

theorem i2PD_zero_eq {z : ℝ × ℝ × ℝ × ℝ × ℝ} (hz : z ∈ i2Dom) (ε : ℂ) :
    i2PD 0 ε z = i2Integrand ε z := by
  obtain ⟨hU, hF⟩ := i2UF_pos hz
  unfold i2PD i9KExp i2Integrand i2PL
  rw [i9_cpow_eq_exp hU, i9_cpow_eq_exp hF, pow_zero, one_mul, mul_assoc, ← exp_add]
  congr 2
  push_cast
  ring

theorem i2PD_at_zero {z : ℝ × ℝ × ℝ × ℝ × ℝ} (hz : z ∈ i2Dom) (k : ℕ) :
    i2PD k 0 z = (((1 - z.2.1) * i2PL z ^ k / i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 :
      ℝ) : ℂ) := by
  obtain ⟨hU, -⟩ := i2UF_pos hz
  have he : Real.exp (-2 * Real.log (i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)) =
      1 / i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 := by
    rw [show -2 * Real.log (i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) =
      Real.log ((i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2)⁻¹) by
        rw [Real.log_inv, Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity), one_div]
  unfold i2PD i9KExp
  rw [zero_mul, add_zero, ← ofReal_exp, he]
  push_cast
  ring

/-- **`P⁽ᵏ⁾(0) = ∫ (1 - w) Lᵏ / 𝒰²`** for `k ≤ 2`. -/
theorem iteratedDeriv_i2PInt {k : ℕ} (hk : k ≤ 2) :
    iteratedDeriv k i2PInt 0 = ((∫ z in i2Dom, (1 - z.2.1) * i2PL z ^ k /
      i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 : ℝ) : ℂ) := by
  have hS : MeasurableSet i2Dom :=
    measurableSet_Ioo.prod (measurableSet_Ioo.prod (measurableSet_Ioi.prod
      (measurableSet_Ioi.prod measurableSet_Ioi)))
  have e : i2PInt = fun ε => ∫ z in i2Dom, i2PD 0 ε z := funext fun ε => by
    rw [i2PInt_eq]
    exact setIntegral_congr_fun hS fun z hz => (i2PD_zero_eq hz ε).symm
  have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk
  rw [e, iteratedDeriv_integral_of_chain (D := i2PD) (R := 1 / 20) (ρ := 1 / 60) (b := i2Maj)
    (by norm_num) (Filter.Eventually.of_forall fun z k ε =>
      (hasDerivAt_i9KExp k _ _ ε).const_mul _)
    (ae_restrict_of_forall_mem hS fun z hz ε hε => by
      rw [i2PD_zero_eq hz]; exact norm_i2Integrand_le hε hz)
    integrable_i2Maj (fun k ε => by
      have : Measurable (i2PD k ε) := by
        unfold i2PD i9KExp i2PL i2F i2U i2LineA i2LineB i2LineC; fun_prop
      exact this.aestronglyMeasurable) k 0 (by simp; linarith),
    ← integral_complex_ofReal]
  exact setIntegral_congr_fun hS fun z hz => i2PD_at_zero hz k

end QED.ThreeLoopD
