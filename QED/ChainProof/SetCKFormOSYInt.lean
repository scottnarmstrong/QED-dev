/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: two elementary `Y`-integrals

Helper level (no frozen statement). The two branches of the outer self-energy weight
`scOutSW` (`SetCKScOutSDom`), as functions of the Feynman parameter `Y`, are elementary:
- above the threshold, a Laurent polynomial `c₂/Y² + c₁/Y + c₀ + d Y` plus `(e₀ + e₁ Y) log Y`;
  **`formOS_integral_hi`** integrates it over `(a, 1)`, `0 < a ≤ 1`;
- below the threshold, `c₀ + c₁ Y + (e₀ + e₁ Y) log Y + (f₀ + f₁ Y) log(1 - Y)`;
  **`formOS_integral_lo`** integrates it over `(0, a]`, `0 < a < 1`.
Both are the fundamental theorem of calculus with explicit antiderivatives.
-/

@[expose] public section

open Real Set MeasureTheory

namespace QED.ChainProof.SetCK

/-- The integrand above the threshold. -/
noncomputable def formOSHi (c₂ c₁ c₀ d e₀ e₁ Y : ℝ) : ℝ :=
  c₂ / Y ^ 2 + c₁ / Y + c₀ + d * Y + (e₀ + e₁ * Y) * log Y

/-- Its antiderivative. -/
noncomputable def formOSHiP (c₂ c₁ c₀ d e₀ e₁ Y : ℝ) : ℝ :=
  -(c₂ / Y) + c₁ * log Y + c₀ * Y + d * Y ^ 2 / 2 + e₀ * (Y * log Y - Y) +
    e₁ * (Y * (Y * log Y) / 2 - Y ^ 2 / 4)

/-- The integrand below the threshold. -/
noncomputable def formOSLo (c₀ c₁ e₀ e₁ f₀ f₁ Y : ℝ) : ℝ :=
  c₀ + c₁ * Y + (e₀ + e₁ * Y) * log Y + (f₀ + f₁ * Y) * log (1 - Y)

/-- Its antiderivative (vanishing at `0`). -/
noncomputable def formOSLoP (c₀ c₁ e₀ e₁ f₀ f₁ Y : ℝ) : ℝ :=
  c₀ * Y + c₁ * Y ^ 2 / 2 + e₀ * (Y * log Y - Y) + e₁ * (Y * (Y * log Y) / 2 - Y ^ 2 / 4) +
    f₀ * (-((1 - Y) * log (1 - Y)) - Y) + f₁ * ((Y ^ 2 - 1) * log (1 - Y) / 2 - Y ^ 2 / 4 - Y / 2)

theorem hasDerivAt_formOSHiP (c₂ c₁ c₀ d e₀ e₁ : ℝ) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (formOSHiP c₂ c₁ c₀ d e₀ e₁) (formOSHi c₂ c₁ c₀ d e₀ e₁ Y) Y := by
  have hY0 := hY.ne'
  have hl := hasDerivAt_log hY0
  have hi : HasDerivAt (fun Y : ℝ => Y⁻¹) (-(Y ^ 2)⁻¹) Y := hasDerivAt_inv hY0
  have h1 := hasDerivAt_id' Y
  have hYl := h1.mul hl
  have h := ((((((hi.const_mul c₂).neg.add (hl.const_mul c₁)).add (h1.const_mul c₀)).add
    (((hasDerivAt_pow 2 Y).const_mul d).div_const 2)).add
    ((hYl.sub h1).const_mul e₀)).add
    ((((h1.mul hYl).div_const 2).sub ((hasDerivAt_pow 2 Y).div_const 4)).const_mul e₁))
  unfold formOSHiP formOSHi
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  field_simp
  ring

theorem hasDerivAt_formOSLoP (c₀ c₁ e₀ e₁ f₀ f₁ : ℝ) {Y : ℝ} (hY : 0 < Y) (hY1 : Y < 1) :
    HasDerivAt (formOSLoP c₀ c₁ e₀ e₁ f₀ f₁) (formOSLo c₀ c₁ e₀ e₁ f₀ f₁ Y) Y := by
  have hY0 := hY.ne'
  have h1Y : (1 - Y) ≠ 0 := by linarith
  have hl := hasDerivAt_log hY0
  have h1 := hasDerivAt_id' Y
  have hm : HasDerivAt (fun Y : ℝ => 1 - Y) (-1) Y := by
    simpa using (hasDerivAt_id' Y).const_sub 1
  have hl1 := hm.log h1Y
  have hYl := h1.mul hl
  have h := (((((h1.const_mul c₀).add (((hasDerivAt_pow 2 Y).const_mul c₁).div_const 2)).add
    ((hYl.sub h1).const_mul e₀)).add
    ((((h1.mul hYl).div_const 2).sub ((hasDerivAt_pow 2 Y).div_const 4)).const_mul e₁)).add
    (((hm.mul hl1).neg.sub h1).const_mul f₀)).add
    ((((((hasDerivAt_pow 2 Y).sub_const 1).mul hl1).div_const 2).sub
      ((hasDerivAt_pow 2 Y).div_const 4)).sub (h1.div_const 2) |>.const_mul f₁)
  unfold formOSLoP formOSLo
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- **The integral above the threshold**: for `0 < a ≤ 1`, the integrand is integrable on
`(a, 1)` with integral `P(1) - P(a)`. -/
theorem formOS_integral_hi (c₂ c₁ c₀ d e₀ e₁ : ℝ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    IntegrableOn (formOSHi c₂ c₁ c₀ d e₀ e₁) (Ioo a 1) ∧
      ∫ Y in Ioo a 1, formOSHi c₂ c₁ c₀ d e₀ e₁ Y =
        formOSHiP c₂ c₁ c₀ d e₀ e₁ 1 - formOSHiP c₂ c₁ c₀ d e₀ e₁ a := by
  have hc : ContinuousOn (formOSHi c₂ c₁ c₀ d e₀ e₁) (Icc a 1) := by
    unfold formOSHi
    have hne : ∀ Y ∈ Icc a 1, Y ≠ 0 := fun Y hY => (ha.trans_le hY.1).ne'
    refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.add (ContinuousOn.add
      (continuousOn_const.div (continuousOn_pow 2) fun Y hY => pow_ne_zero 2 (hne Y hY))
      (continuousOn_const.div continuousOn_id hne)) continuousOn_const) (by fun_prop)) ?_
    exact ContinuousOn.mul (by fun_prop) (continuousOn_log.mono fun Y hY => hne Y hY)
  have hi : IntegrableOn (formOSHi c₂ c₁ c₀ d e₀ e₁) (Ioo a 1) :=
    hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  refine ⟨hi, ?_⟩
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha1]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun Y hY => ?_)
    ((hc.mono (uIcc_of_le ha1).subset).intervalIntegrable)
  rw [uIcc_of_le ha1] at hY
  exact hasDerivAt_formOSHiP c₂ c₁ c₀ d e₀ e₁ (ha.trans_le hY.1)

theorem formOSLoP_zero (c₀ c₁ e₀ e₁ f₀ f₁ : ℝ) : formOSLoP c₀ c₁ e₀ e₁ f₀ f₁ 0 = 0 := by
  simp [formOSLoP]

/-- **The integral below the threshold**: for `0 < a < 1`, the integrand is integrable on
`(0, a]` with integral `P(a)`. -/
theorem formOS_integral_lo (c₀ c₁ e₀ e₁ f₀ f₁ : ℝ) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    IntegrableOn (formOSLo c₀ c₁ e₀ e₁ f₀ f₁) (Ioc 0 a) ∧
      ∫ Y in Ioc 0 a, formOSLo c₀ c₁ e₀ e₁ f₀ f₁ Y = formOSLoP c₀ c₁ e₀ e₁ f₀ f₁ a := by
  have hne : ∀ Y ∈ uIcc 0 a, 1 - Y ≠ 0 := fun Y hY => by
    rw [uIcc_of_le ha.le] at hY
    linarith [hY.2]
  have hl1 : ContinuousOn (fun Y : ℝ => log (1 - Y)) (uIcc 0 a) :=
    continuousOn_log.comp (by fun_prop) fun Y hY => hne Y hY
  have iL : IntervalIntegrable (fun Y => (e₀ + e₁ * Y) * log Y) volume 0 a :=
    intervalIntegral.intervalIntegrable_log'.continuousOn_mul (by fun_prop)
  have iP : IntervalIntegrable (fun Y => c₀ + c₁ * Y) volume 0 a :=
    (by fun_prop : Continuous fun Y : ℝ => c₀ + c₁ * Y).intervalIntegrable 0 a
  have iF : IntervalIntegrable (fun Y => (f₀ + f₁ * Y) * log (1 - Y)) volume 0 a :=
    (ContinuousOn.mul (by fun_prop) hl1).intervalIntegrable
  have hi : IntervalIntegrable (formOSLo c₀ c₁ e₀ e₁ f₀ f₁) volume 0 a :=
    (iP.add iL).add iF
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).1 hi, ?_⟩
  rw [← intervalIntegral.integral_of_le ha.le]
  have hc : ContinuousOn (formOSLoP c₀ c₁ e₀ e₁ f₀ f₁) (Icc 0 a) := by
    rw [← uIcc_of_le ha.le]
    unfold formOSLoP
    have hYl : Continuous fun Y : ℝ => Y * log Y := continuous_mul_log
    have hm : ContinuousOn (fun Y : ℝ => (1 - Y) * log (1 - Y)) (uIcc 0 a) :=
      (continuous_mul_log.comp (continuous_const.sub continuous_id)).continuousOn
    refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_) ?_) ?_
    · fun_prop
    · exact ((hYl.sub continuous_id).const_mul e₀).continuousOn
    · exact ((((continuous_id.mul hYl).div_const 2).sub (by fun_prop)).const_mul e₁).continuousOn
    · exact (hm.neg.sub continuousOn_id).const_mul f₀
    · exact (((((by fun_prop : Continuous fun Y : ℝ => Y ^ 2 - 1).continuousOn.mul hl1).div_const
        2).sub ((continuous_pow 2).div_const 4).continuousOn).sub
        (continuous_id.div_const 2).continuousOn).const_mul f₁
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.le hc
    (fun Y hY => hasDerivAt_formOSLoP c₀ c₁ e₀ e₁ f₀ f₁ hY.1 (hY.2.trans ha1)) hi,
    formOSLoP_zero, sub_zero]

end QED.ChainProof.SetCK

end
