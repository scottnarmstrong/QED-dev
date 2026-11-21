/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.OneLoopSchwinger
public import QED.DimReg.BetaPrime
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The one-loop on-shell self-energy: convergence and closed form of the Schwinger integral

For the Euclidean one-loop on-shell self-energy kernel of `QED.DimReg.OneLoopSchwinger`
(`U = x₀ + x₁`, `F = x₁²`) we prove absolute convergence and evaluate

  `∫_{(0,∞)²} x₀^{a-1} x₁^{b-1} U^{-d/2} e^{-F/U} dx`
  `  = Γ(a + b - d/2) Γ(a) Γ(d - 2a - b) / Γ(d - a - b)`

for `0 < re a`, `0 < re (a + b - d/2)`, `0 < re (d - 2a - b)`. In each fiber `x₁ = y` we
substitute `x₀ = y s` (a one-variable linear substitution), which turns the integrand times the
Jacobian into `s^{a-1} (1 + s)^{-d/2} · y^{a+b-d/2-1} e^{-y/(1+s)}`
(`QED.DimReg.OneLoopSchwinger.substIntegrand`). By Tonelli, the `y`-integral is a Gamma integral
`(1 + s)^{a+b-d/2} Γ(a + b - d/2)` and the `s`-integral is the Beta integral of the second kind
(`QED.DimReg.integral_betaPrime`). Integrability is transferred fiberwise through
`integrable_prod_iff`, so no two-dimensional change of variables is needed.

Normalized by `Γ(a) Γ(b)`, the integral is `phi a b d = Γ(a + b - d/2) Γ(d - 2a - b) /
(Γ(b) Γ(d - a - b))` (`QED.DimReg.OneLoopSchwinger.schw_eq_phi`). `phi` is the meromorphic
continuation in all three variables.

## Main results

* `QED.DimReg.OneLoopSchwinger.conv_of_re`: convergence.
* `QED.DimReg.OneLoopSchwinger.mellin₂_eq`: the closed form.
* `QED.DimReg.OneLoopSchwinger.schw_eq_phi`: the Γ-normalized closed form.
-/

@[expose] public section

open MeasureTheory Set Complex Filter

namespace QED.DimReg.OneLoopSchwinger

/-! ### The Gamma fiber -/

/-- The scaled Gamma integrand `y ^ (e - 1) e ^ (-r y)`. -/
noncomputable def gammaFiber (e : ℂ) (r y : ℝ) : ℂ := (y : ℂ) ^ (e - 1) * cexp (-((r * y : ℝ) : ℂ))

theorem norm_gammaFiber (e : ℂ) (r : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖gammaFiber e r y‖ = y ^ (e.re - 1) * Real.exp (-(r * y)) := by
  rw [gammaFiber, norm_mul, norm_cpow_eq_rpow_re_of_pos hy, Complex.norm_exp]
  simp

theorem integrableOn_gammaFiber {e : ℂ} (he : 0 < e.re) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (gammaFiber e r) (Ioi 0) := by
  have hR := integrableOn_rpow_mul_exp_neg_mul_rpow (s := e.re - 1) (p := 1) (b := r)
    (by linarith) one_pos hr
  have hm : AEStronglyMeasurable (gammaFiber e r) (volume.restrict (Ioi 0)) := by
    unfold gammaFiber; fun_prop
  refine (integrable_norm_iff hm).mp (hR.congr_fun (fun y hy => ?_) measurableSet_Ioi)
  simp only [norm_gammaFiber e r hy, Real.rpow_one, neg_mul]

theorem integral_gammaFiber {e : ℂ} (he : 0 < e.re) {r : ℝ} (hr : 0 < r) :
    ∫ y in Ioi (0 : ℝ), gammaFiber e r y = ((1 / r : ℝ) : ℂ) ^ e * Gamma e := by
  have h := integral_cpow_mul_exp_neg_mul_Ioi he hr
  push_cast at h ⊢
  rw [← h]
  simp only [gammaFiber, ofReal_mul]

theorem integral_norm_gammaFiber {e : ℂ} (he : 0 < e.re) {r : ℝ} (hr : 0 < r) :
    ∫ y in Ioi (0 : ℝ), ‖gammaFiber e r y‖ = (1 / r) ^ e.re * Real.Gamma e.re := by
  rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi he hr]
  exact setIntegral_congr_fun measurableSet_Ioi fun y hy => norm_gammaFiber e r hy

/-! ### The substituted integrand -/

/-- The prefactor `s ^ (a - 1) (1 + s) ^ (-d / 2)` of the substituted integrand. -/
noncomputable def substPre (a d : ℂ) (s : ℝ) : ℂ :=
  (s : ℂ) ^ (a - 1) * ((1 + s : ℝ) : ℂ) ^ (-(d / 2))

/-- The integrand after the substitution `x₀ = y s`, `x₁ = y`, times the Jacobian `y`:
`s ^ (a - 1) (1 + s) ^ (-d / 2) y ^ (a + b - d / 2 - 1) e ^ (-y / (1 + s))`. -/
noncomputable def substIntegrand (a b d : ℂ) (z : ℝ × ℝ) : ℂ :=
  substPre a d z.1 * gammaFiber (a + b - d / 2) (1 + z.1)⁻¹ z.2

theorem measurable_integrand (a b d : ℂ) : Measurable (integrand a b d) := by
  unfold integrand kernel; fun_prop

theorem measurable_substIntegrand (a b d : ℂ) : Measurable (substIntegrand a b d) := by
  unfold substIntegrand substPre gammaFiber; fun_prop

theorem norm_substPre (a d : ℂ) {s : ℝ} (hs : 0 < s) :
    ‖substPre a d s‖ = s ^ (a.re - 1) * (1 + s) ^ (-(d.re / 2)) := by
  rw [substPre, norm_mul, norm_cpow_eq_rpow_re_of_pos hs,
    norm_cpow_eq_rpow_re_of_pos (by linarith)]
  simp

theorem norm_betaPrime (a c : ℂ) {s : ℝ} (hs : 0 < s) :
    ‖betaPrimeIntegrand a c 1 s‖ = s ^ (a.re - 1) * (1 + s) ^ (-(a.re + c.re)) := by
  rw [betaPrimeIntegrand, norm_mul, norm_cpow_eq_rpow_re_of_pos hs,
    norm_cpow_eq_rpow_re_of_pos (by linarith)]
  simp

theorem integrableOn_substIntegrand {a b d : ℂ} (ha : 0 < a.re) (he : 0 < (a + b - d / 2).re)
    (hc : 0 < (d - 2 * a - b).re) : IntegrableOn (substIntegrand a b d) quad := by
  have hB := (integrableOn_betaPrime ha hc one_pos).norm.const_mul
    (Real.Gamma (a + b - d / 2).re)
  unfold IntegrableOn at hB ⊢
  rw [quad, Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [integrable_prod_iff (measurable_substIntegrand a b d).aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have h1 : 0 < 1 + s := by linarith [hs.out]
    simpa only [substIntegrand] using
      (integrableOn_gammaFiber he (r := (1 + s)⁻¹) (inv_pos.mpr h1)).const_mul (substPre a d s)
  · refine hB.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have h1 : 0 < 1 + s := by linarith [hs.out]
    simp only [substIntegrand, norm_mul]
    rw [integral_const_mul, integral_norm_gammaFiber he (inv_pos.mpr h1), norm_substPre a d hs,
      norm_betaPrime a _ hs, one_div, inv_inv]
    have hsplit : (1 + s) ^ (-(a.re + (d - 2 * a - b).re)) =
        (1 + s) ^ (-(d.re / 2)) * (1 + s) ^ (a + b - d / 2).re := by
      rw [← Real.rpow_add h1]
      congr 1
      simp
      ring
    rw [hsplit]
    ring

theorem integral_substIntegrand {a b d : ℂ} (ha : 0 < a.re) (he : 0 < (a + b - d / 2).re)
    (hc : 0 < (d - 2 * a - b).re) :
    ∫ z in quad, substIntegrand a b d z =
      Gamma (a + b - d / 2) * (Gamma a * Gamma (d - 2 * a - b) / Gamma (d - a - b)) := by
  have hS := integrableOn_substIntegrand ha he hc
  unfold IntegrableOn at hS
  rw [quad, Measure.volume_eq_prod, ← Measure.prod_restrict] at hS ⊢
  rw [integral_prod _ hS]
  have hB := integral_betaPrime ha hc one_pos
  rw [ofReal_one, one_cpow, one_mul, show a + (d - 2 * a - b) = d - a - b by ring] at hB
  rw [← hB, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have h1 : 0 < 1 + s := by linarith [hs.out]
  have h1' : ((1 + s : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h1.ne'
  simp only [substIntegrand]
  rw [integral_const_mul, integral_gammaFiber he (inv_pos.mpr h1), one_div, inv_inv]
  simp only [substPre, betaPrimeIntegrand, one_mul]
  rw [show -(a + (d - 2 * a - b)) = -(d / 2) + (a + b - d / 2) by ring, cpow_add _ _ h1']
  ring

/-! ### The substitution `x₀ = y s` in each fiber -/

theorem mul_integrand_mul {a b d : ℂ} {y s : ℝ} (hy : 0 < y) (hs : 0 < s) :
    (y : ℂ) * integrand a b d (y * s, y) = substIntegrand a b d (s, y) := by
  have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  have e1 : ((y * s : ℝ) : ℂ) ^ (a - 1) = (y : ℂ) ^ (a - 1) * (s : ℂ) ^ (a - 1) := by
    rw [ofReal_mul, mul_cpow_ofReal_nonneg hy.le hs.le]
  have e2 : ((y * s + y : ℝ) : ℂ) ^ (-(d / 2)) =
      (y : ℂ) ^ (-(d / 2)) * ((1 + s : ℝ) : ℂ) ^ (-(d / 2)) := by
    rw [show y * s + y = y * (1 + s) by ring, ofReal_mul,
      mul_cpow_ofReal_nonneg hy.le (by linarith)]
  have e3 : y ^ 2 / (y * s + y) = (1 + s)⁻¹ * y := by
    have : (1 + s) ≠ 0 := by linarith
    field_simp
    ring
  have e4 : (y : ℂ) ^ (a + b - d / 2 - 1) =
      (y : ℂ) ^ (a - 1) * (y : ℂ) ^ (b - 1) * (y : ℂ) ^ (-(d / 2)) * y := by
    rw [show a + b - d / 2 - 1 = (a - 1) + (b - 1) + (-(d / 2)) + 1 by ring, cpow_add _ _ hy',
      cpow_add _ _ hy', cpow_add _ _ hy', cpow_one]
  simp only [integrand, kernel, substIntegrand, substPre, gammaFiber]
  rw [e1, e2, e3, e4]
  ring

/-- **Convergence of the one-loop Schwinger integral** for `0 < re a`, `0 < re (a + b - d/2)`,
`0 < re (d - 2a - b)`. -/
theorem conv_of_re {a b d : ℂ} (ha : 0 < a.re) (he : 0 < (a + b - d / 2).re)
    (hc : 0 < (d - 2 * a - b).re) : Conv a b d := by
  have hS := integrableOn_substIntegrand ha he hc
  unfold IntegrableOn at hS
  unfold Conv IntegrableOn
  rw [quad, Measure.volume_eq_prod, ← Measure.prod_restrict] at hS ⊢
  rw [integrable_prod_iff' (measurable_integrand a b d).aestronglyMeasurable]
  constructor
  · filter_upwards [hS.prod_left_ae, ae_restrict_mem measurableSet_Ioi] with y h hy
    have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.out.ne'
    have h2 := (integrableOn_Ioi_comp_mul_left_iff (fun x => integrand a b d (x, y)) 0 hy.out).mp
      (IntegrableOn.congr_fun (h.const_mul (y : ℂ)⁻¹) (fun s hs => by
        rw [← mul_integrand_mul hy.out hs, ← mul_assoc, inv_mul_cancel₀ hy', one_mul])
        measurableSet_Ioi)
    rwa [mul_zero] at h2
  · refine hS.integral_norm_prod_right.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have h := integral_comp_mul_left_Ioi (fun x => ‖integrand a b d (x, y)‖) 0 hy.out
    rw [mul_zero] at h
    rw [eq_inv_smul_iff₀ hy.out.ne'] at h
    rw [← h, smul_eq_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    rw [← mul_integrand_mul hy.out hs, norm_mul, norm_real, Real.norm_of_nonneg hy.out.le]

/-- **Closed form of the one-loop Schwinger integral.** In its region of convergence,
`∫_{(0,∞)²} x₀ ^ (a - 1) x₁ ^ (b - 1) U ^ (-d/2) e ^ (-F/U) dx =
Γ(a + b - d/2) Γ(a) Γ(d - 2a - b) / Γ(d - a - b)`. -/
theorem mellin₂_eq {a b d : ℂ} (ha : 0 < a.re) (he : 0 < (a + b - d / 2).re)
    (hc : 0 < (d - 2 * a - b).re) :
    mellin₂ a b d =
      Gamma (a + b - d / 2) * (Gamma a * Gamma (d - 2 * a - b) / Gamma (d - a - b)) := by
  have hC := conv_of_re ha he hc
  have hS := integrableOn_substIntegrand ha he hc
  rw [← integral_substIntegrand ha he hc]
  unfold IntegrableOn at hS
  unfold Conv IntegrableOn at hC
  unfold mellin₂
  rw [quad, Measure.volume_eq_prod, ← Measure.prod_restrict] at hS hC ⊢
  rw [integral_prod_symm _ hC, integral_prod_symm _ hS]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have h := integral_comp_mul_left_Ioi (fun x => integrand a b d (x, y)) 0 hy.out
  rw [mul_zero, eq_inv_smul_iff₀ hy.out.ne'] at h
  rw [← h, ← integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  rw [← mul_integrand_mul hy.out hs, Complex.real_smul]

/-- The closed form `Γ(a + b - d/2) Γ(d - 2a - b) / (Γ(b) Γ(d - a - b))` of the Γ-normalized
integral, written with `Γ⁻¹` (an entire function), so that it is meromorphic in `(a, b, d)` and
vanishes on the scaleless sector `b ∈ {0, -1, -2, …}`. -/
noncomputable def phi (a b d : ℂ) : ℂ :=
  Gamma (a + b - d / 2) * Gamma (d - 2 * a - b) * (Gamma b)⁻¹ * (Gamma (d - a - b))⁻¹

/-- In the region of convergence the Γ-normalized Schwinger integral is `phi`. -/
theorem schw_eq_phi {a b d : ℂ} (ha : 0 < a.re) (he : 0 < (a + b - d / 2).re)
    (hc : 0 < (d - 2 * a - b).re) : schw a b d = phi a b d := by
  have hga : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  rw [schw, mellin₂_eq ha he hc, phi]
  field_simp

end QED.DimReg.OneLoopSchwinger
