/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.CountertermLimitProduct

/-!
# Set (a): the auxiliary loop does not vanish at fixed `ε`

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`.
A one-loop integrand times the auxiliary loop `(ℓ₁² + M² - iε)⁻³` is a two-loop integrand whose
joint energy-first integral is the product of the two one-loop integrals
(`QED.TwoLoop.CountertermLimit.jointEnergyFirstIntegral_two_mul`). To divide by the auxiliary
loop at a **fixed** `ε > 0` (not only in the limit, `auxLimit_ne_zero`) it must not vanish there:

* **`setASpec_aux_ne_zero`**: for `0 < M`, `0 < ε` and `2 ε ≤ M²` the energy-first integral of
  `(ℓ² + M² - iε)⁻³` is not zero. Its spatial integrand
  `-(3π/8) (-(v² + M² - iε))^{-5/2}` has positive imaginary part: the argument of
  `-(v² + M²) + iε` is `π - arcsin(ε/|z|)` with `arcsin(ε/|z|) < π/5`, so the phase
  `-(5/2) arg` lies in `(-5π/2, -2π)`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Real

namespace QED.ChainProof.SetASpec

open QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge

/-- The argument bound behind the sign of the auxiliary integrand. -/
theorem setASpec_arcsin_lt {x : ℝ} (hx : x ≤ 1 / 2) : Real.arcsin x < π / 5 := by
  rw [Real.arcsin_lt_iff_lt_sin' ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩]
  have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two (x := π / 6) (y := π / 5)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [Real.sin_pi_div_six] at h
  linarith

/-- **The imaginary part of the auxiliary spatial integrand is positive** when `2 ε ≤ M²`. -/
theorem setASpec_im_auxSpatial_pos {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) (h : 2 * ε ≤ M ^ 2)
    (v : Fin 3 → ℝ) : 0 < (auxSpatial M ε v).im := by
  set b : ℝ := ∑ k, v k ^ 2 + M ^ 2 with hb
  have hb0 : M ^ 2 ≤ b := by
    have : 0 ≤ ∑ k, v k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
    linarith
  set z : ℂ := -(((b : ℝ) : ℂ) - (ε : ℂ) * I) with hz
  have hzre : z.re = -b := re_neg_aux b ε
  have hzim : z.im = ε := im_neg_aux b ε
  have hz0 : z ≠ 0 := aux_ne_zero hM ε v
  have hnorm : b ≤ ‖z‖ := by
    have := Complex.abs_re_le_norm z
    rw [hzre, abs_neg, abs_of_pos (by positivity)] at this
    exact this
  have hnpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  -- the argument
  set a : ℝ := Real.arcsin (ε / ‖z‖) with ha
  have harg : arg z = π - a := by
    rw [Complex.arg_of_re_neg_of_im_nonneg (by rw [hzre]; linarith [sq_pos_of_pos hM])
      (by rw [hzim]; exact hε.le), neg_im, hzim, neg_div, Real.arcsin_neg]
    ring
  have ha0 : 0 ≤ a := Real.arcsin_nonneg.mpr (by positivity)
  have ha1 : a < π / 5 := by
    refine setASpec_arcsin_lt ?_
    rw [div_le_iff₀ hnpos]
    linarith
  -- the imaginary part
  have hcp : z ^ (-(5 / 2 : ℂ)) = exp (log z * (-(5 / 2 : ℂ))) := cpow_def_of_ne_zero hz0 _
  have him : (log z * (-(5 / 2 : ℂ))).im = -(5 / 2) * arg z := by
    rw [mul_im, log_re, log_im]
    norm_num
    ring
  have hsin : Real.sin (-(5 / 2) * arg z) = -Real.cos (5 / 2 * a) := by
    rw [harg]
    have e : -(5 / 2) * (π - a) = (5 / 2 * a - π / 2) - 2 * π := by ring
    rw [e, Real.sin_sub_two_pi, Real.sin_sub_pi_div_two]
  have hcos : 0 < Real.cos (5 / 2 * a) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have key : (auxSpatial M ε v).im =
      3 * π / 8 * (Real.exp (log z * (-(5 / 2 : ℂ))).re * Real.cos (5 / 2 * a)) := by
    rw [auxSpatial, ← hb, ← hz, hcp, neg_im, mul_im, exp_im, exp_re, him, hsin]
    have h1 : (3 * π / 8 : ℂ).re = 3 * π / 8 := by
      rw [show (3 * π / 8 : ℂ) = ((3 * π / 8 : ℝ) : ℂ) by push_cast; ring, ofReal_re]
    have h2 : (3 * π / 8 : ℂ).im = 0 := by
      rw [show (3 * π / 8 : ℂ) = ((3 * π / 8 : ℝ) : ℂ) by push_cast; ring, ofReal_im]
    rw [h1, h2]
    ring
  rw [key]
  have := Real.exp_pos (log z * (-(5 / 2 : ℂ))).re
  positivity

theorem setASpec_integrable_auxSpatial {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    Integrable (auxSpatial M ε) := by
  have hbnd : Integrable fun v : Fin 3 → ℝ =>
      3 * π / 8 * (∑ k, v k ^ 2 + M ^ 2) ^ (-(5 / 2 : ℝ)) :=
    (QED.Integration.integrable_sum_sq_add_rpow (by positivity) (by norm_num)).const_mul _
  exact hbnd.mono' (continuous_auxSpatial M hε).aestronglyMeasurable
    (Eventually.of_forall fun v => norm_auxSpatial_le hM ε v)

/-- **The auxiliary loop does not vanish at fixed `ε`** when `2 ε ≤ M²`. -/
theorem setASpec_aux_ne_zero {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) (h : 2 * ε ≤ M ^ 2) :
    QED.OneLoop.energyFirstIntegral (fun k => ((propDenom M ε k)⁻¹) ^ 3) ≠ 0 := by
  have e : QED.OneLoop.energyFirstIntegral (fun k => ((propDenom M ε k)⁻¹) ^ 3) =
      ∫ v, auxSpatial M ε v := by
    unfold QED.OneLoop.energyFirstIntegral
    exact integral_congr_ae (Eventually.of_forall fun v => integral_aux_time M hε v)
  rw [e]
  intro h0
  have hI := setASpec_integrable_auxSpatial hM hε
  have him : ∫ v, (auxSpatial M ε v).im = (∫ v, auxSpatial M ε v).im := integral_im hI
  rw [h0, zero_im] at him
  have hpos : 0 < ∫ v, (auxSpatial M ε v).im := by
    have hc : Continuous fun v => (auxSpatial M ε v).im :=
      continuous_im.comp (continuous_auxSpatial M hε)
    rw [integral_pos_iff_support_of_nonneg (fun v => (setASpec_im_auxSpatial_pos hM hε h v).le)
      hI.im]
    have hs : Function.support (fun v => (auxSpatial M ε v).im) = univ :=
      eq_univ_of_forall fun v => (setASpec_im_auxSpatial_pos hM hε h v).ne'
    rw [hs, Measure.measure_univ_pos]
    exact NeZero.ne volume
  linarith

end QED.ChainProof.SetASpec

end
