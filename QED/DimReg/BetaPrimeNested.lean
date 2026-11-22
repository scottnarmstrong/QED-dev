/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.BetaPrime
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Iterated Beta integrals of the second kind

Tools for evaluating multi-dimensional parametric integrals by integrating one variable at a time
against the Beta integral of the second kind (`QED.DimReg.integral_betaPrime`).

* `QED.DimReg.integral_norm_betaPrimeIntegrand`: scaling of the absolute integral,
  `∫₀^∞ ‖t ^ (a - 1) (1 + c t) ^ (-(a + b))‖ dt = c ^ (-re a) · K(a, b)`.
* `QED.DimReg.integrableOn_prod_betaPrime`, `QED.DimReg.integral_prod_betaPrime`: if
  `F (t, w) = A(w) t ^ (a - 1) (1 + c(w) t) ^ (-(a + b))` for `t > 0` and `w ∈ S`, and
  `w ↦ A(w) c(w) ^ (-a)` is integrable on `S`, then `F` is integrable on `(0, ∞) × S` and
  `∫ F = (∫_S A c ^ (-a)) Γ(a) Γ(b) / Γ(a + b)` (Tonelli fiberwise, no change of variables).
* `QED.DimReg.integrableOn_quad_of_subst`, `QED.DimReg.integral_quad_eq_subst`: the fiberwise
  substitution `x₀ = y s` on the quadrant `(0, ∞)²`, `∫ H(x₀, x₁) = ∫ y H(y s, y) d(y, s)`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.DimReg

/-- The norm of the Beta integrand of the second kind. -/
theorem norm_betaPrimeIntegrand (a b : ℂ) {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    ‖betaPrimeIntegrand a b c t‖ = t ^ (a.re - 1) * (1 + c * t) ^ (-(a.re + b.re)) := by
  rw [betaPrimeIntegrand, norm_mul, norm_cpow_eq_rpow_re_of_pos ht,
    norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp

/-- Scaling of the absolute Beta integral:
`∫₀^∞ ‖betaPrimeIntegrand a b c t‖ dt = c ^ (-re a) ∫₀^∞ ‖betaPrimeIntegrand a b 1 t‖ dt`. -/
theorem integral_norm_betaPrimeIntegrand (a b : ℂ) {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), ‖betaPrimeIntegrand a b c t‖ =
      c ^ (-a.re) * ∫ t in Ioi (0 : ℝ), ‖betaPrimeIntegrand a b 1 t‖ := by
  have h := integral_comp_mul_left_Ioi (fun t => ‖betaPrimeIntegrand a b 1 t‖) 0 hc
  rw [mul_zero] at h
  have hc' : c ^ (a.re - 1) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  have e : ∀ t ∈ Ioi (0 : ℝ), ‖betaPrimeIntegrand a b c t‖ =
      (c ^ (a.re - 1))⁻¹ * ‖betaPrimeIntegrand a b 1 (c * t)‖ := by
    intro t ht
    have ht : 0 < t := ht
    rw [norm_betaPrimeIntegrand a b hc ht, norm_betaPrimeIntegrand a b one_pos (by positivity),
      Real.mul_rpow hc.le ht.le, one_mul]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul, h, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← Real.rpow_neg hc.le, ← Real.rpow_neg_one, ← Real.rpow_add hc]
  congr 1
  ring

/-- For positive reals, `((x w⁻¹ : ℝ) : ℂ) ^ s = x ^ s w ^ (-s)`. -/
theorem ofReal_mul_inv_cpow {x w : ℝ} (hx : 0 ≤ x) (hw : 0 < w) (s : ℂ) :
    ((x * w⁻¹ : ℝ) : ℂ) ^ s = (x : ℂ) ^ s * (w : ℂ) ^ (-s) := by
  rw [ofReal_mul, mul_cpow_ofReal_nonneg hx (inv_nonneg.mpr hw.le),
    ofReal_inv_cpow hw]

/-- `((x y : ℝ) : ℂ) ^ r = x ^ r y ^ r` for nonnegative reals. -/
theorem cpow_ofReal_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (r : ℂ) :
    ((x * y : ℝ) : ℂ) ^ r = (x : ℂ) ^ r * (y : ℂ) ^ r := by
  rw [ofReal_mul, mul_cpow_ofReal_nonneg hx hy]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

/-- **Iterated Beta integral, integrability.** If `F (t, w) = A(w) · betaPrimeIntegrand a b
(c(w)) t` on `(0, ∞) × S` with `c > 0` on `S`, and `w ↦ A(w) c(w) ^ (-a)` is integrable on `S`,
then `F` is integrable on `(0, ∞) × S`. -/
theorem integrableOn_prod_betaPrime {S : Set α} (hS : MeasurableSet S) {a b : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) {F : ℝ × α → ℂ} (hFm : AEStronglyMeasurable F
      ((volume.restrict (Ioi 0)).prod (μ.restrict S)))
    {A : α → ℂ} {c : α → ℝ} (hc : ∀ w ∈ S, 0 < c w)
    (hF : ∀ t : ℝ, 0 < t → ∀ w ∈ S, F (t, w) = A w * betaPrimeIntegrand a b (c w) t)
    (hA : IntegrableOn (fun w => A w * ((c w : ℝ) : ℂ) ^ (-a)) S μ) :
    IntegrableOn F (Ioi 0 ×ˢ S) ((volume : Measure ℝ).prod μ) := by
  unfold IntegrableOn
  rw [← Measure.prod_restrict, integrable_prod_iff' hFm]
  constructor
  · filter_upwards [ae_restrict_mem hS] with w hw
    exact IntegrableOn.congr_fun
      (((integrableOn_betaPrime ha hb (hc w hw)).const_mul (A w) : IntegrableOn _ _ _))
      (fun t ht => (hF t ht w hw).symm) measurableSet_Ioi
  · refine (hA.norm.mul_const (∫ t in Ioi (0 : ℝ), ‖betaPrimeIntegrand a b 1 t‖)).congr ?_
    filter_upwards [ae_restrict_mem hS] with w hw
    have hcw := hc w hw
    have e : ∫ t in Ioi (0 : ℝ), ‖F (t, w)‖ =
        ∫ t in Ioi (0 : ℝ), ‖A w‖ * ‖betaPrimeIntegrand a b (c w) t‖ :=
      setIntegral_congr_fun measurableSet_Ioi (fun t ht => by rw [hF t ht w hw, norm_mul])
    rw [e, integral_const_mul, integral_norm_betaPrimeIntegrand a b hcw, norm_mul,
      norm_cpow_eq_rpow_re_of_pos hcw, neg_re]
    ring

/-- **Iterated Beta integral, value.** Under the hypotheses of
`QED.DimReg.integrableOn_prod_betaPrime`,
`∫_{(0,∞) × S} F = (∫_S A(w) c(w) ^ (-a) dμ) · Γ(a) Γ(b) / Γ(a + b)`. -/
theorem integral_prod_betaPrime {S : Set α} (hS : MeasurableSet S) {a b : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) {F : ℝ × α → ℂ} (hFm : AEStronglyMeasurable F
      ((volume.restrict (Ioi 0)).prod (μ.restrict S)))
    {A : α → ℂ} {c : α → ℝ} (hc : ∀ w ∈ S, 0 < c w)
    (hF : ∀ t : ℝ, 0 < t → ∀ w ∈ S, F (t, w) = A w * betaPrimeIntegrand a b (c w) t)
    (hA : IntegrableOn (fun w => A w * ((c w : ℝ) : ℂ) ^ (-a)) S μ) :
    ∫ z in Ioi 0 ×ˢ S, F z ∂((volume : Measure ℝ).prod μ) =
      (∫ w in S, A w * ((c w : ℝ) : ℂ) ^ (-a) ∂μ) * (Gamma a * Gamma b / Gamma (a + b)) := by
  have hI := integrableOn_prod_betaPrime hS ha hb hFm hc hF hA
  unfold IntegrableOn at hI
  rw [← Measure.prod_restrict] at hI ⊢
  rw [integral_prod_symm _ hI, ← integral_mul_const]
  refine setIntegral_congr_fun hS fun w hw => ?_
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => by rw [hF t ht w hw]),
    integral_const_mul, integral_betaPrime ha hb (hc w hw)]
  ring

/-! ### The fiberwise substitution `x₀ = y s` on the quadrant -/

/-- The substituted integrand `(y, s) ↦ y H(y s, y)`. -/
noncomputable def quadSubst (H : ℝ × ℝ → ℂ) (z : ℝ × ℝ) : ℂ := (z.1 : ℂ) * H (z.1 * z.2, z.1)

theorem quadSubst_fiber {H : ℝ × ℝ → ℂ} {y : ℝ} (hy : 0 < y) :
    ∫ s in Ioi (0 : ℝ), quadSubst H (y, s) = ∫ x in Ioi (0 : ℝ), H (x, y) := by
  have h := integral_comp_mul_left_Ioi (fun x => H (x, y)) 0 hy
  rw [mul_zero] at h
  simp only [quadSubst]
  rw [integral_const_mul, h, Complex.real_smul, ofReal_inv, ← mul_assoc,
    mul_inv_cancel₀ (ofReal_ne_zero.mpr hy.ne'), one_mul]

theorem quadSubst_fiber_norm {H : ℝ × ℝ → ℂ} {y : ℝ} (hy : 0 < y) :
    ∫ s in Ioi (0 : ℝ), ‖quadSubst H (y, s)‖ = ∫ x in Ioi (0 : ℝ), ‖H (x, y)‖ := by
  have h := integral_comp_mul_left_Ioi (fun x => ‖H (x, y)‖) 0 hy
  rw [mul_zero] at h
  simp only [quadSubst, norm_mul, norm_real, Real.norm_of_nonneg hy.le]
  rw [integral_const_mul, h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hy.ne', one_mul]

/-- **Fiberwise substitution, integrability.** If `(y, s) ↦ y H(y s, y)` is integrable on the
quadrant, so is `H`. -/
theorem integrableOn_quad_of_subst {H : ℝ × ℝ → ℂ} (hHm : Measurable H)
    (h : IntegrableOn (quadSubst H) (Ioi 0 ×ˢ Ioi 0)) : IntegrableOn H (Ioi 0 ×ˢ Ioi 0) := by
  unfold IntegrableOn at h ⊢
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at h ⊢
  rw [integrable_prod_iff' hHm.aestronglyMeasurable]
  constructor
  · filter_upwards [h.prod_right_ae, ae_restrict_mem measurableSet_Ioi] with y hy hy0
    have hy0 : 0 < y := hy0
    have h2 := (integrableOn_Ioi_comp_mul_left_iff (fun x => H (x, y)) 0 hy0).mp
      (IntegrableOn.congr_fun (hy.const_mul (y : ℂ)⁻¹ : IntegrableOn _ _ _) (fun s _ => by
        simp only [quadSubst]
        rw [← mul_assoc, inv_mul_cancel₀ (ofReal_ne_zero.mpr hy0.ne'), one_mul])
        measurableSet_Ioi)
    rwa [mul_zero] at h2
  · refine h.integral_norm_prod_left.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact quadSubst_fiber_norm hy

/-- **Fiberwise substitution, value.** `∫_{(0,∞)²} H(x₀, x₁) = ∫_{(0,∞)²} y H(y s, y) d(y, s)`. -/
theorem integral_quad_eq_subst {H : ℝ × ℝ → ℂ} (hHm : Measurable H)
    (h : IntegrableOn (quadSubst H) (Ioi 0 ×ˢ Ioi 0)) :
    ∫ x in Ioi 0 ×ˢ Ioi 0, H x = ∫ z in Ioi 0 ×ˢ Ioi 0, quadSubst H z := by
  have hH := integrableOn_quad_of_subst hHm h
  unfold IntegrableOn at h hH
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at h hH ⊢
  rw [integral_prod_symm _ hH, integral_prod _ h]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  exact (quadSubst_fiber hy).symm

end QED.DimReg
