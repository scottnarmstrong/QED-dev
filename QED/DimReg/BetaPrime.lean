/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The Beta integral of the second kind

For `0 < re a`, `0 < re b` and `0 < c`,
`∫₀^∞ t ^ (a - 1) (1 + c t) ^ (-(a + b)) dt = c ^ (-a) Γ(a) Γ(b) / Γ(a + b)`,
together with the absolute convergence of the integral. This is the one-dimensional
Lee–Pomeransky integral of the massive tadpole.

The proof substitutes `t = u / (c (1 - u))`, which maps `(0, 1)` onto `(0, ∞)` and carries the
integrand to `c ^ (-a) u ^ (a - 1) (1 - u) ^ (b - 1)`, Mathlib's `Complex.betaIntegral`.

## Main results

* `QED.DimReg.integrableOn_betaPrime`: the integrand is integrable on `(0, ∞)`.
* `QED.DimReg.integral_betaPrime`: the closed form.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.DimReg

/-- For `y > 0`, `(y⁻¹) ^ s = y ^ (-s)` with real `y` cast to `ℂ`. -/
theorem ofReal_inv_cpow {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ((y⁻¹ : ℝ) : ℂ) ^ s = (y : ℂ) ^ (-s) := by
  rw [ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hy.le]; exact Real.pi_pos.ne),
    cpow_neg]

/-- The integrand of the Beta integral of the second kind,
`t ↦ t ^ (a - 1) (1 + c t) ^ (-(a + b))`. -/
noncomputable def betaPrimeIntegrand (a b : ℂ) (c t : ℝ) : ℂ :=
  (t : ℂ) ^ (a - 1) * ((1 + c * t : ℝ) : ℂ) ^ (-(a + b))

/-- The substitution `u ↦ u / (c (1 - u))`. -/
noncomputable def betaPrimeSubst (c u : ℝ) : ℝ := u / (c * (1 - u))

/-- The derivative of `betaPrimeSubst`. -/
noncomputable def betaPrimeSubstDeriv (c u : ℝ) : ℝ := (c * (1 - u) ^ 2)⁻¹

/-- The substitution has derivative `(c (1 - u) ^ 2)⁻¹` on `(0, 1)`. -/
theorem hasDerivWithinAt_betaPrimeSubst {c : ℝ} (hc : 0 < c) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (betaPrimeSubst c) (betaPrimeSubstDeriv c u) (Ioo 0 1) u := by
  have h1 : 1 - u ≠ 0 := by linarith [hu.2]
  have hden : c * (1 - u) ≠ 0 := mul_ne_zero hc.ne' h1
  have h := (hasDerivAt_id u).div (((hasDerivAt_id u).const_sub 1).const_mul c) hden
  refine (h.congr_deriv ?_).hasDerivWithinAt
  simp only [id, betaPrimeSubstDeriv]
  field_simp
  ring

/-- The substitution is injective on `(0, 1)`. -/
theorem injOn_betaPrimeSubst {c : ℝ} (hc : 0 < c) : InjOn (betaPrimeSubst c) (Ioo 0 1) := by
  intro u hu v hv huv
  simp only [betaPrimeSubst] at huv
  have h1 : 1 - u ≠ 0 := by linarith [hu.2]
  have h2 : 1 - v ≠ 0 := by linarith [hv.2]
  rw [div_eq_div_iff (mul_ne_zero hc.ne' h1) (mul_ne_zero hc.ne' h2)] at huv
  have : c * (u - v) = 0 := by linear_combination huv
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hc.ne'
  · linarith

/-- The substitution maps `(0, 1)` onto `(0, ∞)`. -/
theorem image_betaPrimeSubst {c : ℝ} (hc : 0 < c) : betaPrimeSubst c '' Ioo 0 1 = Ioi 0 := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : 0 < 1 - u := by linarith [hu.2]
    exact div_pos hu.1 (mul_pos hc this)
  · intro ht
    have ht : 0 < t := ht
    refine ⟨c * t / (1 + c * t), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_one (by positivity)]; linarith
    · simp only [betaPrimeSubst]
      have : 0 < 1 + c * t := by positivity
      field_simp
      ring

/-- After the substitution, the transformed integrand is the Beta integrand times `c ^ (-a)`. -/
theorem betaPrime_subst_eq {a b : ℂ} {c : ℝ} (hc : 0 < c) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    |betaPrimeSubstDeriv c u| • betaPrimeIntegrand a b c (betaPrimeSubst c u) =
      (c : ℂ) ^ (-a) * ((u : ℂ) ^ (a - 1) * (1 - (u : ℂ)) ^ (b - 1)) := by
  have hw : 0 < 1 - u := by linarith [hu.2]
  have hu0 : 0 < u := hu.1
  have hcw : 0 < c * (1 - u) := mul_pos hc hw
  have hderiv : |betaPrimeSubstDeriv c u| = c⁻¹ * ((1 - u) ^ 2)⁻¹ := by
    rw [betaPrimeSubstDeriv, abs_of_pos (by positivity), mul_inv]
  have hsub : betaPrimeSubst c u = u * (c * (1 - u))⁻¹ := div_eq_mul_inv _ _
  have hone : 1 + c * betaPrimeSubst c u = (1 - u)⁻¹ := by
    simp only [betaPrimeSubst]; field_simp; ring
  rw [hderiv, betaPrimeIntegrand, hone, hsub, ofReal_mul,
    mul_cpow_ofReal_nonneg hu0.le (inv_nonneg.mpr hcw.le), ofReal_inv_cpow hcw,
    ofReal_inv_cpow hw, ofReal_mul, mul_cpow_ofReal_nonneg hc.le hw.le]
  have hc0 : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  have hw0 : ((1 - u : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw.ne'
  have e1 : (c : ℂ) ^ (-(a - 1)) = (c : ℂ) ^ (-a) * c := by
    rw [show -(a - 1) = -a + 1 by ring, cpow_add _ _ hc0, cpow_one]
  have e2 : ((1 - u : ℝ) : ℂ) ^ (-(a - 1)) * ((1 - u : ℝ) : ℂ) ^ (-(-(a + b))) =
      ((1 - u : ℝ) : ℂ) ^ (b - 1) * ((1 - u : ℝ) : ℂ) ^ 2 := by
    rw [← cpow_add _ _ hw0, ← cpow_two, ← cpow_add _ _ hw0]
    congr 1; ring
  rw [Complex.real_smul]
  push_cast
  rw [e1]
  have e2' := e2
  push_cast at e2'
  calc _ = (c : ℂ) ^ (-a) * (u : ℂ) ^ (a - 1) * ((c : ℂ)⁻¹ * c) *
        (((1 - (u : ℂ)) ^ 2)⁻¹ * ((1 - (u : ℂ)) ^ (-(a - 1)) * (1 - (u : ℂ)) ^ (-(-(a + b))))) := by
        ring
    _ = _ := by
        rw [e2', inv_mul_cancel₀ hc0]
        have h1 : (1 - (u : ℂ)) ≠ 0 := by push_cast at hw0; exact hw0
        field_simp

/-- The Beta integral of the second kind converges absolutely for `0 < re a`, `0 < re b`. -/
theorem integrableOn_betaPrime {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (betaPrimeIntegrand a b c) (Ioi 0) := by
  rw [← image_betaPrimeSubst hc, integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioo (fun u hu => hasDerivWithinAt_betaPrimeSubst hc hu) (injOn_betaPrimeSubst hc)]
  have hB := (betaIntegral_convergent ha hb)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hB
  have h : IntegrableOn
      (fun u : ℝ => (c : ℂ) ^ (-a) * ((u : ℂ) ^ (a - 1) * (1 - (u : ℂ)) ^ (b - 1))) (Ioo 0 1) :=
    (hB.mono_set Ioo_subset_Ioc_self).const_mul _
  exact h.congr_fun (fun u hu => (betaPrime_subst_eq hc hu).symm) measurableSet_Ioo

/-- The Beta integral of the second kind:
`∫₀^∞ t ^ (a - 1) (1 + c t) ^ (-(a + b)) dt = c ^ (-a) Γ(a) Γ(b) / Γ(a + b)`. -/
theorem integral_betaPrime {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), betaPrimeIntegrand a b c t =
      (c : ℂ) ^ (-a) * (Gamma a * Gamma b / Gamma (a + b)) := by
  rw [← image_betaPrimeSubst hc, integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo (fun u hu => hasDerivWithinAt_betaPrimeSubst hc hu) (injOn_betaPrimeSubst hc),
    setIntegral_congr_fun measurableSet_Ioo (fun u hu => betaPrime_subst_eq hc hu),
    integral_const_mul, ← betaIntegral_eq_Gamma_mul_div a b ha hb, betaIntegral,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

end QED.DimReg
