/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.BetaPrimeNested

/-!
# Feynman's formula for joining two denominators

For `0 < A`, `0 < B` and `0 < re a`, `0 < re b`,

  `A ^ (-a) B ^ (-b) Γ(a) Γ(b) / Γ(a + b)
    = ∫₀¹ y ^ (a - 1) (1 - y) ^ (b - 1) (y A + (1 - y) B) ^ (-(a + b)) dy`,

the formula that joins two propagator powers `(k² + M₁²) ^ (-a)`, `(k² + M₂²) ^ (-b)` into one
power of `k² + y M₁² + (1 - y) M₂²`. It is first proved in the form of a Beta integral of the
second kind, `∫₀^∞ t ^ (a - 1) (B + t A) ^ (-(a + b)) dt` (`QED.DimReg.integral_betaPrime`
after factoring out `B`), and then carried to `(0, 1)` by `t = y / (1 - y)`.

## Main results

* `QED.DimReg.integrableOn_feynmanJoinPrime`, `QED.DimReg.integral_feynmanJoinPrime`: the
  Beta-prime form.
* `QED.DimReg.integrableOn_feynmanJoin`, `QED.DimReg.integral_feynmanJoin`: the form on `(0, 1)`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.DimReg

/-- The Beta-prime form of the Feynman join, `t ↦ t ^ (a - 1) (B + t A) ^ (-(a + b))`. -/
noncomputable def feynmanJoinPrime (a b : ℂ) (A B t : ℝ) : ℂ :=
  (t : ℂ) ^ (a - 1) * ((B + t * A : ℝ) : ℂ) ^ (-(a + b))

/-- The Feynman-parameter integrand,
`y ↦ y ^ (a - 1) (1 - y) ^ (b - 1) (y A + (1 - y) B) ^ (-(a + b))`. -/
noncomputable def feynmanJoin (a b : ℂ) (A B y : ℝ) : ℂ :=
  (y : ℂ) ^ (a - 1) * ((1 - y : ℝ) : ℂ) ^ (b - 1) * ((y * A + (1 - y) * B : ℝ) : ℂ) ^ (-(a + b))

theorem feynmanJoinPrime_eq {a b : ℂ} {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {t : ℝ} (ht : 0 < t) :
    feynmanJoinPrime a b A B t =
      (B : ℂ) ^ (-(a + b)) * betaPrimeIntegrand a b (A * B⁻¹) t := by
  have h : B + t * A = B * (1 + A * B⁻¹ * t) := by field_simp
  have h1 : 0 ≤ 1 + A * B⁻¹ * t := by positivity
  rw [feynmanJoinPrime, betaPrimeIntegrand, h, cpow_ofReal_mul hB.le h1]
  ring

theorem integrableOn_feynmanJoinPrime {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) : IntegrableOn (feynmanJoinPrime a b A B) (Ioi 0) := by
  have hc : 0 < A * B⁻¹ := by positivity
  have h : IntegrableOn (fun t => (B : ℂ) ^ (-(a + b)) * betaPrimeIntegrand a b (A * B⁻¹) t)
      (Ioi 0) := (integrableOn_betaPrime ha hb hc).const_mul _
  exact h.congr_fun (fun t ht => (feynmanJoinPrime_eq hA hB ht).symm) measurableSet_Ioi

/-- **The Feynman join, Beta-prime form.**
`∫₀^∞ t ^ (a - 1) (B + t A) ^ (-(a + b)) dt = A ^ (-a) B ^ (-b) Γ(a) Γ(b) / Γ(a + b)`. -/
theorem integral_feynmanJoinPrime {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) :
    ∫ t in Ioi (0 : ℝ), feynmanJoinPrime a b A B t =
      (A : ℂ) ^ (-a) * (B : ℂ) ^ (-b) * (Gamma a * Gamma b / Gamma (a + b)) := by
  have hc : 0 < A * B⁻¹ := by positivity
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => feynmanJoinPrime_eq hA hB ht),
    integral_const_mul, integral_betaPrime ha hb hc, ofReal_mul_inv_cpow hA.le hB]
  have hB0 : (B : ℂ) ≠ 0 := ofReal_ne_zero.mpr hB.ne'
  have e : (B : ℂ) ^ (-(a + b)) * (B : ℂ) ^ (-(-a)) = (B : ℂ) ^ (-b) := by
    rw [← cpow_add _ _ hB0]; congr 1; ring
  rw [← e]
  ring

/-- Pulled back along `t = y / (1 - y)`, the Beta-prime form is the Feynman integrand. -/
theorem feynmanJoin_subst_eq {a b : ℂ} {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    |betaPrimeSubstDeriv 1 y| • feynmanJoinPrime a b A B (betaPrimeSubst 1 y) =
      feynmanJoin a b A B y := by
  have hw : 0 < 1 - y := by linarith [hy.2]
  have hy0 : 0 < y := hy.1
  have hL : 0 < y * A + (1 - y) * B := by nlinarith
  have hderiv : |betaPrimeSubstDeriv 1 y| = ((1 - y) ^ 2)⁻¹ := by
    rw [betaPrimeSubstDeriv, abs_of_pos (by positivity), one_mul]
  have hsub : betaPrimeSubst 1 y = y * (1 - y)⁻¹ := by rw [betaPrimeSubst, one_mul, div_eq_mul_inv]
  have hden : B + y * (1 - y)⁻¹ * A = (y * A + (1 - y) * B) * (1 - y)⁻¹ := by field_simp; ring
  rw [hderiv, feynmanJoinPrime, hsub, ofReal_mul_inv_cpow hy0.le hw, hden,
    ofReal_mul_inv_cpow hL.le hw, Complex.real_smul, feynmanJoin]
  have hw0 : ((1 - y : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw.ne'
  have e : ((((1 - y) ^ 2)⁻¹ : ℝ) : ℂ) * ((1 - y : ℝ) : ℂ) ^ (-(a - 1)) *
      ((1 - y : ℝ) : ℂ) ^ (-(-(a + b))) = ((1 - y : ℝ) : ℂ) ^ (b - 1) := by
    have h2 : ((((1 - y) ^ 2)⁻¹ : ℝ) : ℂ) = ((1 - y : ℝ) : ℂ) ^ (-2 : ℂ) := by
      rw [cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]; push_cast; rfl
    rw [h2, ← cpow_add _ _ hw0, ← cpow_add _ _ hw0]
    congr 1; ring
  rw [← e]
  ring

theorem integrableOn_feynmanJoin {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) : IntegrableOn (feynmanJoin a b A B) (Ioo 0 1) := by
  have h := integrableOn_feynmanJoinPrime ha hb hA hB
  rw [← image_betaPrimeSubst one_pos, integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioo (fun u hu => hasDerivWithinAt_betaPrimeSubst one_pos hu)
    (injOn_betaPrimeSubst one_pos)] at h
  exact h.congr_fun (fun y hy => feynmanJoin_subst_eq hA hB hy) measurableSet_Ioo

/-- **The Feynman join.** For `0 < A`, `0 < B`, `0 < re a`, `0 < re b`,
`∫₀¹ y ^ (a - 1) (1 - y) ^ (b - 1) (y A + (1 - y) B) ^ (-(a + b)) dy
  = A ^ (-a) B ^ (-b) Γ(a) Γ(b) / Γ(a + b)`. -/
theorem integral_feynmanJoin {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) :
    ∫ y in Ioo (0 : ℝ) 1, feynmanJoin a b A B y =
      (A : ℂ) ^ (-a) * (B : ℂ) ^ (-b) * (Gamma a * Gamma b / Gamma (a + b)) := by
  rw [← integral_feynmanJoinPrime ha hb hA hB, ← image_betaPrimeSubst one_pos,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun u hu => hasDerivWithinAt_betaPrimeSubst one_pos hu) (injOn_betaPrimeSubst one_pos)]
  exact (setIntegral_congr_fun measurableSet_Ioo (fun y hy => feynmanJoin_subst_eq hA hB hy)).symm

end QED.DimReg
