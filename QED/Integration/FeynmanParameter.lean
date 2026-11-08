/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Feynman parameters (obligation O-5)

Obligation O-5 of `docs/ONE-LOOP-DERIVATION.md` combines the three propagator
denominators of the one-loop vertex, each of the form `real - iε` with `ε > 0`,
into a single power by Feynman parameters. This module proves the identities on
the unit square, with no contour or limiting argument. For `x, y ∈ [0, 1]`, the
substitution `x₁ = yx`, `x₂ = y(1 - x)`, `x₃ = 1 - y` maps the square onto the
simplex `x₁ + x₂ + x₃ = 1` with Jacobian `y`. The weight `2y` below is therefore
the measure `dF₃` of the source in these coordinates.

The proofs are by the fundamental theorem of calculus. With `L(x) = xA + (1 - x)B`,
the function `x / (B L(x))` is a primitive of `L(x)⁻²`. With `L(y) = yX + (1 - y)C`,
the function `y² / (C L(y)²)` is a primitive of `2y L(y)⁻³`. Neither needs a case
split on `A = B` or `X = C`.

## Main statements

* `QED.Integration.im_convex_combo_neg` and `QED.Integration.convex_combo_ne_zero`:
  a convex combination of two points of the open lower half plane lies in the open
  lower half plane, so it is nonzero (`QED.Integration.ne_zero_of_im_neg`).
* `QED.Integration.inv_mul_eq_integral_feynman_two`:
  `1/(AB) = ∫₀¹ (xA + (1 - x)B)⁻² dx`.
* `QED.Integration.inv_sq_mul_eq_integral_feynman`:
  `1/(X²C) = ∫₀¹ 2y (yX + (1 - y)C)⁻³ dy`.
* `QED.Integration.inv_mul_mul_eq_integral_feynman_three`: for `A, B, C` in the open
  lower half plane, `1/(ABC) = ∫₀¹ ∫₀¹ 2y (y(xA + (1 - x)B) + (1 - y)C)⁻³ dy dx`.
* `QED.Integration.feynmanMeasure`: the measure `dx dy` on the unit square, with
  `QED.Integration.integrable_feynmanMeasure_three` and
  `QED.Integration.inv_mul_mul_eq_integral_feynmanMeasure`: the three-denominator
  integrand is integrable, and the same identity holds against `feynmanMeasure`.
-/

@[expose] public section

open MeasureTheory

namespace QED.Integration

/-- A complex number with negative imaginary part is nonzero. -/
theorem ne_zero_of_im_neg {z : ℂ} (hz : z.im < 0) : z ≠ 0 := fun h0 => by
  rw [h0, Complex.zero_im] at hz
  exact lt_irrefl _ hz

/-- A convex combination of two points of the open lower half plane lies in the open lower
half plane. -/
theorem im_convex_combo_neg {A B : ℂ} (hA : A.im < 0) (hB : B.im < 0) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : ((x : ℂ) * A + (1 - x) * B).im < 0 := by
  have h : ((x : ℂ) * A + (1 - x) * B).im = x * A.im + (1 - x) * B.im := by simp
  rw [h]
  rcases le_total A.im B.im with hAB | hAB
  · nlinarith [mul_nonneg hx.1 (sub_nonneg.2 hAB)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hx.2) (sub_nonneg.2 hAB)]

/-- A convex combination of two points of the open lower half plane is nonzero. -/
theorem convex_combo_ne_zero {A B : ℂ} (hA : A.im < 0) (hB : B.im < 0) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : (x : ℂ) * A + (1 - x) * B ≠ 0 :=
  ne_zero_of_im_neg (im_convex_combo_neg hA hB hx)

/-- Two denominators: `1/(AB) = ∫₀¹ (xA + (1-x)B)⁻² dx`. -/
theorem inv_mul_eq_integral_feynman_two {A B : ℂ} (hB : B ≠ 0)
    (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, (x : ℂ) * A + (1 - x) * B ≠ 0) :
    (A * B)⁻¹ = ∫ x in (0 : ℝ)..1, ((x : ℂ) * A + (1 - x) * B) ^ (-2 : ℤ) := by
  have hI : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt
      (fun x : ℝ => (x : ℂ) / (B * ((x : ℂ) * A + (1 - x) * B)))
      (((x : ℂ) * A + (1 - x) * B) ^ (-2 : ℤ)) x := by
    intro x hx
    have hL := h x (hI ▸ hx)
    have hLd : HasDerivAt (fun w : ℂ => w * A + (1 - w) * B) (A - B) x := by
      have := ((hasDerivAt_id' (x := (x : ℂ))).mul_const A).fun_add
        (((hasDerivAt_id' (x := (x : ℂ))).const_sub 1).mul_const B)
      convert this using 1; ring
    have hd := (hasDerivAt_id' (x := (x : ℂ))).fun_div (hLd.const_mul B) (mul_ne_zero hB hL)
    refine HasDerivAt.comp_ofReal (e := fun w : ℂ => w / (B * (w * A + (1 - w) * B))) ?_
    convert hd using 1
    rw [zpow_neg, zpow_ofNat]
    field_simp
    ring
  have hcont : ContinuousOn (fun x : ℝ => ((x : ℂ) * A + (1 - x) * B) ^ (-2 : ℤ))
      (Set.uIcc 0 1) :=
    ContinuousOn.zpow₀ (by fun_prop) _ fun x hx => Or.inl (h x (hI ▸ hx))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp [mul_comm]

/-- `1/(X²C) = ∫₀¹ 2y (yX + (1-y)C)⁻³ dy`. -/
theorem inv_sq_mul_eq_integral_feynman {X C : ℂ} (hC : C ≠ 0)
    (h : ∀ y ∈ Set.Icc (0 : ℝ) 1, (y : ℂ) * X + (1 - y) * C ≠ 0) :
    (X ^ 2 * C)⁻¹ = ∫ y in (0 : ℝ)..1, 2 * (y : ℂ) * ((y : ℂ) * X + (1 - y) * C) ^ (-3 : ℤ) := by
  have hI : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt
      (fun y : ℝ => (y : ℂ) ^ 2 / (C * ((y : ℂ) * X + (1 - y) * C) ^ 2))
      (2 * (y : ℂ) * ((y : ℂ) * X + (1 - y) * C) ^ (-3 : ℤ)) y := by
    intro y hy
    have hL := h y (hI ▸ hy)
    have hLd : HasDerivAt (fun w : ℂ => w * X + (1 - w) * C) (X - C) y := by
      have := ((hasDerivAt_id' (x := (y : ℂ))).mul_const X).fun_add
        (((hasDerivAt_id' (x := (y : ℂ))).const_sub 1).mul_const C)
      convert this using 1; ring
    have hd := ((hasDerivAt_id' (x := (y : ℂ))).fun_pow 2).fun_div
      ((hLd.fun_pow 2).const_mul C) (mul_ne_zero hC (pow_ne_zero 2 hL))
    refine HasDerivAt.comp_ofReal (e := fun w : ℂ => w ^ 2 / (C * (w * X + (1 - w) * C) ^ 2)) ?_
    convert hd using 1
    rw [zpow_neg, zpow_ofNat]
    field_simp
    ring
  have hcont : ContinuousOn (fun y : ℝ => 2 * (y : ℂ) * ((y : ℂ) * X + (1 - y) * C) ^ (-3 : ℤ))
      (Set.uIcc 0 1) :=
    ContinuousOn.mul (by fun_prop)
      (ContinuousOn.zpow₀ (by fun_prop) _ fun y hy => Or.inl (h y (hI ▸ hy)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp [mul_comm]

/-- Three denominators in the open lower half plane, as an iterated interval integral. -/
theorem inv_mul_mul_eq_integral_feynman_three {A B C : ℂ} (hA : A.im < 0) (hB : B.im < 0)
    (hC : C.im < 0) :
    (A * B * C)⁻¹ = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
      2 * (y : ℂ) * ((y : ℂ) * ((x : ℂ) * A + (1 - x) * B) + (1 - y) * C) ^ (-3 : ℤ) := by
  rw [mul_inv, inv_mul_eq_integral_feynman_two (ne_zero_of_im_neg hB)
    fun x hx => convex_combo_ne_zero hA hB hx, ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le zero_le_one] at hx
  have hL := im_convex_combo_neg hA hB hx
  rw [← inv_sq_mul_eq_integral_feynman (ne_zero_of_im_neg hC)
    fun y hy => convex_combo_ne_zero hL hC hy, zpow_neg, zpow_ofNat, mul_inv]

/-- The measure `dx dy` on the unit square, for Feynman parameters. -/
noncomputable def feynmanMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))

instance : IsFiniteMeasure feynmanMeasure := by
  unfold feynmanMeasure
  infer_instance

/-- `feynmanMeasure` is Lebesgue measure on `ℝ²` restricted to the half-open unit square. -/
theorem feynmanMeasure_eq :
    feynmanMeasure = volume.restrict (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1) := by
  rw [feynmanMeasure, Measure.prod_restrict, ← Measure.volume_eq_prod]

/-- The three-denominator Feynman integrand is integrable against `feynmanMeasure`. -/
theorem integrable_feynmanMeasure_three {A B C : ℂ} (hA : A.im < 0) (hB : B.im < 0)
    (hC : C.im < 0) :
    Integrable (fun z : ℝ × ℝ => 2 * (z.2 : ℂ) * ((z.2 : ℂ) * ((z.1 : ℂ) * A + (1 - z.1) * B)
      + (1 - z.2) * C) ^ (-3 : ℤ)) feynmanMeasure := by
  have hcont : ContinuousOn (fun z : ℝ × ℝ => 2 * (z.2 : ℂ) * ((z.2 : ℂ) *
      ((z.1 : ℂ) * A + (1 - z.1) * B) + (1 - z.2) * C) ^ (-3 : ℤ))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    ContinuousOn.mul (by fun_prop) (ContinuousOn.zpow₀ (by fun_prop) _ fun z hz =>
      Or.inl (convex_combo_ne_zero (im_convex_combo_neg hA hB hz.1) hC hz.2))
  rw [feynmanMeasure_eq]
  exact (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

/-- The same identity against `feynmanMeasure` (for a later Fubini swap with the loop-energy
integral). -/
theorem inv_mul_mul_eq_integral_feynmanMeasure {A B C : ℂ} (hA : A.im < 0) (hB : B.im < 0)
    (hC : C.im < 0) :
    (A * B * C)⁻¹ = ∫ z, 2 * (z.2 : ℂ) * ((z.2 : ℂ) * ((z.1 : ℂ) * A + (1 - z.1) * B)
      + (1 - z.2) * C) ^ (-3 : ℤ) ∂feynmanMeasure := by
  have hint := integrable_feynmanMeasure_three hA hB hC
  rw [feynmanMeasure] at hint ⊢
  rw [integral_prod _ hint, inv_mul_mul_eq_integral_feynman_three hA hB hC]
  simp_rw [intervalIntegral.integral_of_le zero_le_one]

end QED.Integration

end
