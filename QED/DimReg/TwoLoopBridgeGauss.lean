/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The two-loop Gaussian integral in integer dimension

After Schwinger parametrization `D^(-ν) = Γ(ν)⁻¹ ∫₀^∞ α^(ν-1) e^(-α D)`, the exponent of a
two-loop integrand is `-∑ α_j D_j = -(ℓ·Aℓ) + 2 b·ℓ - c` with `A = A(α)` a positive definite
`2 × 2` matrix acting on the loop momenta `ℓ = (ℓ₁, ℓ₂) ∈ ℝ^D × ℝ^D`. The momentum integral is
Gaussian:
`∫ e^(-(ℓ·Aℓ) + 2 b·ℓ) d^Dℓ₁ d^Dℓ₂ = (π² / det A)^(D/2) · e^(b·A⁻¹b)`
(`integral_gauss_two`), with `det A = U` the first Symanzik polynomial and `c - b·A⁻¹b = F / U`.
In the Lee–Pomeransky and projective forms of `QED.DimReg.FeynmanFamily.integral` this
identity is the convention linking parameters to momenta; here it is proved in every integer
dimension `D`, by two one-loop Gaussians (`integral_cexp_neg_mul_sq_norm_add`) after Fubini,
with integrability from a uniform quadratic lower bound on `ℓ·Aℓ` (`quad_lower_bound`).

We write `A = [[p, q], [q, r]]` with `p > 0` and `det A = p r - q² > 0`.
-/

@[expose] public section

open MeasureTheory Complex GaussianFourier
open scoped Real InnerProductSpace

namespace QED.DimReg.TwoLoopBridgeGauss

variable {D : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin D)

/-- The quadratic form `ℓ·Aℓ = p |ℓ₁|² + 2 q ℓ₁·ℓ₂ + r |ℓ₂|²`. -/
noncomputable def quad (p q r : ℝ) (z : V × V) : ℝ :=
  p * ‖z.1‖ ^ 2 + 2 * q * ⟪z.1, z.2⟫_ℝ + r * ‖z.2‖ ^ 2

/-- The linear form `b·ℓ = b₁·ℓ₁ + b₂·ℓ₂`. -/
noncomputable def lin (b₁ b₂ : V) (z : V × V) : ℝ := ⟪b₁, z.1⟫_ℝ + ⟪b₂, z.2⟫_ℝ

/-- The Gaussian integrand `e^(-(ℓ·Aℓ) + 2 b·ℓ)`. -/
noncomputable def gauss (p q r : ℝ) (b₁ b₂ : V) (z : V × V) : ℂ :=
  cexp ((-quad p q r z + 2 * lin b₁ b₂ z : ℝ) : ℂ)

/-- The exponent `b·A⁻¹b = (r |b₁|² - 2 q b₁·b₂ + p |b₂|²) / det A`. -/
noncomputable def invForm (p q r : ℝ) (b₁ b₂ : V) : ℝ :=
  (r * ‖b₁‖ ^ 2 - 2 * q * ⟪b₁, b₂⟫_ℝ + p * ‖b₂‖ ^ 2) / (p * r - q ^ 2)

/-! ### Integrability -/

/-- A uniform lower bound `ℓ·Aℓ ≥ λ (|ℓ₁|² + |ℓ₂|²)`, `λ = det A / tr A`. -/
theorem quad_lower_bound {p q r : ℝ} (hp : 0 < p) (hdet : 0 < p * r - q ^ 2) (z : V × V) :
    (p * r - q ^ 2) / (p + r) * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) ≤ quad p q r z := by
  have hr : 0 < r := by nlinarith [sq_nonneg q]
  set x := ‖z.1‖
  set y := ‖z.2‖
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hin : -(|q| * (x * y)) ≤ q * ⟪z.1, z.2⟫_ℝ := by
    have h1 := abs_real_inner_le_norm z.1 z.2
    have h2 : |q * ⟪z.1, z.2⟫_ℝ| ≤ |q| * (x * y) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg q)
    linarith [neg_abs_le (q * ⟪z.1, z.2⟫_ℝ)]
  set l := (p * r - q ^ 2) / (p + r)
  have hpr : 0 < p + r := by linarith
  have ha : 0 < p - l := by
    have : p - l = (p ^ 2 + q ^ 2) / (p + r) := by simp only [l]; field_simp; ring
    rw [this]; positivity
  have hac : q ^ 2 ≤ (p - l) * (r - l) := by
    have : (p - l) * (r - l) = q ^ 2 + l ^ 2 := by simp only [l]; field_simp; ring
    rw [this]; nlinarith [sq_nonneg l]
  have hkey : 0 ≤ (p - l) * x ^ 2 - 2 * |q| * (x * y) + (r - l) * y ^ 2 := by
    have h3 : 0 ≤ (p - l) * ((p - l) * x ^ 2 - 2 * |q| * (x * y) + (r - l) * y ^ 2) := by
      have e : (p - l) * ((p - l) * x ^ 2 - 2 * |q| * (x * y) + (r - l) * y ^ 2) =
          ((p - l) * x - |q| * y) ^ 2 + ((p - l) * (r - l) - |q| ^ 2) * y ^ 2 := by ring
      rw [e, sq_abs]
      exact add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
    exact (mul_nonneg_iff_of_pos_left ha).mp h3
  unfold quad
  nlinarith [hin, hkey]

theorem exponent_le {p q r : ℝ} (hp : 0 < p) (hdet : 0 < p * r - q ^ 2) (b₁ b₂ : V)
    (z : V × V) :
    -quad p q r z + 2 * lin b₁ b₂ z ≤
      2 * (p + r) / (p * r - q ^ 2) * (‖b₁‖ ^ 2 + ‖b₂‖ ^ 2) +
        (-((p * r - q ^ 2) / (p + r) / 2 * ‖z.1‖ ^ 2) +
          -((p * r - q ^ 2) / (p + r) / 2 * ‖z.2‖ ^ 2)) := by
  have hr : 0 < r := by nlinarith [sq_nonneg q]
  have hl : 0 < (p * r - q ^ 2) / (p + r) := by positivity
  set l := (p * r - q ^ 2) / (p + r)
  have hl' : 2 * (p + r) / (p * r - q ^ 2) = 2 / l := by simp only [l]; field_simp
  rw [hl']
  have hQ := quad_lower_bound hp hdet z
  have h1 : ⟪b₁, z.1⟫_ℝ ≤ ‖b₁‖ * ‖z.1‖ := real_inner_le_norm _ _
  have h2 : ⟪b₂, z.2⟫_ℝ ≤ ‖b₂‖ * ‖z.2‖ := real_inner_le_norm _ _
  have e1 : 2 * (‖b₁‖ * ‖z.1‖) ≤ l / 2 * ‖z.1‖ ^ 2 + 2 / l * ‖b₁‖ ^ 2 := by
    have : 0 ≤ l / 2 * (‖z.1‖ - 2 / l * ‖b₁‖) ^ 2 := by positivity
    have e : l / 2 * (‖z.1‖ - 2 / l * ‖b₁‖) ^ 2 =
        l / 2 * ‖z.1‖ ^ 2 + 2 / l * ‖b₁‖ ^ 2 - 2 * (‖b₁‖ * ‖z.1‖) := by field_simp; ring
    linarith
  have e2 : 2 * (‖b₂‖ * ‖z.2‖) ≤ l / 2 * ‖z.2‖ ^ 2 + 2 / l * ‖b₂‖ ^ 2 := by
    have : 0 ≤ l / 2 * (‖z.2‖ - 2 / l * ‖b₂‖) ^ 2 := by positivity
    have e : l / 2 * (‖z.2‖ - 2 / l * ‖b₂‖) ^ 2 =
        l / 2 * ‖z.2‖ ^ 2 + 2 / l * ‖b₂‖ ^ 2 - 2 * (‖b₂‖ * ‖z.2‖) := by field_simp; ring
    linarith
  unfold lin
  nlinarith [hQ, h1, h2, e1, e2]

theorem continuous_gauss (p q r : ℝ) (b₁ b₂ : V) : Continuous (gauss (D := D) p q r b₁ b₂) := by
  unfold gauss quad lin
  fun_prop

theorem integrable_gauss {p q r : ℝ} (hp : 0 < p) (hdet : 0 < p * r - q ^ 2) (b₁ b₂ : V) :
    Integrable (gauss p q r b₁ b₂) (volume.prod volume) := by
  have hl : 0 < (p * r - q ^ 2) / (p + r) / 2 := by
    have hr : 0 < r := by nlinarith [sq_nonneg q]
    positivity
  set l := (p * r - q ^ 2) / (p + r) / 2
  set C := 2 * (p + r) / (p * r - q ^ 2) * (‖b₁‖ ^ 2 + ‖b₂‖ ^ 2)
  have hG := integrable_cexp_neg_mul_sq_norm_add (b := (l : ℂ)) (by simpa using hl)
    (0 : ℂ) (0 : EuclideanSpace ℝ (Fin D))
  have hP := (hG.mul_prod hG).norm.const_mul (Real.exp C)
  refine hP.mono' (continuous_gauss p q r b₁ b₂).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [gauss, norm_exp_ofReal, norm_mul, norm_exp, norm_exp]
  simp only [inner_zero_left, ofReal_zero, mul_zero, add_zero, neg_mul, neg_re, mul_re,
    ofReal_re, ofReal_im, zero_mul, sub_zero]
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have := exponent_le hp hdet b₁ b₂ z
  norm_cast at this ⊢

/-! ### The Gaussian integral -/

theorem integral_gauss_inner {p q r : ℝ} (hp : 0 < p) (b₁ b₂ y : V) :
    ∫ v : V, gauss p q r b₁ b₂ (v, y) =
      ((π : ℂ) / p) ^ ((D : ℂ) / 2) *
        cexp ((‖b₁ - q • y‖ ^ 2 / p - r * ‖y‖ ^ 2 + 2 * ⟪b₂, y⟫_ℝ : ℝ) : ℂ) := by
  have hpt : ∀ v : V, gauss p q r b₁ b₂ (v, y) =
      cexp (-(p : ℂ) * ‖v‖ ^ 2 + (2 : ℂ) * ⟪b₁ - q • y, v⟫_ℝ) *
        cexp ((-(r * ‖y‖ ^ 2) + 2 * ⟪b₂, y⟫_ℝ : ℝ) : ℂ) := by
    intro v
    rw [gauss, ← Complex.exp_add]
    congr 1
    simp only [quad, lin, inner_sub_left, inner_smul_left, real_inner_comm y v]
    push_cast
    simp only [RCLike.conj_to_real]
    ring
  simp_rw [hpt]
  rw [integral_mul_const, integral_cexp_neg_mul_sq_norm_add (by simpa using hp),
    finrank_euclideanSpace_fin, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  field_simp
  ring

/-- **The two-loop Gaussian integral in dimension `D`**: for `p > 0`, `p r - q² > 0`,
`∫ e^(-(p|ℓ₁|² + 2q ℓ₁·ℓ₂ + r|ℓ₂|²) + 2(b₁·ℓ₁ + b₂·ℓ₂)) = (π² / det A)^(D/2) e^(b·A⁻¹b)`. -/
theorem integral_gauss_two {p q r : ℝ} (hp : 0 < p) (hdet : 0 < p * r - q ^ 2) (b₁ b₂ : V) :
    ∫ z : V × V, gauss p q r b₁ b₂ z ∂(volume.prod volume) =
      ((π ^ 2 / (p * r - q ^ 2) : ℝ) : ℂ) ^ ((D : ℂ) / 2) * cexp (invForm p q r b₁ b₂ : ℂ) := by
  rw [integral_prod_symm _ (integrable_gauss hp hdet b₁ b₂)]
  simp_rw [integral_gauss_inner hp]
  set w : V := b₂ - (q / p) • b₁
  have hb : 0 < (p * r - q ^ 2) / p := by positivity
  have hpt : ∀ y : V, ((π : ℂ) / p) ^ ((D : ℂ) / 2) *
      cexp ((‖b₁ - q • y‖ ^ 2 / p - r * ‖y‖ ^ 2 + 2 * ⟪b₂, y⟫_ℝ : ℝ) : ℂ) =
      (((π : ℂ) / p) ^ ((D : ℂ) / 2) * cexp ((‖b₁‖ ^ 2 / p : ℝ) : ℂ)) *
        cexp (-(((p * r - q ^ 2) / p : ℝ) : ℂ) * ‖y‖ ^ 2 + (2 : ℂ) * ⟪w, y⟫_ℝ) := by
    intro y
    have hp0 : (p : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [w, inner_sub_left, inner_smul_left, RCLike.conj_to_real]
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    push_cast
    field_simp
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_cexp_neg_mul_sq_norm_add (by rw [ofReal_re]; exact hb),
    finrank_euclideanSpace_fin]
  have hπp : (π : ℂ) / p = ((π / p : ℝ) : ℂ) := by push_cast; rfl
  have hπb : (π : ℂ) / (((p * r - q ^ 2) / p : ℝ) : ℂ) =
      ((π / ((p * r - q ^ 2) / p) : ℝ) : ℂ) := by push_cast; rfl
  rw [hπp, hπb, show ∀ A B C E : ℂ, A * B * (C * E) = (A * C) * (B * E) from fun _ _ _ _ => by
    ring, ← mul_cpow_ofReal_nonneg (by positivity) (by positivity), ← Complex.exp_add]
  have hp0 : (p : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
  have hd0 : (p : ℂ) * r - q ^ 2 ≠ 0 := by exact_mod_cast hdet.ne'
  congr 2
  · rw [← ofReal_mul]
    congr 1
    field_simp
  · have hn : ‖b₂ - (q / p) • b₁‖ ^ 2 =
        ‖b₂‖ ^ 2 - 2 * (q / p) * ⟪b₂, b₁⟫_ℝ + (q / p) ^ 2 * ‖b₁‖ ^ 2 := by
      rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    simp only [invForm, w]
    rw [← ofReal_pow, hn, real_inner_comm b₁ b₂]
    push_cast
    field_simp
    ring

end QED.DimReg.TwoLoopBridgeGauss
