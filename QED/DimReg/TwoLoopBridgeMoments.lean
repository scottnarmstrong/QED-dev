/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.TwoLoopBridgeGauss
public import QED.DimReg.OneLoopBridgeNum
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Gaussian moments up to second order, one and two loops, in integer dimension

After Schwinger parametrization a numerator of degree at most two in the loop momenta multiplies
the Gaussian `e^(-(ℓ·Aℓ) + 2 b·ℓ)` of `QED.DimReg.TwoLoopBridgeGauss`. Writing a numerator
as a product of two affine forms `(α + c·ℓ)(α' + c'·ℓ)`, its Gaussian integral is
`∫ (α + c·ℓ)(α' + c'·ℓ) e^(-(ℓ·Aℓ) + 2 b·ℓ) d^Dℓ₁ d^Dℓ₂ =
  (π² / det A)^(D/2) e^(b·A⁻¹b) · ((α + c·A⁻¹b)(α' + c'·A⁻¹b) + ½ c·A⁻¹c')`
(`integral_affine_mul_affine_two`), in every integer dimension `D ≥ 1`. The shift
`ℓ = u + A⁻¹b` turns the linear term into the constant `c·A⁻¹b` (odd moments vanish), and the
second moment `½ c·A⁻¹c'` is the Wick contraction. Both sides are polynomials in the
dimension-independent data times `(π² / det A)^(D/2)`: this is how a polynomial numerator enters
the parametric representation.

The proof is two one-loop computations (`integral_affine_mul_affine`) joined by Fubini, as in
`QED.DimReg.TwoLoopBridgeGauss.integral_gauss_two`. The one-loop second moment
`∫ (γ·v)(γ'·v) e^(-a|v|²) = γ·γ' / (2a) · (π/a)^(D/2)` (`integral_inner_mul_inner_exp`) comes
from isotropy and the radial formula of `QED.DimReg.OneLoopBridgeNum`. Everything here is real
valued.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real InnerProductSpace

namespace QED.DimReg.TwoLoopBridgeMoments

open QED.DimReg.TwoLoopBridgeGauss QED.DimReg.OneLoopBridgeNum

variable {D : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin D)

/-! ### One loop: integrability -/

theorem integrable_exp_neg_mul_sq_norm {a : ℝ} (ha : 0 < a) :
    Integrable fun v : V => Real.exp (-a * ‖v‖ ^ 2) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (b := (a : ℂ))
    (by simpa using ha) 0 (0 : V)).norm
  refine h.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, add_zero, Complex.norm_exp]
  congr 1
  simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  norm_cast

/-- `1 + t ≤ (1 + 2/l) e^(l t / 2)` for `t ≥ 0`, `l > 0`. -/
theorem one_add_le_exp {l t : ℝ} (hl : 0 < l) (ht : 0 ≤ t) :
    1 + t ≤ (1 + 2 / l) * Real.exp (l / 2 * t) := by
  have h1 : 1 ≤ Real.exp (l / 2 * t) := Real.one_le_exp (by positivity)
  have h2 : l / 2 * t ≤ Real.exp (l / 2 * t) := by
    linarith [Real.add_one_le_exp (l / 2 * t)]
  have h3 : t = 2 / l * (l / 2 * t) := by field_simp
  have h4 : 2 / l * (l / 2 * t) ≤ 2 / l * Real.exp (l / 2 * t) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  nlinarith

/-- A continuous function of at most quadratic growth times `e^(-a|v|²)` is integrable. -/
theorem integrable_mul_exp {a K : ℝ} (ha : 0 < a) {f : V → ℝ} (hf : Continuous f)
    (hK : ∀ v, |f v| ≤ K * (1 + ‖v‖ ^ 2)) :
    Integrable fun v : V => f v * Real.exp (-a * ‖v‖ ^ 2) := by
  have hG := (integrable_exp_neg_mul_sq_norm (D := D) (half_pos ha)).const_mul
    (|K| * (1 + 2 / a))
  refine hG.mono' (by fun_prop) (Filter.Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  have h1 := one_add_le_exp ha (sq_nonneg ‖v‖)
  have h2 : |f v| ≤ |K| * ((1 + 2 / a) * Real.exp (a / 2 * ‖v‖ ^ 2)) :=
    (hK v).trans (mul_le_mul (le_abs_self K) h1 (by positivity) (abs_nonneg K))
  have h3 : Real.exp (a / 2 * ‖v‖ ^ 2) * Real.exp (-a * ‖v‖ ^ 2) =
      Real.exp (-(a / 2) * ‖v‖ ^ 2) := by rw [← Real.exp_add]; ring_nf
  calc |f v| * Real.exp (-a * ‖v‖ ^ 2)
      ≤ |K| * ((1 + 2 / a) * Real.exp (a / 2 * ‖v‖ ^ 2)) * Real.exp (-a * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = |K| * (1 + 2 / a) * Real.exp (-(a / 2) * ‖v‖ ^ 2) := by rw [← h3]; ring

theorem abs_inner_le {γ v : V} : |⟪γ, v⟫_ℝ| ≤ ‖γ‖ * (1 + ‖v‖ ^ 2) := by
  have h1 := abs_real_inner_le_norm γ v
  have h2 : ‖v‖ ≤ 1 + ‖v‖ ^ 2 := by nlinarith [sq_nonneg (‖v‖ - 1)]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))

theorem abs_inner_mul_inner_le {γ γ' v : V} :
    |⟪γ, v⟫_ℝ * ⟪γ', v⟫_ℝ| ≤ ‖γ‖ * ‖γ'‖ * (1 + ‖v‖ ^ 2) := by
  rw [abs_mul]
  calc |⟪γ, v⟫_ℝ| * |⟪γ', v⟫_ℝ| ≤ (‖γ‖ * ‖v‖) * (‖γ'‖ * ‖v‖) :=
        mul_le_mul (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _) (abs_nonneg _)
          (by positivity)
    _ = ‖γ‖ * ‖γ'‖ * ‖v‖ ^ 2 := by ring
    _ ≤ ‖γ‖ * ‖γ'‖ * (1 + ‖v‖ ^ 2) := by gcongr; linarith

/-! ### One loop: centered moments -/

/-- `∫_{ℝ^D} |v|² e^(-a|v|²) dv = D / (2a) · (π/a)^(D/2)`. -/
theorem integral_sum_sq_mul_exp (hD : 0 < D) {a : ℝ} (ha : 0 < a) :
    ∫ v : Fin D → ℝ, (∑ j, v j ^ 2) * Real.exp (-a * ∑ j, v j ^ 2) =
      D / (2 * a) * (π / a) ^ ((D : ℝ) / 2) := by
  have h := integral_radial hD (fun t : ℝ => t * Real.exp (-a * t))
  simp only [smul_eq_mul] at h
  rw [h]
  have hin : ∫ t in Ioi (0 : ℝ), t ^ ((D : ℝ) / 2 - 1) * (t * Real.exp (-a * t)) =
      ∫ t in Ioi (0 : ℝ), t ^ (((D : ℝ) / 2 + 1) - 1) * Real.exp (-(a * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    rw [show ((D : ℝ) / 2 + 1) - 1 = ((D : ℝ) / 2 - 1) + 1 by ring,
      Real.rpow_add_one ht.ne', neg_mul]
    ring
  rw [hin, Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) ha]
  have hD2 : (D : ℝ) / 2 ≠ 0 := by positivity
  rw [Real.Gamma_add_one hD2, Real.rpow_add (by positivity), Real.rpow_one,
    Real.div_rpow Real.pi_pos.le ha.le, one_div, Real.inv_rpow ha.le]
  have hΓ : Real.Gamma ((D : ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have ha' : a ^ ((D : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos ha _).ne'
  field_simp

theorem integrable_sum_sq_mul_exp {a : ℝ} (ha : 0 < a) :
    Integrable fun v : Fin D → ℝ => (∑ j, v j ^ 2) * Real.exp (-a * ∑ j, v j ^ 2) := by
  have e := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin D)
  have h : Integrable fun x : V => ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2) :=
    integrable_mul_exp (f := fun x : V => ‖x‖ ^ 2) (K := 1) ha (by fun_prop) fun v => by
      rw [abs_of_nonneg (sq_nonneg _), one_mul]; linarith
  rw [← e.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, EuclideanSpace.real_norm_sq_eq]
  rfl

/-- **The one-loop second moment**: `∫_{ℝ^D} (γ·v)(γ'·v) e^(-a|v|²) dv =
γ·γ' / (2a) · (π/a)^(D/2)`. -/
theorem integral_inner_mul_inner_exp (hD : 0 < D) {a : ℝ} (ha : 0 < a) (γ γ' : V) :
    ∫ v : V, ⟪γ, v⟫_ℝ * ⟪γ', v⟫_ℝ * Real.exp (-a * ‖v‖ ^ 2) =
      ⟪γ, γ'⟫_ℝ / (2 * a) * (π / a) ^ ((D : ℝ) / 2) := by
  have e := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin D)
  set g : ℝ → ℝ := fun t => Real.exp (-a * t)
  have hint := integrable_sum_sq_mul_exp (D := D) ha
  have hpt : ∀ x : V, ⟪γ, x⟫_ℝ * ⟪γ', x⟫_ℝ * Real.exp (-a * ‖x‖ ^ 2) =
      (fun v : Fin D → ℝ => ∑ k, ∑ l, (γ k * γ' l) *
        ((v k * v l) • g (∑ j, v j ^ 2))) ((MeasurableEquiv.toLp 2 (Fin D → ℝ)).symm x) := by
    intro x
    simp only [g, smul_eq_mul, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial]
    change _ = ∑ k, ∑ l, γ k * γ' l * (x k * x l * Real.exp (-a * ∑ j, x j ^ 2))
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [hpt]
  rw [e.integral_comp' (fun v : Fin D → ℝ => ∑ k, ∑ l, (γ k * γ' l) *
    ((v k * v l) • g (∑ j, v j ^ 2)))]
  have hkl : ∀ k l : Fin D, Integrable fun v : Fin D → ℝ => (v k * v l) • g (∑ j, v j ^ 2) := by
    intro k l
    refine hint.mono' (by fun_prop) (Filter.Eventually.of_forall fun v => ?_)
    rw [smul_eq_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have hk := Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ k)
    have hl := Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ l)
    rw [abs_mul]
    nlinarith [abs_nonneg (v k), abs_nonneg (v l), sq_abs (v k), sq_abs (v l),
      sq_nonneg (|v k| - |v l|)]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (hkl k l).const_mul _]
  simp_rw [fun k => integral_finsetSum _ fun l (_ : l ∈ Finset.univ) => (hkl k l).const_mul
    (γ k * γ' l), integral_const_mul]
  have hM := integral_sum_sq_mul_exp hD ha
  have hdiag : ∀ k l : Fin D, ∫ v : Fin D → ℝ, (v k * v l) • g (∑ j, v j ^ 2) =
      if k = l then (1 / D : ℝ) * (D / (2 * a) * (π / a) ^ ((D : ℝ) / 2)) else 0 := by
    intro k l
    split_ifs with h
    · subst h
      have h1 := integral_coord_sq_smul_radial g (by simpa [g] using hint) k
      simp only [g, smul_eq_mul, ← pow_two] at h1 ⊢
      rw [h1, hM]
    · exact integral_coord_mul_coord_smul_radial g h
  simp_rw [hdiag, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hD0 : (D : ℝ) ≠ 0 := by positivity
  rw [← Finset.sum_mul, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [show ∑ k, γ' k * γ k = ∑ k, γ k * γ' k from Finset.sum_congr rfl fun k _ => mul_comm _ _]
  field_simp

theorem integral_inner_mul_exp {a : ℝ} (γ : V) :
    ∫ v : V, ⟪γ, v⟫_ℝ * Real.exp (-a * ‖v‖ ^ 2) = 0 := by
  have h := integral_neg_eq_self (fun v : V => ⟪γ, v⟫_ℝ * Real.exp (-a * ‖v‖ ^ 2)) volume
  have h2 : (fun v : V => ⟪γ, -v⟫_ℝ * Real.exp (-a * ‖-v‖ ^ 2)) =
      fun v => -(⟪γ, v⟫_ℝ * Real.exp (-a * ‖v‖ ^ 2)) := by
    funext v; rw [inner_neg_right, norm_neg, neg_mul]
  rw [h2, integral_neg] at h
  linarith

/-! ### One loop: affine numerators -/

/-- **One loop, numerators of degree two**: for `a > 0`,
`∫ ((α + γ·v)(α' + γ'·v) + κ) e^(-a|v|² + 2 β·v) dv =
  (π/a)^(D/2) e^(|β|²/a) ((α + γ·β/a)(α' + γ'·β/a) + γ·γ'/(2a) + κ)`. -/
theorem integral_affine_mul_affine (hD : 0 < D) {a : ℝ} (ha : 0 < a) (α α' κ : ℝ)
    (γ γ' β : V) :
    ∫ v : V, ((α + ⟪γ, v⟫_ℝ) * (α' + ⟪γ', v⟫_ℝ) + κ) *
        Real.exp (-a * ‖v‖ ^ 2 + 2 * ⟪β, v⟫_ℝ) =
      (π / a) ^ ((D : ℝ) / 2) * Real.exp (‖β‖ ^ 2 / a) *
        ((α + ⟪γ, β⟫_ℝ / a) * (α' + ⟪γ', β⟫_ℝ / a) + ⟪γ, γ'⟫_ℝ / (2 * a) + κ) := by
  rw [← integral_add_right_eq_self _ (a⁻¹ • β)]
  set A := α + ⟪γ, β⟫_ℝ / a
  set A' := α' + ⟪γ', β⟫_ℝ / a
  set E : V → ℝ := fun w => Real.exp (-a * ‖w‖ ^ 2)
  have hpt : ∀ w : V, ((α + ⟪γ, w + a⁻¹ • β⟫_ℝ) * (α' + ⟪γ', w + a⁻¹ • β⟫_ℝ) + κ) *
      Real.exp (-a * ‖w + a⁻¹ • β‖ ^ 2 + 2 * ⟪β, w + a⁻¹ • β⟫_ℝ) =
      Real.exp (‖β‖ ^ 2 / a) * ((A * A' + κ) * E w + A * (⟪γ', w⟫_ℝ * E w) +
        A' * (⟪γ, w⟫_ℝ * E w) + ⟪γ, w⟫_ℝ * ⟪γ', w⟫_ℝ * E w) := by
    intro w
    have hexp : Real.exp (-a * ‖w + a⁻¹ • β‖ ^ 2 + 2 * ⟪β, w + a⁻¹ • β⟫_ℝ) =
        Real.exp (‖β‖ ^ 2 / a) * E w := by
      rw [← Real.exp_add]
      congr 1
      rw [norm_add_sq_real, inner_add_right, inner_smul_right, inner_smul_right,
        real_inner_self_eq_norm_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        real_inner_comm w β]
      field_simp
      ring
    rw [hexp, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right]
    simp only [A, A']
    field_simp
    ring
  simp_rw [hpt]
  have hE : Integrable E := integrable_exp_neg_mul_sq_norm ha
  have h1 : ∀ γ₀ : V, Integrable fun w : V => ⟪γ₀, w⟫_ℝ * E w := fun γ₀ =>
    integrable_mul_exp ha (by fun_prop) fun v => abs_inner_le
  have h2 : Integrable fun w : V => ⟪γ, w⟫_ℝ * ⟪γ', w⟫_ℝ * E w :=
    integrable_mul_exp ha (by fun_prop) fun v => abs_inner_mul_inner_le
  have i0 : Integrable fun w => (A * A' + κ) * E w := hE.const_mul _
  have i1 : Integrable fun w => A * (⟪γ', w⟫_ℝ * E w) := (h1 γ').const_mul _
  have i2 : Integrable fun w => A' * (⟪γ, w⟫_ℝ * E w) := (h1 γ).const_mul _
  rw [integral_const_mul, integral_add (f := fun w => (A * A' + κ) * E w +
      A * (⟪γ', w⟫_ℝ * E w) + A' * (⟪γ, w⟫_ℝ * E w)) ((i0.add i1).add i2) h2,
    integral_add (f := fun w => (A * A' + κ) * E w + A * (⟪γ', w⟫_ℝ * E w)) (i0.add i1) i2,
    integral_add i0 i1, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_inner_mul_exp,
    integral_inner_mul_exp, integral_inner_mul_inner_exp hD ha]
  simp only [E]
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm ha, finrank_euclideanSpace_fin]
  ring

/-! ### Two loops -/

/-- The real two-loop Gaussian `e^(-(ℓ·Aℓ) + 2 b·ℓ)`. -/
noncomputable def gaussR (p q r : ℝ) (b₁ b₂ : V) (z : V × V) : ℝ :=
  Real.exp (-quad p q r z + 2 * lin b₁ b₂ z)

/-- The bilinear form `c·A⁻¹c' = (r c₁·c'₁ - q (c₁·c'₂ + c₂·c'₁) + p c₂·c'₂) / det A`. -/
noncomputable def bil (p q r : ℝ) (c₁ c₂ c₁' c₂' : V) : ℝ :=
  (r * ⟪c₁, c₁'⟫_ℝ - q * (⟪c₁, c₂'⟫_ℝ + ⟪c₂, c₁'⟫_ℝ) + p * ⟪c₂, c₂'⟫_ℝ) / (p * r - q ^ 2)

theorem invForm_eq_bil (p q r : ℝ) (b₁ b₂ : V) : invForm p q r b₁ b₂ = bil p q r b₁ b₂ b₁ b₂ := by
  simp only [invForm, bil, real_inner_self_eq_norm_sq, real_inner_comm b₁ b₂]
  ring

theorem continuous_gaussR (p q r : ℝ) (b₁ b₂ : V) : Continuous (gaussR p q r b₁ b₂) := by
  unfold gaussR quad lin
  fun_prop

theorem integrable_affine_mul_affine_gaussR {p q r : ℝ} (hp : 0 < p) (hdet : 0 < p * r - q ^ 2)
    (α α' κ : ℝ) (c₁ c₂ c₁' c₂' b₁ b₂ : V) :
    Integrable (fun z : V × V => ((α + lin c₁ c₂ z) * (α' + lin c₁' c₂' z) + κ) *
      gaussR p q r b₁ b₂ z) (volume.prod volume) := by
  have hr : 0 < r := by nlinarith [sq_nonneg q]
  set l := (p * r - q ^ 2) / (p + r) / 2
  have hl : 0 < l := by positivity
  set C := 2 * (p + r) / (p * r - q ^ 2) * (‖b₁‖ ^ 2 + ‖b₂‖ ^ 2)
  set K₁ := (|α| + ‖c₁‖ + ‖c₂‖) * (|α'| + ‖c₁'‖ + ‖c₂'‖)
  set K₀ := K₁ + |κ|
  set M := (1 + 2 / (l / 2)) ^ 2
  have hG := integrable_exp_neg_mul_sq_norm (D := D) (by positivity : 0 < l / 2)
  have hP := (hG.mul_prod hG).const_mul (K₀ * M ^ 2 * Real.exp C)
  have hc : Continuous fun z : V × V => ((α + lin c₁ c₂ z) * (α' + lin c₁' c₂' z) + κ) *
      gaussR p q r b₁ b₂ z := by
    have := continuous_gaussR p q r b₁ b₂
    unfold lin
    fun_prop
  refine hP.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  have hx := one_add_le_exp (half_pos hl) (sq_nonneg ‖z.1‖)
  have hy := one_add_le_exp (half_pos hl) (sq_nonneg ‖z.2‖)
  have hlin : ∀ (β : ℝ) (e₁ e₂ : V), |β + lin e₁ e₂ z| ≤
      (|β| + ‖e₁‖ + ‖e₂‖) * ((1 + ‖z.1‖ ^ 2) * (1 + ‖z.2‖ ^ 2)) := by
    intro β e₁ e₂
    have h1 : |⟪e₁, z.1⟫_ℝ| ≤ ‖e₁‖ * (1 + ‖z.1‖ ^ 2) := abs_inner_le
    have h2 : |⟪e₂, z.2⟫_ℝ| ≤ ‖e₂‖ * (1 + ‖z.2‖ ^ 2) := abs_inner_le
    have hx1 : 1 ≤ 1 + ‖z.1‖ ^ 2 := by nlinarith [sq_nonneg ‖z.1‖]
    have hy1 : 1 ≤ 1 + ‖z.2‖ ^ 2 := by nlinarith [sq_nonneg ‖z.2‖]
    have hX1 : 1 ≤ (1 + ‖z.1‖ ^ 2) * (1 + ‖z.2‖ ^ 2) := one_le_mul_of_one_le_of_one_le hx1 hy1
    unfold lin
    calc |β + (⟪e₁, z.1⟫_ℝ + ⟪e₂, z.2⟫_ℝ)| ≤ |β| + |⟪e₁, z.1⟫_ℝ| + |⟪e₂, z.2⟫_ℝ| := by
          have := abs_add_le β (⟪e₁, z.1⟫_ℝ + ⟪e₂, z.2⟫_ℝ)
          have := abs_add_le ⟪e₁, z.1⟫_ℝ ⟪e₂, z.2⟫_ℝ
          linarith
      _ ≤ |β| * ((1 + ‖z.1‖ ^ 2) * (1 + ‖z.2‖ ^ 2)) +
          ‖e₁‖ * (1 + ‖z.1‖ ^ 2) * (1 + ‖z.2‖ ^ 2) +
          ‖e₂‖ * (1 + ‖z.2‖ ^ 2) * (1 + ‖z.1‖ ^ 2) := by
          gcongr
          · nlinarith [abs_nonneg β]
          · have : 0 ≤ ‖e₁‖ * (1 + ‖z.1‖ ^ 2) := by positivity
            nlinarith
          · have : 0 ≤ ‖e₂‖ * (1 + ‖z.2‖ ^ 2) := by positivity
            nlinarith
      _ = _ := by ring
  have hE : -quad p q r z + 2 * lin b₁ b₂ z ≤ C + (-(l * ‖z.1‖ ^ 2) + -(l * ‖z.2‖ ^ 2)) :=
    exponent_le hp hdet b₁ b₂ z
  have hgauss : gaussR p q r b₁ b₂ z ≤
      Real.exp C * (Real.exp (-l * ‖z.1‖ ^ 2) * Real.exp (-l * ‖z.2‖ ^ 2)) := by
    rw [gaussR, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    linarith
  have hq1 := hlin α c₁ c₂
  have hq2 := hlin α' c₁' c₂'
  set X := (1 + ‖z.1‖ ^ 2) * (1 + ‖z.2‖ ^ 2)
  have hX : 0 ≤ X := by positivity
  have hXe : X ≤ M *
      (Real.exp (l / 2 / 2 * ‖z.1‖ ^ 2) * Real.exp (l / 2 / 2 * ‖z.2‖ ^ 2)) := by
    calc X ≤ ((1 + 2 / (l / 2)) * Real.exp (l / 2 / 2 * ‖z.1‖ ^ 2)) *
          ((1 + 2 / (l / 2)) * Real.exp (l / 2 / 2 * ‖z.2‖ ^ 2)) :=
          mul_le_mul hx hy (by positivity) (by positivity)
      _ = _ := by simp only [M]; ring
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (by unfold gaussR; exact Real.exp_pos _ : 0 < gaussR p q r b₁ b₂ z)]
  have hX1 : 1 ≤ X := one_le_mul_of_one_le_of_one_le (by nlinarith [sq_nonneg ‖z.1‖])
    (by nlinarith [sq_nonneg ‖z.2‖])
  have hprod : |(α + lin c₁ c₂ z) * (α' + lin c₁' c₂' z) + κ| ≤ K₀ * X ^ 2 := by
    have h0 : |(α + lin c₁ c₂ z) * (α' + lin c₁' c₂' z)| ≤ K₁ * X ^ 2 := by
      rw [abs_mul]
      calc _ ≤ ((|α| + ‖c₁‖ + ‖c₂‖) * X) * ((|α'| + ‖c₁'‖ + ‖c₂'‖) * X) :=
            mul_le_mul hq1 hq2 (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hX2 : 1 ≤ X ^ 2 := one_le_pow₀ hX1
    calc _ ≤ |(α + lin c₁ c₂ z) * (α' + lin c₁' c₂' z)| + |κ| := abs_add_le _ _
      _ ≤ K₁ * X ^ 2 + |κ| * X ^ 2 := by nlinarith [abs_nonneg κ]
      _ = K₀ * X ^ 2 := by ring
  have hX2 : X ^ 2 ≤ M ^ 2 *
      (Real.exp (l / 2 * ‖z.1‖ ^ 2) * Real.exp (l / 2 * ‖z.2‖ ^ 2)) := by
    calc X ^ 2 ≤ (M *
          (Real.exp (l / 2 / 2 * ‖z.1‖ ^ 2) * Real.exp (l / 2 / 2 * ‖z.2‖ ^ 2))) ^ 2 :=
          pow_le_pow_left₀ hX hXe 2
      _ = _ := by
          rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
          congr 3 <;> push_cast <;> ring
  have hK₀ : 0 ≤ K₀ := by positivity
  calc |(α + lin c₁ c₂ z) * (α' + lin c₁' c₂' z) + κ| * gaussR p q r b₁ b₂ z
      ≤ (K₀ * X ^ 2) * (Real.exp C *
          (Real.exp (-l * ‖z.1‖ ^ 2) * Real.exp (-l * ‖z.2‖ ^ 2))) :=
        mul_le_mul hprod hgauss (by unfold gaussR; positivity) (by positivity)
    _ ≤ (K₀ * (M ^ 2 * (Real.exp (l / 2 * ‖z.1‖ ^ 2) * Real.exp (l / 2 * ‖z.2‖ ^ 2)))) *
          (Real.exp C *
          (Real.exp (-l * ‖z.1‖ ^ 2) * Real.exp (-l * ‖z.2‖ ^ 2))) := by
        gcongr
    _ = K₀ * M ^ 2 * Real.exp C * (Real.exp (-(l / 2) * ‖z.1‖ ^ 2) *
          Real.exp (-(l / 2) * ‖z.2‖ ^ 2)) := by
        have e1 : Real.exp (l / 2 * ‖z.1‖ ^ 2) * Real.exp (-l * ‖z.1‖ ^ 2) =
            Real.exp (-(l / 2) * ‖z.1‖ ^ 2) := by rw [← Real.exp_add]; ring_nf
        have e2 : Real.exp (l / 2 * ‖z.2‖ ^ 2) * Real.exp (-l * ‖z.2‖ ^ 2) =
            Real.exp (-(l / 2) * ‖z.2‖ ^ 2) := by rw [← Real.exp_add]; ring_nf
        rw [← e1, ← e2]
        ring
    _ = _ := rfl

/-- **Two loops, numerators of degree two**: for `p > 0` and `det A = p r - q² > 0`,
`∫ ((α + c·ℓ)(α' + c'·ℓ) + κ) e^(-(ℓ·Aℓ) + 2 b·ℓ) d^Dℓ₁ d^Dℓ₂ =
  (π² / det A)^(D/2) e^(b·A⁻¹b) ((α + c·A⁻¹b)(α' + c'·A⁻¹b) + ½ c·A⁻¹c' + κ)`. -/
theorem integral_affine_mul_affine_two (hD : 0 < D) {p q r : ℝ} (hp : 0 < p)
    (hdet : 0 < p * r - q ^ 2) (α α' κ : ℝ) (c₁ c₂ c₁' c₂' b₁ b₂ : V) :
    ∫ z : V × V, ((α + lin c₁ c₂ z) * (α' + lin c₁' c₂' z) + κ) * gaussR p q r b₁ b₂ z
        ∂(volume.prod volume) =
      (π ^ 2 / (p * r - q ^ 2)) ^ ((D : ℝ) / 2) * Real.exp (invForm p q r b₁ b₂) *
        ((α + bil p q r c₁ c₂ b₁ b₂) * (α' + bil p q r c₁' c₂' b₁ b₂) +
          bil p q r c₁ c₂ c₁' c₂' / 2 + κ) := by
  rw [integral_prod_symm _ (integrable_affine_mul_affine_gaussR hp hdet α α' κ c₁ c₂ c₁' c₂'
    b₁ b₂)]
  have hpt : ∀ y x : V, ((α + lin c₁ c₂ (x, y)) * (α' + lin c₁' c₂' (x, y)) + κ) *
      gaussR p q r b₁ b₂ (x, y) =
      (((α + ⟪c₂, y⟫_ℝ) + ⟪c₁, x⟫_ℝ) * ((α' + ⟪c₂', y⟫_ℝ) + ⟪c₁', x⟫_ℝ) + κ) *
        Real.exp (-p * ‖x‖ ^ 2 + 2 * ⟪b₁ - q • y, x⟫_ℝ) *
        Real.exp (-r * ‖y‖ ^ 2 + 2 * ⟪b₂, y⟫_ℝ) := by
    intro y x
    simp only [gaussR, quad, lin]
    rw [mul_assoc _ (Real.exp _), ← Real.exp_add]
    congr 1
    · ring
    · congr 1
      rw [inner_sub_left, inner_smul_left, real_inner_comm y x]
      simp only [RCLike.conj_to_real]
      ring
  simp_rw [hpt, integral_mul_const, integral_affine_mul_affine hD hp]
  set w : V := b₂ - (q / p) • b₁
  set a' := (p * r - q ^ 2) / p
  have ha' : 0 < a' := by positivity
  have hA : ∀ (y : V) (β : ℝ) (e₁ e₂ : V), (β + ⟪e₂, y⟫_ℝ) + ⟪e₁, b₁ - q • y⟫_ℝ / p =
      (β + ⟪e₁, b₁⟫_ℝ / p) + ⟪e₂ - (q / p) • e₁, y⟫_ℝ := by
    intro y β e₁ e₂
    rw [inner_sub_right, inner_smul_right, inner_sub_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
    field_simp
    ring
  have hX : ∀ y : V, Real.exp (‖b₁ - q • y‖ ^ 2 / p) * Real.exp (-r * ‖y‖ ^ 2 + 2 * ⟪b₂, y⟫_ℝ) =
      Real.exp (‖b₁‖ ^ 2 / p) * Real.exp (-a' * ‖y‖ ^ 2 + 2 * ⟪w, y⟫_ℝ) := by
    intro y
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    simp only [w, a', inner_sub_left, inner_smul_left, RCLike.conj_to_real]
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    field_simp
    ring
  set κ' := ⟪c₁, c₁'⟫_ℝ / (2 * p) + κ
  have hpt2 : ∀ y : V, (π / p) ^ ((D : ℝ) / 2) * Real.exp (‖b₁ - q • y‖ ^ 2 / p) *
      ((α + ⟪c₂, y⟫_ℝ + ⟪c₁, b₁ - q • y⟫_ℝ / p) * (α' + ⟪c₂', y⟫_ℝ + ⟪c₁', b₁ - q • y⟫_ℝ / p) +
        ⟪c₁, c₁'⟫_ℝ / (2 * p) + κ) * Real.exp (-r * ‖y‖ ^ 2 + 2 * ⟪b₂, y⟫_ℝ) =
      ((π / p) ^ ((D : ℝ) / 2) * Real.exp (‖b₁‖ ^ 2 / p)) *
        (((α + ⟪c₁, b₁⟫_ℝ / p + ⟪c₂ - (q / p) • c₁, y⟫_ℝ) *
          (α' + ⟪c₁', b₁⟫_ℝ / p + ⟪c₂' - (q / p) • c₁', y⟫_ℝ) + κ') *
          Real.exp (-a' * ‖y‖ ^ 2 + 2 * ⟪w, y⟫_ℝ)) := by
    intro y
    rw [hA y α c₁ c₂, hA y α' c₁' c₂']
    rw [show ∀ P E₁ E₂ B : ℝ, P * E₁ * B * E₂ = P * (E₁ * E₂) * B from fun _ _ _ _ => by ring,
      hX y]
    simp only [κ']
    ring
  simp_rw [hpt2]
  rw [integral_const_mul, integral_affine_mul_affine hD ha']
  have hpi : (π / p) ^ ((D : ℝ) / 2) * (π / a') ^ ((D : ℝ) / 2) =
      (π ^ 2 / (p * r - q ^ 2)) ^ ((D : ℝ) / 2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    simp only [a']
    field_simp
  have hexp : Real.exp (‖b₁‖ ^ 2 / p) * Real.exp (‖w‖ ^ 2 / a') =
      Real.exp (invForm p q r b₁ b₂) := by
    rw [← Real.exp_add]
    congr 1
    have hn : ‖b₂ - (q / p) • b₁‖ ^ 2 =
        ‖b₂‖ ^ 2 - 2 * (q / p) * ⟪b₂, b₁⟫_ℝ + (q / p) ^ 2 * ‖b₁‖ ^ 2 := by
      rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    simp only [invForm, w, a']
    rw [hn, real_inner_comm b₁ b₂]
    field_simp
    ring
  rw [show ∀ P₁ E₁ P₂ E₂ B : ℝ, P₁ * E₁ * (P₂ * E₂ * B) = (P₁ * P₂) * (E₁ * E₂) * B from
    fun _ _ _ _ _ => by ring, hpi, hexp]
  congr 1
  simp only [bil, κ', w, a', inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, RCLike.conj_to_real]
  have hp0 : p ≠ 0 := hp.ne'
  have hd0 : p * r - q ^ 2 ≠ 0 := hdet.ne'
  field_simp
  ring

/-! ### Quadratic forms: the dimension enters -/

/-- The shift `s = A⁻¹b`, first component `(r b₁ - q b₂) / det A`. -/
noncomputable def shift₁ (p q r : ℝ) (b₁ b₂ : V) : V := (p * r - q ^ 2)⁻¹ • (r • b₁ - q • b₂)

/-- The shift `s = A⁻¹b`, second component `(p b₂ - q b₁) / det A`. -/
noncomputable def shift₂ (p q r : ℝ) (b₁ b₂ : V) : V := (p * r - q ^ 2)⁻¹ • (p • b₂ - q • b₁)

theorem bil_single_left₁ (p q r : ℝ) (k : Fin D) (b₁ b₂ : V) :
    bil p q r (EuclideanSpace.single k 1) 0 b₁ b₂ = shift₁ p q r b₁ b₂ k := by
  simp only [bil, shift₁, EuclideanSpace.inner_single_left, inner_zero_left, map_one, one_mul,
    PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  ring

theorem bil_single_left₂ (p q r : ℝ) (k : Fin D) (b₁ b₂ : V) :
    bil p q r 0 (EuclideanSpace.single k 1) b₁ b₂ = shift₂ p q r b₁ b₂ k := by
  simp only [bil, shift₂, EuclideanSpace.inner_single_left, inner_zero_left, map_one, one_mul,
    PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  ring

theorem quad_eq_sum (p' q' r' : ℝ) (z : V × V) :
    quad p' q' r' z = ∑ k : Fin D,
      (p' * (lin (EuclideanSpace.single k 1) 0 z * lin (EuclideanSpace.single k 1) 0 z) +
        2 * q' * (lin (EuclideanSpace.single k 1) 0 z * lin 0 (EuclideanSpace.single k 1) z) +
        r' * (lin 0 (EuclideanSpace.single k 1) z * lin 0 (EuclideanSpace.single k 1) z)) := by
  simp only [quad, lin, EuclideanSpace.inner_single_left, inner_zero_left, map_one, one_mul,
    add_zero, zero_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, sq]
  congr 2
  · congr 1
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **Two loops, a quadratic-form numerator**: with `s = A⁻¹b` (`shift₁`, `shift₂`),
`∫ (ℓ·A'ℓ) e^(-(ℓ·Aℓ) + 2 b·ℓ) = (π² / det A)^(D/2) e^(b·A⁻¹b)
  (s·A's + D/2 · tr(A' A⁻¹))`, `tr(A' A⁻¹) = (p' r - 2 q' q + r' p) / det A`: the second
moment contributes the polynomial `D/2` of the dimension. -/
theorem integral_quad_mul_gaussR (hD : 0 < D) {p q r : ℝ} (hp : 0 < p)
    (hdet : 0 < p * r - q ^ 2) (p' q' r' : ℝ) (b₁ b₂ : V) :
    ∫ z : V × V, quad p' q' r' z * gaussR p q r b₁ b₂ z ∂(volume.prod volume) =
      (π ^ 2 / (p * r - q ^ 2)) ^ ((D : ℝ) / 2) * Real.exp (invForm p q r b₁ b₂) *
        (quad p' q' r' (shift₁ p q r b₁ b₂, shift₂ p q r b₁ b₂) +
          D * (p' * r - 2 * q' * q + r' * p) / (2 * (p * r - q ^ 2))) := by
  set e : Fin D → V := fun k => EuclideanSpace.single k 1
  set G : V → V → V → V → V × V → ℝ := fun c₁ c₂ c₁' c₂' z =>
    ((0 + lin c₁ c₂ z) * (0 + lin c₁' c₂' z) + 0) * gaussR p q r b₁ b₂ z
  have hG : ∀ c₁ c₂ c₁' c₂', Integrable (G c₁ c₂ c₁' c₂') (volume.prod volume) :=
    fun c₁ c₂ c₁' c₂' => integrable_affine_mul_affine_gaussR hp hdet 0 0 0 c₁ c₂ c₁' c₂' b₁ b₂
  have hpt : ∀ z : V × V, quad p' q' r' z * gaussR p q r b₁ b₂ z = ∑ k : Fin D,
      (p' * G (e k) 0 (e k) 0 z + 2 * q' * G (e k) 0 0 (e k) z + r' * G 0 (e k) 0 (e k) z) := by
    intro z
    rw [quad_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [G, zero_add, add_zero]
    ring
  have hI2 : ∀ k : Fin D, Integrable (fun z => p' * G (e k) 0 (e k) 0 z +
      2 * q' * G (e k) 0 0 (e k) z) (volume.prod volume) := fun k =>
    ((hG _ _ _ _).const_mul _).add ((hG _ _ _ _).const_mul _)
  have hI3 : ∀ k : Fin D, Integrable (fun z => p' * G (e k) 0 (e k) 0 z +
      2 * q' * G (e k) 0 0 (e k) z + r' * G 0 (e k) 0 (e k) z) (volume.prod volume) := fun k =>
    (hI2 k).add ((hG _ _ _ _).const_mul _)
  simp_rw [hpt]
  rw [integral_finsetSum _ fun k _ => hI3 k]
  have hval : ∀ c₁ c₂ c₁' c₂', ∫ z, G c₁ c₂ c₁' c₂' z ∂(volume.prod volume) =
      (π ^ 2 / (p * r - q ^ 2)) ^ ((D : ℝ) / 2) * Real.exp (invForm p q r b₁ b₂) *
        (bil p q r c₁ c₂ b₁ b₂ * bil p q r c₁' c₂' b₁ b₂ + bil p q r c₁ c₂ c₁' c₂' / 2) := by
    intro c₁ c₂ c₁' c₂'
    rw [integral_affine_mul_affine_two hD hp hdet 0 0 0 c₁ c₂ c₁' c₂' b₁ b₂]
    ring
  have hk : ∀ k : Fin D, ∫ z, (p' * G (e k) 0 (e k) 0 z + 2 * q' * G (e k) 0 0 (e k) z +
      r' * G 0 (e k) 0 (e k) z) ∂(volume.prod volume) =
      (π ^ 2 / (p * r - q ^ 2)) ^ ((D : ℝ) / 2) * Real.exp (invForm p q r b₁ b₂) *
        (p' * shift₁ p q r b₁ b₂ k ^ 2 + 2 * q' * (shift₁ p q r b₁ b₂ k * shift₂ p q r b₁ b₂ k) +
          r' * shift₂ p q r b₁ b₂ k ^ 2 +
          (p' * r - 2 * q' * q + r' * p) / (2 * (p * r - q ^ 2))) := by
    intro k
    rw [integral_add (hI2 k) ((hG _ _ _ _).const_mul _), integral_add ((hG _ _ _ _).const_mul _)
      ((hG _ _ _ _).const_mul _), integral_const_mul, integral_const_mul, integral_const_mul,
      hval, hval, hval, bil_single_left₁, bil_single_left₂]
    have h11 : bil p q r (e k) 0 (e k) 0 = r / (p * r - q ^ 2) := by
      simp [e, bil]
    have h12 : bil p q r (e k) 0 0 (e k) = -q / (p * r - q ^ 2) := by
      simp [e, bil]
    have h22 : bil p q r 0 (e k) 0 (e k) = p / (p * r - q ^ 2) := by
      simp [e, bil]
    rw [h11, h12, h22]
    have hd0 : p * r - q ^ 2 ≠ 0 := hdet.ne'
    field_simp
    ring
  simp_rw [hk]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  congr 1
  simp only [quad]
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [show ∑ k, shift₂ p q r b₁ b₂ k * shift₁ p q r b₁ b₂ k =
      ∑ k, shift₁ p q r b₁ b₂ k * shift₂ p q r b₁ b₂ k from
    Finset.sum_congr rfl fun k _ => mul_comm _ _]
  ring

end QED.DimReg.TwoLoopBridgeMoments
