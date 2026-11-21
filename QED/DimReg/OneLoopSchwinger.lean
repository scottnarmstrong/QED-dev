/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.OrthantFTC
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import QED.Algebra.IBPCertPilotData
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The one-loop on-shell self-energy: momentum IBPs as Schwinger-parameter identities (B1, B2)

The bridge from the momentum-space IBP relations of the certificate checker (layer L2,
`QED.Algebra.IBPCert.Family.template`) to actual parametric integrals, carried out for the
checker's pilot family `QED.Algebra.IBPCert.Pilot.oneLoopSE` (`D₀ = k²`, `D₁ = (k + p)² - 1`,
`p² = 1`, Minkowski signature).

**The integral.** After Wick rotation, `k² ↦ -k_E²` and `p² = 1 ↦ p_E² = -1`, so
`D_a = -D_a^E` with `D₀^E = k_E²`, `D₁^E = (k_E + p_E)² + 1`, and
`∏ D_a^{-ν_a} = (-1)^{|ν|} ∏ (D_a^E)^{-ν_a}`. Schwinger parameters
`(D^E)^{-ν} = Γ(ν)⁻¹ ∫₀^∞ x^{ν-1} e^{-x D^E}` and the Gaussian `k_E`-integral (measure
`dᵈk_E / π^{d/2}`) give the Euclidean integral

  `I_S(a, b; d) = (Γ(a) Γ(b))⁻¹ ∫_{(0,∞)²} x₀^{a-1} x₁^{b-1} S(x) dx`,
  `S(x) = U^{-d/2} e^{-F/U}`, `U = x₀ + x₁`, `F = x₁²`

(`QED.DimReg.OneLoopSchwinger.schw`). Here `I_S` is the definition; the Wick rotation and the
Gaussian integral are the documented convention linking it to momentum space (as in
`QED.DimReg.LR96Family`). The Minkowski family value is `(-1)^{|ν|} I_S(ν)`.

**B1.** At fixed `x`, the `k`-integral of `∂/∂k · (q_j e^{-Σ x_a D_a})` vanishes; with
`D_b e^{-x·D} = -∂_{x_b} e^{-x·D}` this is a first-order identity for `S`:
`2d S + (4x₀ + 2x₁) ∂₀S + 2x₁ ∂₁S = 0` (`q_j = k`) and `2U (∂₁S - ∂₀S) + 4x₁ S = 0`
(`q_j = p`). Divided by `S` and multiplied by `U²` they are polynomial identities in `(x, d)`,
proved by `ring` (`b1Poly₀₀`, `b1Poly₀₁`, then `b1₀₀`, `b1₀₁`).

**B2.** Multiply by `x^{ν-1}` and integrate over the quadrant. Integration by parts in `x_b`
(`integral_quad_eq_zero₀/₁`, from `QED.DimReg.integral_Ioi_eq_zero_of_hasDerivAt`, no
boundary hypotheses) turns `∫ x^{μ-1} ∂_b S` into `-(μ_b - 1) ∫ x^{μ-e_b-1} S`
(`integral_monoD₀/₁`), and the Γ-normalization turns the result into exactly the checker's
relation `template 0 j` (`schw_template`), at every complex `ν` with `re νᵢ > 1` where the
integrals involved converge.

## Main results

* `QED.DimReg.OneLoopSchwinger.b1₀₀`, `b1₀₁`: B1.
* `QED.DimReg.OneLoopSchwinger.mellin₂_rel₀₀`, `mellin₂_rel₀₁`: B1 + B2, unnormalized.
* `QED.DimReg.OneLoopSchwinger.schw_rel₀₀`, `schw_rel₀₁`: B1 + B2, Γ-normalized.
* `QED.DimReg.OneLoopSchwinger.schw_template`: the checker's relations for `(-1)^{|ν|} I_S`.
-/

@[expose] public section

open MeasureTheory Set Complex Filter

namespace QED.DimReg.OneLoopSchwinger

/-- The open quadrant `(0, ∞)²`. -/
def quad : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioi 0

theorem measurableSet_quad : MeasurableSet quad := measurableSet_Ioi.prod measurableSet_Ioi

/-- The Schwinger kernel `U ^ (-d / 2) e ^ (-F / U)` of the Euclidean one-loop on-shell
self-energy, `U = x₀ + x₁`, `F = x₁²`. -/
noncomputable def kernel (d : ℂ) (x : ℝ × ℝ) : ℂ :=
  ((x.1 + x.2 : ℝ) : ℂ) ^ (-(d / 2)) * cexp (-((x.2 ^ 2 / (x.1 + x.2) : ℝ) : ℂ))

/-- The partial derivative of `kernel` in `x₀`. -/
noncomputable def kernelD₀ (d : ℂ) (x : ℝ × ℝ) : ℂ :=
  kernel d x * (-(d / 2) / ((x.1 : ℂ) + x.2) + (x.2 : ℂ) ^ 2 / ((x.1 : ℂ) + x.2) ^ 2)

/-- The partial derivative of `kernel` in `x₁`. -/
noncomputable def kernelD₁ (d : ℂ) (x : ℝ × ℝ) : ℂ :=
  kernel d x * (-(d / 2) / ((x.1 : ℂ) + x.2) + (x.2 : ℂ) ^ 2 / ((x.1 : ℂ) + x.2) ^ 2 -
    2 * x.2 / ((x.1 : ℂ) + x.2))

theorem hasDerivAt_kernel_aux (d : ℂ) {u : ℝ → ℝ} {f : ℝ → ℝ} {u' f' t : ℝ}
    (hu : HasDerivAt u u' t) (hf : HasDerivAt f f' t) (hpos : 0 < u t) :
    HasDerivAt (fun s => ((u s : ℝ) : ℂ) ^ (-(d / 2)) * cexp (-((f s / u s : ℝ) : ℂ)))
      (((u t : ℝ) : ℂ) ^ (-(d / 2)) * cexp (-((f t / u t : ℝ) : ℂ)) *
        (-(d / 2) * u' / u t - (f' * u t - f t * u') / (u t) ^ 2)) t := by
  have hu0 : (u t : ℂ) ≠ 0 := ofReal_ne_zero.mpr hpos.ne'
  have hs : ((u t : ℝ) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hpos
  have hA := (Complex.hasStrictDerivAt_cpow_const (c := -(d / 2)) hs).hasDerivAt.comp t
    hu.ofReal_comp
  have hq := (hf.div hu hpos.ne').ofReal_comp.neg.cexp
  have hpow : ((u t : ℝ) : ℂ) ^ (-(d / 2) - 1) = ((u t : ℝ) : ℂ) ^ (-(d / 2)) / u t := by
    rw [cpow_sub _ _ hu0, cpow_one]
  refine (hA.mul hq).congr_deriv ?_
  simp only [Function.comp, hpow, Pi.div_apply, Pi.neg_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_kernel₀ (d : ℂ) {x : ℝ × ℝ} (hx : 0 < x.1) (hy : 0 < x.2) :
    HasDerivAt (fun t => kernel d (t, x.2)) (kernelD₀ d x) x.1 := by
  have h := hasDerivAt_kernel_aux d (u := fun t => t + x.2) (f := fun _ => x.2 ^ 2)
    ((hasDerivAt_id x.1).add_const x.2) (hasDerivAt_const _ _) (by show 0 < _ + _; linarith)
  refine h.congr_deriv ?_
  have hu0 : (x.1 : ℂ) + x.2 ≠ 0 := by
    rw [← ofReal_add]; exact ofReal_ne_zero.mpr (by linarith)
  simp only [kernelD₀, kernel]
  push_cast
  field_simp
  ring

theorem hasDerivAt_kernel₁ (d : ℂ) {x : ℝ × ℝ} (hx : 0 < x.1) (hy : 0 < x.2) :
    HasDerivAt (fun t => kernel d (x.1, t)) (kernelD₁ d x) x.2 := by
  have h := hasDerivAt_kernel_aux d (u := fun t => x.1 + t) (f := fun t => t ^ 2)
    ((hasDerivAt_id x.2).const_add x.1) (hasDerivAt_pow 2 x.2) (by show 0 < _ + _; linarith)
  refine h.congr_deriv ?_
  have hu0 : (x.1 : ℂ) + x.2 ≠ 0 := by
    rw [← ofReal_add]; exact ofReal_ne_zero.mpr (by linarith)
  simp only [kernelD₁, kernel]
  push_cast
  field_simp
  ring


/-! ### B1: the momentum-space IBPs as first-order identities for the kernel -/

/-- B1 for `∂/∂k · k`, cleared of `S` and of the denominator `U²`: a polynomial identity. -/
theorem b1Poly₀₀ (d x₀ x₁ : ℂ) :
    2 * d * (x₀ + x₁) ^ 2 + (4 * x₀ + 2 * x₁) * (-(d / 2) * (x₀ + x₁) + x₁ ^ 2) +
      2 * x₁ * (-(d / 2) * (x₀ + x₁) + x₁ ^ 2 - 2 * x₁ * (x₀ + x₁)) = 0 := by ring

/-- B1 for `∂/∂k · p`, cleared of `S` and of `U`: a polynomial identity. -/
theorem b1Poly₀₁ (x₀ x₁ : ℂ) : 2 * (x₀ + x₁) * (-2 * x₁) + 4 * x₁ * (x₀ + x₁) = 0 := by ring

theorem ofReal_add_ne_zero {x : ℝ × ℝ} (hx : x ∈ quad) : (x.1 : ℂ) + x.2 ≠ 0 := by
  rw [← ofReal_add]; exact ofReal_ne_zero.mpr (by linarith [hx.1.out, hx.2.out])

/-- B1, `∂/∂k · k`: `2d S + (4x₀ + 2x₁) ∂₀S + 2x₁ ∂₁S = 0`. -/
theorem b1₀₀ (d : ℂ) {x : ℝ × ℝ} (hx : x ∈ quad) :
    2 * d * kernel d x + (4 * x.1 + 2 * x.2) * kernelD₀ d x + 2 * x.2 * kernelD₁ d x = 0 := by
  have hu := ofReal_add_ne_zero hx
  have h := b1Poly₀₀ d x.1 x.2
  simp only [kernelD₀, kernelD₁]
  field_simp
  linear_combination kernel d x * h

/-- B1, `∂/∂k · p`: `2U (∂₁S - ∂₀S) + 4x₁ S = 0`. -/
theorem b1₀₁ (d : ℂ) {x : ℝ × ℝ} (hx : x ∈ quad) :
    2 * ((x.1 : ℂ) + x.2) * (kernelD₁ d x - kernelD₀ d x) + 4 * x.2 * kernel d x = 0 := by
  have hu := ofReal_add_ne_zero hx
  simp only [kernelD₀, kernelD₁]
  field_simp
  ring

/-! ### The orthant integration by parts on the quadrant -/

/-- `∫_{(0,∞)²} ∂₀ g = 0` when `∂₀ g` and `g / x₀` are integrable. -/
theorem integral_quad_eq_zero₀ {g g' : ℝ × ℝ → ℂ}
    (hd : ∀ x ∈ quad, HasDerivAt (fun t => g (t, x.2)) (g' x) x.1)
    (hg' : IntegrableOn g' quad) (hg : IntegrableOn (fun x => (x.1)⁻¹ • g x) quad) :
    ∫ x in quad, g' x = 0 := by
  unfold IntegrableOn at hg' hg
  rw [quad, Measure.volume_eq_prod, ← Measure.prod_restrict] at hg' hg ⊢
  rw [integral_prod_symm _ hg']
  refine (integral_congr_ae ?_).trans (integral_zero _ _)
  filter_upwards [hg'.prod_left_ae, hg.prod_left_ae, ae_restrict_mem measurableSet_Ioi]
    with y h1 h2 hy
  exact integral_Ioi_eq_zero_of_hasDerivAt (g := fun t => g (t, y))
    (fun t ht => hd (t, y) ⟨ht, hy⟩) h1 h2

/-- `∫_{(0,∞)²} ∂₁ g = 0` when `∂₁ g` and `g / x₁` are integrable. -/
theorem integral_quad_eq_zero₁ {g g' : ℝ × ℝ → ℂ}
    (hd : ∀ x ∈ quad, HasDerivAt (fun t => g (x.1, t)) (g' x) x.2)
    (hg' : IntegrableOn g' quad) (hg : IntegrableOn (fun x => (x.2)⁻¹ • g x) quad) :
    ∫ x in quad, g' x = 0 := by
  unfold IntegrableOn at hg' hg
  rw [quad, Measure.volume_eq_prod, ← Measure.prod_restrict] at hg' hg ⊢
  rw [integral_prod _ hg']
  refine (integral_congr_ae ?_).trans (integral_zero _ _)
  filter_upwards [hg'.prod_right_ae, hg.prod_right_ae, ae_restrict_mem measurableSet_Ioi]
    with y h1 h2 hy
  exact integral_Ioi_eq_zero_of_hasDerivAt (g := fun t => g (y, t))
    (fun t ht => hd (y, t) ⟨hy, ht⟩) h1 h2

/-! ### B2: integration against `x ^ (ν - 1)` -/

/-- The Schwinger integrand `x₀ ^ (a - 1) x₁ ^ (b - 1) S(x)`. -/
noncomputable def integrand (a b d : ℂ) (x : ℝ × ℝ) : ℂ :=
  (x.1 : ℂ) ^ (a - 1) * (x.2 : ℂ) ^ (b - 1) * kernel d x

/-- The Schwinger integral `∫_{(0,∞)²} x₀ ^ (a - 1) x₁ ^ (b - 1) S(x) dx`, before the
normalization by `Γ(a) Γ(b)`. -/
noncomputable def mellin₂ (a b d : ℂ) : ℂ := ∫ x in quad, integrand a b d x

/-- Absolute convergence of `mellin₂ a b d`. -/
def Conv (a b d : ℂ) : Prop := IntegrableOn (integrand a b d) quad

/-- `x₀ ^ (a - 1) x₁ ^ (b - 1) ∂₀S`. -/
noncomputable def monoD₀ (a b d : ℂ) (x : ℝ × ℝ) : ℂ :=
  (x.1 : ℂ) ^ (a - 1) * (x.2 : ℂ) ^ (b - 1) * kernelD₀ d x

/-- `x₀ ^ (a - 1) x₁ ^ (b - 1) ∂₁S`. -/
noncomputable def monoD₁ (a b d : ℂ) (x : ℝ × ℝ) : ℂ :=
  (x.1 : ℂ) ^ (a - 1) * (x.2 : ℂ) ^ (b - 1) * kernelD₁ d x

theorem cpow_eq_mul_self {t : ℝ} (ht : 0 < t) (c : ℂ) :
    (t : ℂ) ^ c = (t : ℂ) ^ (c - 1) * t := by
  have h := cpow_add (x := (t : ℂ)) (c - 1) 1 (ofReal_ne_zero.mpr ht.ne')
  rwa [cpow_one, sub_add_cancel] at h

/-- A bounded real factor keeps integrability on the quadrant. -/
theorem IntegrableOn.ofReal_mul_quad {f : ℝ × ℝ → ℝ} (hf : Measurable f) {c : ℝ}
    (hb : ∀ x ∈ quad, |f x| ≤ c) {g : ℝ × ℝ → ℂ} (hg : IntegrableOn g quad) :
    IntegrableOn (fun x => (f x : ℂ) * g x) quad :=
  Integrable.bdd_mul hg (measurable_ofReal.comp hf).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_quad).mpr (Eventually.of_forall fun x hx => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hb x hx))

theorem abs_div_add_le_one {x : ℝ × ℝ} (hx : x ∈ quad) :
    |x.1 / (x.1 + x.2)| ≤ 1 ∧ |x.2 / (x.1 + x.2)| ≤ 1 := by
  have h1 := hx.1.out
  have h2 := hx.2.out
  rw [abs_of_pos (by positivity), abs_of_pos (by positivity), div_le_one (by positivity),
    div_le_one (by positivity)]
  constructor <;> linarith

theorem integrableOn_monoD₀ {a b d : ℂ} (h : Conv a b d) (h' : Conv (a - 1) b d) :
    IntegrableOn (monoD₀ a b d) quad := by
  have hA := IntegrableOn.ofReal_mul_quad (f := fun x => (x.2 / (x.1 + x.2)) ^ 2)
    (by fun_prop) (c := 1) (fun x hx => by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (abs_div_add_le_one hx).2) h
  have hB := (IntegrableOn.ofReal_mul_quad (f := fun x => x.1 / (x.1 + x.2))
    (by fun_prop) (c := 1) (fun x hx => (abs_div_add_le_one hx).1) h').const_mul (-(d / 2))
  refine (hA.add hB).congr_fun (fun x hx => ?_) measurableSet_quad
  have hu := ofReal_add_ne_zero hx
  simp only [monoD₀, kernelD₀, integrand, Pi.add_apply]
  rw [cpow_eq_mul_self hx.1.out (a - 1)]
  push_cast
  field_simp
  ring

theorem integrableOn_monoD₁ {a b d : ℂ} (h : Conv a b d) (h' : Conv a (b - 1) d) :
    IntegrableOn (monoD₁ a b d) quad := by
  have hA := IntegrableOn.ofReal_mul_quad
    (f := fun x => (x.2 / (x.1 + x.2)) ^ 2 - 2 * (x.2 / (x.1 + x.2)))
    (by fun_prop) (c := 3) (fun x hx => by
      have h2 := (abs_div_add_le_one hx).2
      calc _ ≤ |(x.2 / (x.1 + x.2)) ^ 2| + |2 * (x.2 / (x.1 + x.2))| := abs_sub _ _
        _ ≤ 1 + 2 * 1 := by
          rw [abs_pow, abs_mul, abs_two]
          gcongr
          exact pow_le_one₀ (abs_nonneg _) h2
        _ = 3 := by norm_num) h
  have hB := (IntegrableOn.ofReal_mul_quad (f := fun x => x.2 / (x.1 + x.2))
    (by fun_prop) (c := 1) (fun x hx => (abs_div_add_le_one hx).2) h').const_mul (-(d / 2))
  refine (hA.add hB).congr_fun (fun x hx => ?_) measurableSet_quad
  have hu := ofReal_add_ne_zero hx
  simp only [monoD₁, kernelD₁, integrand, Pi.add_apply]
  rw [cpow_eq_mul_self hx.2.out (b - 1)]
  push_cast
  field_simp
  ring

/-- **B2, atomic step in `x₀`.** `∫ x ^ (ν - 1) ∂₀S = -(a - 1) ∫ x ^ (ν - e₀ - 1) S`. -/
theorem integral_monoD₀ {a b d : ℂ} (h : Conv a b d) (h' : Conv (a - 1) b d) :
    ∫ x in quad, monoD₀ a b d x = -((a - 1) * mellin₂ (a - 1) b d) := by
  have hint := integrableOn_monoD₀ h h'
  have h0 := integral_quad_eq_zero₀ (g := integrand a b d)
    (g' := fun x => (a - 1) * integrand (a - 1) b d x + monoD₀ a b d x) (fun x hx => ?_)
    ((h'.const_mul _).add hint) ?_
  · rw [integral_add (h'.const_mul _) hint, integral_const_mul] at h0
    rw [mellin₂]
    linear_combination h0
  · have hc := ((hasDerivAt_id (x.1 : ℂ)).cpow_const (c := a - 1)
      (ofReal_mem_slitPlane.mpr hx.1.out)).comp_ofReal
    refine ((hc.mul_const ((x.2 : ℂ) ^ (b - 1))).mul
      (hasDerivAt_kernel₀ d hx.1.out hx.2.out)).congr_deriv ?_
    simp only [integrand, monoD₀, id, mul_one]
    ring
  · refine h'.congr_fun (fun x hx => ?_) measurableSet_quad
    have h1 : (x.1 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.1.out.ne'
    simp only [integrand, Complex.real_smul, ofReal_inv]
    rw [cpow_eq_mul_self hx.1.out (a - 1)]
    field_simp

/-- **B2, atomic step in `x₁`.** `∫ x ^ (ν - 1) ∂₁S = -(b - 1) ∫ x ^ (ν - e₁ - 1) S`. -/
theorem integral_monoD₁ {a b d : ℂ} (h : Conv a b d) (h' : Conv a (b - 1) d) :
    ∫ x in quad, monoD₁ a b d x = -((b - 1) * mellin₂ a (b - 1) d) := by
  have hint := integrableOn_monoD₁ h h'
  have h0 := integral_quad_eq_zero₁ (g := integrand a b d)
    (g' := fun x => (b - 1) * integrand a (b - 1) d x + monoD₁ a b d x) (fun x hx => ?_)
    ((h'.const_mul _).add hint) ?_
  · rw [integral_add (h'.const_mul _) hint, integral_const_mul] at h0
    rw [mellin₂]
    linear_combination h0
  · have hc := ((hasDerivAt_id (x.2 : ℂ)).cpow_const (c := b - 1)
      (ofReal_mem_slitPlane.mpr hx.2.out)).comp_ofReal
    refine (((hc.const_mul ((x.1 : ℂ) ^ (a - 1)))).mul
      (hasDerivAt_kernel₁ d hx.1.out hx.2.out)).congr_deriv ?_
    simp only [integrand, monoD₁, id, mul_one]
    ring
  · refine h'.congr_fun (fun x hx => ?_) measurableSet_quad
    have h1 : (x.2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.2.out.ne'
    simp only [integrand, Complex.real_smul, ofReal_inv]
    rw [cpow_eq_mul_self hx.2.out (b - 1)]
    field_simp

theorem cpow_add_one_sub_one {t : ℝ} (ht : 0 < t) (c : ℂ) :
    (t : ℂ) ^ (c + 1 - 1) = (t : ℂ) ^ (c - 1) * t := by
  rw [add_sub_cancel_right, cpow_eq_mul_self ht c]

/-- **B1 + B2 for `∂/∂k · k`**, unnormalized:
`(2d - 4a - 2b) M(a, b) - 2(a - 1) M(a - 1, b + 1) = 0`. -/
theorem mellin₂_rel₀₀ {a b d : ℂ} (h₀ : Conv a b d) (h₁ : Conv (a + 1) b d)
    (h₂ : Conv a (b + 1) d) (h₃ : Conv (a - 1) (b + 1) d) :
    (2 * d - 4 * a - 2 * b) * mellin₂ a b d - 2 * (a - 1) * mellin₂ (a - 1) (b + 1) d = 0 := by
  have h₁' : Conv (a + 1 - 1) b d := by rwa [add_sub_cancel_right]
  have h₂' : Conv a (b + 1 - 1) d := by rwa [add_sub_cancel_right]
  have i₁ := integrableOn_monoD₀ h₁ h₁'
  have i₂ := integrableOn_monoD₀ h₂ h₃
  have i₃ := integrableOn_monoD₁ h₂ h₂'
  have e₁ := integral_monoD₀ h₁ h₁'
  have e₂ := integral_monoD₀ h₂ h₃
  have e₃ := integral_monoD₁ h₂ h₂'
  simp only [add_sub_cancel_right] at e₁ e₃
  have hz : ∫ x in quad, (2 * d * integrand a b d x + 4 * monoD₀ (a + 1) b d x +
      2 * monoD₀ a (b + 1) d x + 2 * monoD₁ a (b + 1) d x) = 0 := by
    rw [setIntegral_congr_fun measurableSet_quad (g := fun _ => (0 : ℂ)) (fun x hx => ?_),
      integral_zero]
    simp only [integrand, monoD₀, monoD₁]
    rw [cpow_add_one_sub_one hx.1.out, cpow_add_one_sub_one hx.2.out]
    linear_combination (x.1 : ℂ) ^ (a - 1) * (x.2 : ℂ) ^ (b - 1) * b1₀₀ d hx
  have j₁ : IntegrableOn (fun x => 2 * d * integrand a b d x + 4 * monoD₀ (a + 1) b d x) quad :=
    (h₀.const_mul _).add (i₁.const_mul _)
  have j₂ : IntegrableOn (fun x => 2 * d * integrand a b d x + 4 * monoD₀ (a + 1) b d x +
      2 * monoD₀ a (b + 1) d x) quad := j₁.add (i₂.const_mul _)
  rw [integral_add j₂ (i₃.const_mul _), integral_add j₁ (i₂.const_mul _),
    integral_add (h₀.const_mul _) (i₁.const_mul _)] at hz
  simp only [integral_const_mul, e₁, e₂, e₃] at hz
  simp only [mellin₂] at hz ⊢
  linear_combination hz

/-- **B1 + B2 for `∂/∂k · p`**, unnormalized:
`-2(b - 1) M(a + 1, b - 1) + 2(a - b) M(a, b) + 2(a - 1) M(a - 1, b + 1) + 4 M(a, b + 1) = 0`. -/
theorem mellin₂_rel₀₁ {a b d : ℂ} (h₀ : Conv a b d) (h₁ : Conv (a + 1) b d)
    (h₂ : Conv a (b + 1) d) (h₃ : Conv (a - 1) (b + 1) d) (h₄ : Conv (a + 1) (b - 1) d) :
    -2 * (b - 1) * mellin₂ (a + 1) (b - 1) d + 2 * (a - b) * mellin₂ a b d +
      2 * (a - 1) * mellin₂ (a - 1) (b + 1) d + 4 * mellin₂ a (b + 1) d = 0 := by
  have h₁' : Conv (a + 1 - 1) b d := by rwa [add_sub_cancel_right]
  have h₂' : Conv a (b + 1 - 1) d := by rwa [add_sub_cancel_right]
  have i₁ := integrableOn_monoD₁ h₁ h₄
  have i₂ := integrableOn_monoD₁ h₂ h₂'
  have i₃ := integrableOn_monoD₀ h₁ h₁'
  have i₄ := integrableOn_monoD₀ h₂ h₃
  have e₁ := integral_monoD₁ h₁ h₄
  have e₂ := integral_monoD₁ h₂ h₂'
  have e₃ := integral_monoD₀ h₁ h₁'
  have e₄ := integral_monoD₀ h₂ h₃
  simp only [add_sub_cancel_right] at e₂ e₃
  have hz : ∫ x in quad, (2 * monoD₁ (a + 1) b d x + 2 * monoD₁ a (b + 1) d x +
      (-2) * monoD₀ (a + 1) b d x + (-2) * monoD₀ a (b + 1) d x +
      4 * integrand a (b + 1) d x) = 0 := by
    rw [setIntegral_congr_fun measurableSet_quad (g := fun _ => (0 : ℂ)) (fun x hx => ?_),
      integral_zero]
    simp only [integrand, monoD₀, monoD₁]
    rw [cpow_add_one_sub_one hx.1.out, cpow_add_one_sub_one hx.2.out]
    linear_combination (x.1 : ℂ) ^ (a - 1) * (x.2 : ℂ) ^ (b - 1) * b1₀₁ d hx
  have j₁ : IntegrableOn (fun x => 2 * monoD₁ (a + 1) b d x + 2 * monoD₁ a (b + 1) d x) quad :=
    (i₁.const_mul _).add (i₂.const_mul _)
  have j₂ : IntegrableOn (fun x => 2 * monoD₁ (a + 1) b d x + 2 * monoD₁ a (b + 1) d x +
      (-2) * monoD₀ (a + 1) b d x) quad := j₁.add (i₃.const_mul _)
  have j₃ : IntegrableOn (fun x => 2 * monoD₁ (a + 1) b d x + 2 * monoD₁ a (b + 1) d x +
      (-2) * monoD₀ (a + 1) b d x + (-2) * monoD₀ a (b + 1) d x) quad := j₂.add (i₄.const_mul _)
  rw [integral_add j₃ (h₂.const_mul _), integral_add j₂ (i₄.const_mul _),
    integral_add j₁ (i₃.const_mul _), integral_add (i₁.const_mul _) (i₂.const_mul _)] at hz
  simp only [integral_const_mul, e₁, e₂, e₃, e₄] at hz
  simp only [mellin₂] at hz ⊢
  linear_combination hz

/-! ### The Γ-normalized integral and the checker's relations -/

/-- The Γ-normalized Schwinger integral
`I_S(a, b; d) = (Γ(a) Γ(b))⁻¹ ∫_{(0,∞)²} x₀ ^ (a - 1) x₁ ^ (b - 1) S(x) dx`. -/
noncomputable def schw (a b d : ℂ) : ℂ := mellin₂ a b d / (Gamma a * Gamma b)

/-- The entry `νᵢ` of a complex index vector, `0` out of range. -/
def vecGetC {n : ℕ} (ν : Fin n → ℂ) (i : ℕ) : ℂ := if h : i < n then ν ⟨i, h⟩ else 0

/-- The coefficient of a checker term at a complex index vector `ν` (for integer `ν` it is
`QED.Algebra.IBPCert.Term.coeff`). -/
def coeffC {n : ℕ} (t : QED.Algebra.IBPCert.Term) (d : ℂ) (ν : Fin n → ℂ) : ℂ :=
  t.c0 + t.cd * d + t.cnu * vecGetC ν t.idx

/-- A shift list as a complex index vector. -/
def shiftC (n : ℕ) (l : List ℤ) : Fin n → ℂ := fun i => ((l.getD i 0 : ℤ) : ℂ)

open QED.Algebra.IBPCert QED.Algebra.IBPCert.Pilot

/-- The precomputed relations of `oneLoopSE` are the generated ones. -/
theorem tmplOk_oneLoopSE : oneLoopSE.tmplOk = true := by decide +kernel

theorem gamma_facts {a b : ℂ} (ha : 1 < a.re) (hb : 1 < b.re) :
    (Gamma (a - 1) ≠ 0 ∧ Gamma (b - 1) ≠ 0) ∧ (a ≠ 0 ∧ b ≠ 0) ∧
      (Gamma a = (a - 1) * Gamma (a - 1) ∧ Gamma b = (b - 1) * Gamma (b - 1)) ∧
      (a - 1 ≠ 0 ∧ b - 1 ≠ 0) := by
  have ha1 : a - 1 ≠ 0 := fun h => by rw [sub_eq_zero.mp h] at ha; norm_num at ha
  have hb1 : b - 1 ≠ 0 := fun h => by rw [sub_eq_zero.mp h] at hb; norm_num at hb
  refine ⟨⟨Gamma_ne_zero_of_re_pos (by simp; linarith),
    Gamma_ne_zero_of_re_pos (by simp; linarith)⟩,
    ⟨fun h => by rw [h] at ha; norm_num at ha, fun h => by rw [h] at hb; norm_num at hb⟩,
    ⟨by rw [← Gamma_add_one _ ha1, sub_add_cancel],
      by rw [← Gamma_add_one _ hb1, sub_add_cancel]⟩, ha1, hb1⟩

/-- **B1 + B2 for `∂/∂k · k`**, Γ-normalized:
`(2d - 4a - 2b) I_S(a, b) - 2b I_S(a - 1, b + 1) = 0`. -/
theorem schw_rel₀₀ {a b d : ℂ} (ha : 1 < a.re) (hb : 1 < b.re) (h₀ : Conv a b d)
    (h₁ : Conv (a + 1) b d) (h₂ : Conv a (b + 1) d) (h₃ : Conv (a - 1) (b + 1) d) :
    (2 * d - 4 * a - 2 * b) * schw a b d - 2 * b * schw (a - 1) (b + 1) d = 0 := by
  obtain ⟨⟨gA, gB⟩, ⟨ha0, hb0⟩, ⟨Ga, Gb⟩, ⟨ha1, hb1⟩⟩ := gamma_facts ha hb
  simp only [schw, Gamma_add_one _ hb0, Ga, Gb]
  field_simp
  linear_combination mellin₂_rel₀₀ h₀ h₁ h₂ h₃

/-- **B1 + B2 for `∂/∂k · p`**, Γ-normalized (Euclidean signs):
`2a I_S - 2a I_S(a + 1, b - 1) + 2b I_S(a - 1, b + 1) - 2b I_S + 4b I_S(a, b + 1) = 0`. -/
theorem schw_rel₀₁ {a b d : ℂ} (ha : 1 < a.re) (hb : 1 < b.re) (h₀ : Conv a b d)
    (h₁ : Conv (a + 1) b d) (h₂ : Conv a (b + 1) d) (h₃ : Conv (a - 1) (b + 1) d)
    (h₄ : Conv (a + 1) (b - 1) d) :
    2 * a * schw a b d - 2 * a * schw (a + 1) (b - 1) d + 2 * b * schw (a - 1) (b + 1) d -
      2 * b * schw a b d + 4 * b * schw a (b + 1) d = 0 := by
  obtain ⟨⟨gA, gB⟩, ⟨ha0, hb0⟩, ⟨Ga, Gb⟩, ⟨ha1, hb1⟩⟩ := gamma_facts ha hb
  simp only [schw, Gamma_add_one _ ha0, Gamma_add_one _ hb0, Ga, Gb]
  field_simp
  linear_combination mellin₂_rel₀₁ h₀ h₁ h₂ h₃ h₄

/-- **The checker's IBP relations for the Schwinger integral (B1 + B2).** For `j < 2`, at every
complex `ν` with `re νᵢ > 1` where the five integrals involved converge, the relation
`template 0 j` of `oneLoopSE` holds for `(-1) ^ |ν| I_S(ν; d)` (the factor `(-1) ^ |shift|`
below; it is the sign `(-1) ^ |ν|` relating the Minkowski family `oneLoopSE` to the Euclidean
integral, see the module docstring). -/
theorem schw_template {j : ℕ} (hj : j < 2) {ν : Fin 2 → ℂ} {d : ℂ} (ha : 1 < (ν 0).re)
    (hb : 1 < (ν 1).re) (h₀ : Conv (ν 0) (ν 1) d) (h₁ : Conv (ν 0 + 1) (ν 1) d)
    (h₂ : Conv (ν 0) (ν 1 + 1) d) (h₃ : Conv (ν 0 - 1) (ν 1 + 1) d)
    (h₄ : Conv (ν 0 + 1) (ν 1 - 1) d) :
    ((oneLoopSE.template 0 j).map fun t => coeffC t d ν * (-1 : ℂ) ^ t.shift.sum *
      schw ((ν + shiftC 2 t.shift) 0) ((ν + shiftC 2 t.shift) 1) d).sum = 0 := by
  rw [← Family.tmplAt_eq_template tmplOk_oneLoopSE (by decide) hj]
  interval_cases j
  · simp [Family.tmplAt, oneLoopSE, coeffC, vecGetC, shiftC, ← sub_eq_add_neg]
    linear_combination schw_rel₀₀ ha hb h₀ h₁ h₂ h₃
  · simp [Family.tmplAt, oneLoopSE, coeffC, vecGetC, shiftC, ← sub_eq_add_neg]
    linear_combination schw_rel₀₁ ha hb h₀ h₁ h₂ h₃ h₄

end QED.DimReg.OneLoopSchwinger
