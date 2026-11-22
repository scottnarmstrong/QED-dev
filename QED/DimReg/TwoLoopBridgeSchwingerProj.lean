/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.TwoLoopBridgeLP
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# The Schwinger-parameter integral in projective form

After Schwinger parametrization and the Gaussian loop integration, a Feynman integral becomes
the orthant integral of the **Schwinger integrand** `α^(ν-1) U(α)^(-d/2) e^(-F(α)/U(α))`
(`QED.DimReg.FeynmanFamily.schwIntegrand`). For homogeneous `U`, `F` (degrees `L`, `L + 1`),
positive on the open orthant, the orthant integral is the projective integral of
`QED.DimReg.FeynmanFamily.projIntegrand` with the factor `Γ(a)`, `a = |ν| - L d / 2`:
`∫_{(0,∞)^N} α^(ν-1) U^(-d/2) e^(-F/U) = Γ(a) ∫_Δ y^(ν-1) U^(-b) F^(-a)`
(`integral_schwIntegrand_eq_proj`), and the left side converges absolutely exactly when the
projective integral does (`integrableOn_schwIntegrand_iff`). With
`QED.DimReg.LPChange.integral_eq_proj` this identifies the Schwinger form with
`QED.DimReg.FeynmanFamily.integral`.

The proof is the cone decomposition `α = s · y` of `QED.DimReg.LPChange.integral_posOrthant_eq_cone`
followed by the ray integral `∫₀^∞ s^(a-1) e^(-c s) ds = Γ(a) c^(-a)`
(`Complex.integral_cpow_mul_exp_neg_mul_Ioi`), as for the Lee–Pomeransky form in
`QED/DimReg/TwoLoopBridgeLP.lean`.
-/

@[expose] public section

open MeasureTheory Set Complex MvPolynomial

namespace QED.DimReg.FeynmanFamily

variable {N : ℕ}

/-- The Schwinger integrand `α^(ν-1) U(α)^(-d/2) e^(-F(α)/U(α))`. -/
noncomputable def schwIntegrand (P : FeynmanFamily N) (ν : Fin N → ℂ) (d : ℂ)
    (x : Fin N → ℝ) : ℂ :=
  (∏ i, (x i : ℂ) ^ (ν i - 1)) * (eval x P.U : ℂ) ^ (-(d / 2)) *
    exp (-((eval x P.F / eval x P.U : ℝ) : ℂ))

end QED.DimReg.FeynmanFamily

namespace QED.DimReg.SchwingerProj

open QED.Integration.Feynman (simplexPoint)
open QED.Integration.ChengWu (openSimplex mem_openSimplex)
open QED.DimReg.LPChange
open FeynmanFamily

variable {m : ℕ}

/-! ### The ray integral -/

/-- `∫₀^∞ s^(a-1) e^(-c s) ds = c^(-a) Γ(a)` for `re a > 0`, `c > 0`. -/
theorem integral_ray {a : ℂ} (ha : 0 < a.re) {c : ℝ} (hc : 0 < c) :
    ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (a - 1) * exp (-((c * s : ℝ) : ℂ)) =
      (c : ℂ) ^ (-a) * Gamma a := by
  have h := integral_cpow_mul_exp_neg_mul_Ioi ha hc
  push_cast
  rw [h]
  congr 1
  rw [show (1 : ℂ) / c = ((c⁻¹ : ℝ) : ℂ) by push_cast; ring, cpow_ofReal_pos (inv_pos.mpr hc),
    cpow_ofReal_pos hc, Real.log_inv]
  push_cast
  ring_nf

theorem norm_ray {a : ℂ} {c s : ℝ} (hs : 0 < s) :
    ‖(s : ℂ) ^ (a - 1) * exp (-((c * s : ℝ) : ℂ))‖ = s ^ (a.re - 1) * Real.exp (-(c * s)) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hs, norm_exp]
  simp

theorem integral_norm_ray {a : ℂ} (ha : 0 < a.re) {c : ℝ} (hc : 0 < c) :
    ∫ s in Ioi (0 : ℝ), ‖(s : ℂ) ^ (a - 1) * exp (-((c * s : ℝ) : ℂ))‖ =
      (1 / c) ^ a.re * Real.Gamma a.re := by
  rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi ha hc]
  exact setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => norm_ray hs

theorem integrableOn_ray {a : ℂ} (ha : 0 < a.re) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => (s : ℂ) ^ (a - 1) * exp (-((c * s : ℝ) : ℂ))) (Ioi 0) := by
  have hne : ∫ s in Ioi (0 : ℝ), ‖(s : ℂ) ^ (a - 1) * exp (-((c * s : ℝ) : ℂ))‖ ≠ 0 := by
    rw [integral_norm_ray ha hc]
    exact (mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.Gamma_pos_of_pos ha)).ne'
  have hint := Integrable.of_integral_ne_zero hne
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => (s : ℂ) ^ (a - 1) * exp (-((c * s : ℝ) : ℂ))) (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ (by fun_prop)
    exact fun s (hs : 0 < s) =>
      (continuousAt_ofReal_cpow_const _ _ (Or.inr hs.ne')).continuousWithinAt
  exact (integrable_norm_iff hmeas).mp hint

/-! ### The cone integrand -/

variable (P : FeynmanFamily (m + 1)) (ν : Fin (m + 1) → ℂ) (d : ℂ)

/-- On the ray through a positive point `y`, the cone integrand of the Schwinger integrand is the
Γ integrand `s^(a-1) e^(-c s)` with `c = F(y) / U(y)`. -/
theorem cone_schwIntegrand_eq (hP : P.IsHomogeneous) {y : Fin (m + 1) → ℝ} (hy : ∀ i, 0 < y i)
    (hU : 0 < eval y P.U) (hF : 0 < eval y P.F) {s : ℝ} (hs : 0 < s) :
    s ^ m • P.schwIntegrand ν d (s • y) =
      ((∏ i, (y i : ℂ) ^ (ν i - 1)) * (eval y P.U : ℂ) ^ (-(d / 2))) *
        ((s : ℂ) ^ (P.projA ν d - 1) *
          exp (-((eval y P.F / eval y P.U * s : ℝ) : ℂ))) := by
  set u := eval y P.U
  set f := eval y P.F
  have hUs : eval (s • y) P.U = s ^ P.loops * u := eval_smul_of_isHomogeneous hP.1 s y
  have hFs : eval (s • y) P.F = s ^ (P.loops + 1) * f := eval_smul_of_isHomogeneous hP.2 s y
  have hrat : eval (s • y) P.F / eval (s • y) P.U = f / u * s := by
    rw [hUs, hFs]
    field_simp
    ring
  rw [schwIntegrand, hrat, hUs, Complex.real_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hpos : ∀ i, 0 < s * y i := fun i => mul_pos hs (hy i)
  simp only [cpow_ofReal_pos (hpos _), cpow_ofReal_pos (hy _), cpow_ofReal_pos hU,
    cpow_ofReal_pos hs, cpow_ofReal_pos (by positivity : 0 < s ^ P.loops * u),
    ← Complex.exp_sum]
  rw [Real.log_mul (by positivity) hU.ne', Real.log_pow]
  have hsm : ((s ^ m : ℝ) : ℂ) = exp ((Real.log s : ℂ) * m) := by
    rw [← cpow_ofReal_pos hs, ofReal_pow, cpow_natCast]
  rw [hsm]
  simp only [← Complex.exp_add]
  congr 1
  simp only [Real.log_mul hs.ne' (hy _).ne', ofReal_add, ofReal_mul, ofReal_natCast, add_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, mul_sub]
  simp only [projA]
  push_cast
  ring

theorem measurable_schwIntegrand : Measurable (P.schwIntegrand ν d) := by
  unfold schwIntegrand
  have hU : Measurable fun x : Fin (m + 1) → ℝ => eval x P.U :=
    (MvPolynomial.continuous_eval P.U).measurable
  have hF : Measurable fun x : Fin (m + 1) → ℝ => eval x P.F :=
    (MvPolynomial.continuous_eval P.F).measurable
  refine (Measurable.mul ?_ ?_).mul ?_
  · exact Finset.measurable_prod _ fun i _ =>
      (measurable_ofReal.comp (measurable_pi_apply i)).pow_const _
  · exact (measurable_ofReal.comp hU).pow_const _
  · exact (measurable_ofReal.comp (hF.div hU)).neg.cexp

theorem measurable_coneIntegrand_schwIntegrand :
    Measurable (coneIntegrand (P.schwIntegrand ν d)) := by
  unfold coneIntegrand
  refine (measurable_fst.pow_const _).smul ((measurable_schwIntegrand P ν d).comp ?_)
  exact (continuous_fst.smul (continuous_simplexPoint.comp continuous_snd)).measurable

/-! ### The projective form -/

/-- **The Schwinger integral in projective form.** For a homogeneous family with `U, F > 0` on
the open orthant, `re a > 0` and absolute convergence,
`∫_{(0,∞)^N} α^(ν-1) U^(-d/2) e^(-F/U) = Γ(a) ∫_Δ y^(ν-1) U^(-b) F^(-a)`. -/
theorem integral_schwIntegrand_eq_proj (hP : P.IsHomogeneous)
    (hU : ∀ y : Fin (m + 1) → ℝ, (∀ i, 0 < y i) → 0 < eval y P.U)
    (hF : ∀ y : Fin (m + 1) → ℝ, (∀ i, 0 < y i) → 0 < eval y P.F)
    (ha : 0 < (P.projA ν d).re)
    (hint : IntegrableOn (P.schwIntegrand ν d) (posOrthant (m + 1))) :
    ∫ x in posOrthant (m + 1), P.schwIntegrand ν d x =
      Gamma (P.projA ν d) * ∫ x in openSimplex m, P.projIntegrand ν d x := by
  rw [integral_posOrthant_eq_cone _ hint, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_openSimplex fun x hx => ?_
  have hy := simplexPoint_pos hx
  have hUx := hU _ hy
  have hFx := hF _ hy
  rw [setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) =>
      cone_schwIntegrand_eq P ν d hP hy hUx hFx hs,
    integral_const_mul, integral_ray ha (div_pos hFx hUx), projIntegrand_eq P ν d hUx hFx]
  ring

/-- **Convergence in projective form.** Under the hypotheses of
`integral_schwIntegrand_eq_proj`, the Schwinger integral converges absolutely exactly when the
projective integral does. -/
theorem integrableOn_schwIntegrand_iff (hP : P.IsHomogeneous)
    (hU : ∀ y : Fin (m + 1) → ℝ, (∀ i, 0 < y i) → 0 < eval y P.U)
    (hF : ∀ y : Fin (m + 1) → ℝ, (∀ i, 0 < y i) → 0 < eval y P.F)
    (ha : 0 < (P.projA ν d).re) :
    IntegrableOn (P.schwIntegrand ν d) (posOrthant (m + 1)) ↔
      IntegrableOn (P.projIntegrand ν d) (openSimplex m) := by
  rw [integrableOn_posOrthant_iff, IntegrableOn, ← Measure.prod_restrict,
    integrable_prod_iff' (measurable_coneIntegrand_schwIntegrand P ν d).aestronglyMeasurable]
  have hray : ∀ x ∈ openSimplex m, ∀ s ∈ Ioi (0 : ℝ),
      coneIntegrand (P.schwIntegrand ν d) (s, x) =
        ((∏ i, (simplexPoint x i : ℂ) ^ (ν i - 1)) *
          (eval (simplexPoint x) P.U : ℂ) ^ (-(d / 2))) *
          ((s : ℂ) ^ (P.projA ν d - 1) * exp (-((eval (simplexPoint x) P.F /
            eval (simplexPoint x) P.U * s : ℝ) : ℂ))) := fun x hx s hs =>
    cone_schwIntegrand_eq P ν d hP (simplexPoint_pos hx) (hU _ (simplexPoint_pos hx))
      (hF _ (simplexPoint_pos hx)) hs
  have h1 : ∀ᵐ x ∂(volume.restrict (openSimplex m)),
      Integrable (fun s => coneIntegrand (P.schwIntegrand ν d) (s, x))
        (volume.restrict (Ioi 0)) := by
    refine ae_restrict_of_forall_mem measurableSet_openSimplex fun x hx => ?_
    have hc := div_pos (hF _ (simplexPoint_pos hx)) (hU _ (simplexPoint_pos hx))
    exact IntegrableOn.congr_fun ((integrableOn_ray ha hc).const_mul _)
      (fun s hs => (hray x hx s hs).symm) measurableSet_Ioi
  rw [and_iff_right h1]
  have h2 : ∀ x ∈ openSimplex m,
      ∫ s in Ioi 0, ‖coneIntegrand (P.schwIntegrand ν d) (s, x)‖ =
        Real.Gamma (P.projA ν d).re * ‖P.projIntegrand ν d x‖ := by
    intro x hx
    have hUx := hU _ (simplexPoint_pos hx)
    have hFx := hF _ (simplexPoint_pos hx)
    rw [setIntegral_congr_fun measurableSet_Ioi fun s hs => by rw [hray x hx s hs, norm_mul],
      integral_const_mul, integral_norm_ray ha (div_pos hFx hUx),
      projIntegrand_eq P ν d hUx hFx, norm_mul (_ * _),
      norm_cpow_eq_rpow_re_of_pos (div_pos hFx hUx), neg_re, one_div,
      Real.inv_rpow (div_pos hFx hUx).le, Real.rpow_neg (div_pos hFx hUx).le]
    ring
  rw [integrable_congr (ae_restrict_of_forall_mem measurableSet_openSimplex h2),
    integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (Real.Gamma_pos_of_pos ha).ne'),
    integrable_norm_iff (measurable_projIntegrand P ν d).aestronglyMeasurable, IntegrableOn]

end QED.DimReg.SchwingerProj
