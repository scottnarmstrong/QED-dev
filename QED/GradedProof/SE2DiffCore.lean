/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2ParamCont
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Differentiability of integrals of ratios of polynomial families

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 3.

* `differentiableAt_integral_poly_div`: if `a(x, ·)`, `v(x, ·)` are polynomials of bounded
  degree, the coefficients of `a` integrable, those of `v` bounded, and `|v(x, 0)| ≥ c > 0`, then
  `u ↦ ∫ a(x, u) / v(x, u)ᴺ` is differentiable at `0` (differentiation under the integral sign:
  near `0`, `|v| ≥ c / 2`, and the derivative of the integrand is bounded by an integrable
  function).
* `differentiableAt_integral_upoly`: the same for polynomial families on `(-1, 1)` given by their
  values at the interpolation nodes (`IsUPoly`).
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set Polynomial Metric

namespace QED.GradedProof.SE2

open QED.TwoLoop.PauliZeroLimit

/-! ### Bounds on polynomials on `[-1, 1]` -/

theorem norm_eval_le_of_natDegree {P : ℂ[X]} {D : ℕ} (hP : P.natDegree ≤ D) {u : ℝ}
    (hu : |u| ≤ 1) : ‖P.eval (u : ℂ)‖ ≤ ∑ j ∈ Finset.range (D + 1), ‖P.coeff j‖ := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hP)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (abs_nonneg u) hu)

theorem norm_derivative_eval_le {P : ℂ[X]} {D : ℕ} (hP : P.natDegree ≤ D) {u : ℝ}
    (hu : |u| ≤ 1) :
    ‖P.derivative.eval (u : ℂ)‖ ≤ ∑ j ∈ Finset.range (D + 1), ‖P.coeff (j + 1)‖ * (j + 1) := by
  have hd : P.derivative.natDegree ≤ D := (natDegree_derivative_le P).trans (by omega)
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hd)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [coeff_derivative, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖((j : ℂ) + 1)‖ = (j : ℝ) + 1 := by
    rw [show ((j : ℂ) + 1) = ((j + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  rw [h1]
  exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (abs_nonneg u) hu)

theorem norm_eval_sub_eval_zero_le {P : ℂ[X]} {D : ℕ} (hP : P.natDegree ≤ D) {u : ℝ}
    (hu : |u| ≤ 1) :
    ‖P.eval (u : ℂ) - P.eval 0‖ ≤ |u| * ∑ j ∈ Finset.range (D + 1), ‖P.coeff j‖ := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hP), eval_eq_sum_range' (Nat.lt_succ_of_le hP),
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← mul_sub, norm_mul]
  rcases j with _ | j
  · simp only [pow_zero, sub_self, norm_zero, mul_zero]
    positivity
  · rw [zero_pow (Nat.succ_ne_zero j), sub_zero, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [pow_succ]
    exact mul_le_of_le_one_left (abs_nonneg u) (pow_le_one₀ (abs_nonneg u) hu)

/-! ### Differentiation under the integral sign -/

section Core

variable {ι : Type*} [MeasurableSpace ι] {μ : Measure ι}

theorem aestronglyMeasurable_eval {a : ι → ℂ[X]} {D : ℕ} (ha : ∀ x, (a x).natDegree ≤ D)
    (hm : ∀ j, AEStronglyMeasurable (fun x => (a x).coeff j) μ) (z : ℂ) :
    AEStronglyMeasurable (fun x => (a x).eval z) μ := by
  have e : (fun x => (a x).eval z) = fun x => ∑ j ∈ Finset.range (D + 1), (a x).coeff j * z ^ j :=
    funext fun x => eval_eq_sum_range' (Nat.lt_succ_of_le (ha x)) z
  rw [e]
  exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hm j).mul aestronglyMeasurable_const

theorem aestronglyMeasurable_derivative_eval {a : ι → ℂ[X]} {D : ℕ}
    (ha : ∀ x, (a x).natDegree ≤ D) (hm : ∀ j, AEStronglyMeasurable (fun x => (a x).coeff j) μ)
    (z : ℂ) : AEStronglyMeasurable (fun x => (a x).derivative.eval z) μ := by
  have hd : ∀ x, (a x).derivative.natDegree ≤ D := fun x =>
    (natDegree_derivative_le _).trans (by have := ha x; omega)
  refine aestronglyMeasurable_eval hd (fun j => ?_) z
  simp only [coeff_derivative]
  exact (hm (j + 1)).mul aestronglyMeasurable_const

/-- **Differentiability of `u ↦ ∫ a(x, u) / v(x, u)ᴺ` at `0`.** -/
theorem differentiableAt_integral_poly_div {N D E : ℕ} {a v : ι → ℂ[X]}
    (ha : ∀ x, (a x).natDegree ≤ D) (hv : ∀ x, (v x).natDegree ≤ E)
    (hai : ∀ j, Integrable (fun x => (a x).coeff j) μ)
    (hvm : ∀ j, AEStronglyMeasurable (fun x => (v x).coeff j) μ) {K : ℕ → ℝ}
    (hK0 : ∀ j, 0 ≤ K j) (hK : ∀ j, ∀ᵐ x ∂μ, ‖(v x).coeff j‖ ≤ K j) {c : ℝ} (hc : 0 < c)
    (hv0 : ∀ᵐ x ∂μ, c ≤ ‖(v x).eval 0‖) :
    DifferentiableAt ℝ (fun u : ℝ => ∫ x, (a x).eval (u : ℂ) / (v x).eval (u : ℂ) ^ N ∂μ) 0 := by
  set KV : ℝ := ∑ j ∈ Finset.range (E + 1), K j with hKV
  set KV' : ℝ := ∑ j ∈ Finset.range (E + 1), K (j + 1) * (j + 1) with hKV'
  have hKV0 : 0 ≤ KV := Finset.sum_nonneg fun j _ => hK0 j
  have hKae : ∀ᵐ x ∂μ, ∀ j, ‖(v x).coeff j‖ ≤ K j := ae_all_iff.mpr hK
  set δ : ℝ := min (1 / 2) (c / (2 * (KV + 1))) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδKV : δ * KV ≤ c / 2 := by
    calc δ * KV ≤ c / (2 * (KV + 1)) * KV := mul_le_mul_of_nonneg_right (min_le_right _ _) hKV0
      _ ≤ c / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have hball : ∀ u ∈ ball (0 : ℝ) δ, |u| ≤ 1 := fun u hu => by
    rw [mem_ball, Real.dist_eq, sub_zero] at hu
    linarith
  -- bounds at a good point
  set Ba : ι → ℝ := fun x => ∑ j ∈ Finset.range (D + 1), ‖(a x).coeff j‖ with hBa
  set Ba' : ι → ℝ := fun x => ∑ j ∈ Finset.range (D + 1), ‖(a x).coeff (j + 1)‖ * (j + 1)
    with hBa'
  have hBai : Integrable Ba μ := integrable_finsetSum _ fun j _ => (hai j).norm
  have hBai' : Integrable Ba' μ :=
    integrable_finsetSum _ fun j _ => (hai (j + 1)).norm.mul_const _
  have hgood : ∀ x, (∀ j, ‖(v x).coeff j‖ ≤ K j) → c ≤ ‖(v x).eval 0‖ → ∀ u ∈ ball (0 : ℝ) δ,
      c / 2 ≤ ‖(v x).eval (u : ℂ)‖ ∧ ‖(v x).eval (u : ℂ)‖ ≤ KV ∧
        ‖(v x).derivative.eval (u : ℂ)‖ ≤ KV' := by
    intro x hx h0 u hu
    have hu1 := hball u hu
    have hsum : ∑ j ∈ Finset.range (E + 1), ‖(v x).coeff j‖ ≤ KV :=
      Finset.sum_le_sum fun j _ => hx j
    refine ⟨?_, (norm_eval_le_of_natDegree (hv x) hu1).trans hsum,
      (norm_derivative_eval_le (hv x) hu1).trans
        (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hx _) (by positivity))⟩
    have h1 := norm_eval_sub_eval_zero_le (hv x) hu1
    have h2 : |u| * ∑ j ∈ Finset.range (E + 1), ‖(v x).coeff j‖ ≤ c / 2 := by
      have hu' : |u| ≤ δ := by
        rw [mem_ball, Real.dist_eq, sub_zero] at hu
        exact hu.le
      calc |u| * ∑ j ∈ Finset.range (E + 1), ‖(v x).coeff j‖ ≤ δ * KV :=
            mul_le_mul hu' hsum (Finset.sum_nonneg fun _ _ => norm_nonneg _) hδ0.le
        _ ≤ c / 2 := hδKV
    have h3 := norm_sub_norm_le ((v x).eval 0) ((v x).eval (u : ℂ))
    rw [norm_sub_rev] at h3
    linarith
  -- the integrand and its derivative
  set F : ℝ → ι → ℂ := fun u x => (a x).eval (u : ℂ) / (v x).eval (u : ℂ) ^ N with hF
  set F' : ℝ → ι → ℂ := fun u x => ((a x).derivative.eval (u : ℂ) * (v x).eval (u : ℂ) ^ N -
      (a x).eval (u : ℂ) * ((N : ℂ) * (v x).eval (u : ℂ) ^ (N - 1) *
        (v x).derivative.eval (u : ℂ))) / ((v x).eval (u : ℂ) ^ N) ^ 2 with hF'
  have hderiv : ∀ x (u : ℝ), (v x).eval (u : ℂ) ≠ 0 → HasDerivAt (fun u => F u x) (F' u x) u := by
    intro x u hne
    have h1 := Polynomial.hasDerivAt (a x) (u : ℂ)
    have h2 := Polynomial.hasDerivAt ((v x) ^ N) (u : ℂ)
    have hne' : ((v x) ^ N).eval (u : ℂ) ≠ 0 := by rw [eval_pow]; exact pow_ne_zero _ hne
    have h3 := (h1.fun_div h2 hne').comp_ofReal
    simp only [eval_pow, derivative_pow, eval_mul, eval_C] at h3
    exact h3
  have hmeas : ∀ u : ℝ, AEStronglyMeasurable (F u) μ := fun u =>
    (aestronglyMeasurable_eval ha (fun j => (hai j).1) _).div₀
      ((aestronglyMeasurable_eval hv hvm _).pow N)
  have hmeas' : AEStronglyMeasurable (F' 0) μ := by
    have hA := aestronglyMeasurable_eval ha (fun j => (hai j).1) ((0 : ℝ) : ℂ)
    have hA' := aestronglyMeasurable_derivative_eval ha (fun j => (hai j).1) ((0 : ℝ) : ℂ)
    have hV := aestronglyMeasurable_eval hv hvm ((0 : ℝ) : ℂ)
    have hV' := aestronglyMeasurable_derivative_eval hv hvm ((0 : ℝ) : ℂ)
    exact ((hA'.mul (hV.pow N)).sub (hA.mul ((aestronglyMeasurable_const.mul
      (hV.pow (N - 1))).mul hV'))).div₀ ((hV.pow N).pow 2)
  have hint : Integrable (F 0) μ := by
    refine (hBai.div_const (c ^ N)).mono' (hmeas 0) ?_
    filter_upwards [hv0] with x hx
    simp only [hF, ofReal_zero]
    rw [norm_div, norm_pow]
    have hA := norm_eval_le_of_natDegree (ha x) (u := 0) (by simp)
    simp only [ofReal_zero] at hA
    exact div_le_div₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) hA (by positivity)
      (pow_le_pow_left₀ hc.le hx N)
  set bound : ι → ℝ := fun x => (Ba' x * KV ^ N + Ba x * (N * KV ^ (N - 1) * KV')) /
    ((c / 2) ^ N) ^ 2 with hbound
  have hbi : Integrable bound μ :=
    ((hBai'.mul_const _).add (hBai.mul_const _)).div_const _
  have hb : ∀ᵐ x ∂μ, ∀ u ∈ ball (0 : ℝ) δ, ‖F' u x‖ ≤ bound x := by
    filter_upwards [hKae, hv0] with x hx h0 u hu
    obtain ⟨l1, l2, l3⟩ := hgood x hx h0 u hu
    have hu1 := hball u hu
    have hA := norm_eval_le_of_natDegree (ha x) hu1
    have hA' := norm_derivative_eval_le (ha x) hu1
    have hc2 : 0 < c / 2 := by positivity
    have hBa0 : 0 ≤ Ba x := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hBa0' : 0 ≤ Ba' x := Finset.sum_nonneg fun _ _ => by positivity
    have hKV'0 : 0 ≤ KV' := Finset.sum_nonneg fun j _ => mul_nonneg (hK0 _) (by positivity)
    simp only [hF', hbound]
    rw [norm_div, norm_pow, norm_pow]
    refine div_le_div₀ (add_nonneg (mul_nonneg hBa0' (pow_nonneg hKV0 _))
      (mul_nonneg hBa0 (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hKV0 _)) hKV'0)))
      ?_ (by positivity)
      (pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hc2.le l1 N) 2)
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_pow]
      exact mul_le_mul hA' (pow_le_pow_left₀ (norm_nonneg _) l2 N) (by positivity)
        (Finset.sum_nonneg fun _ _ => by positivity)
    · rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
      exact mul_le_mul hA (mul_le_mul (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) l2 _) (Nat.cast_nonneg _)) l3 (norm_nonneg _)
        (by positivity)) (by positivity) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hd : ∀ᵐ x ∂μ, ∀ u ∈ ball (0 : ℝ) δ, HasDerivAt (fun u => F u x) (F' u x) u := by
    filter_upwards [hKae, hv0] with x hx h0 u hu
    have l1 := (hgood x hx h0 u hu).1
    refine hderiv x u fun h => ?_
    rw [h, norm_zero] at l1
    linarith
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds 0 hδ0)
    (Eventually.of_forall hmeas) hint hmeas' hb hbi hd).2.differentiableAt

/-- **Differentiability at `0` of `u ↦ ∫ A(x, u) / V(x, u)ᴺ`** for polynomial families on
`(-1, 1)` with integrable (resp. bounded) values at the nodes and `|V(x, 0)| ≥ c > 0`. -/
theorem differentiableAt_integral_upoly {D E N : ℕ} {A V : ι → ℝ → ℂ} (hA : IsUPoly D A)
    (hAi : ∀ k, Integrable (fun x => A x (node D k)) μ) (hV : IsUPoly E V)
    (hVm : ∀ k, AEStronglyMeasurable (fun x => V x (node E k)) μ) {K c : ℝ}
    (hK : ∀ k, ∀ᵐ x ∂μ, ‖V x (node E k)‖ ≤ K) (hc : 0 < c) (hV0 : ∀ᵐ x ∂μ, c ≤ ‖V x 0‖) :
    DifferentiableAt ℝ (fun u : ℝ => ∫ x, A x u / V x u ^ N ∂μ) 0 := by
  set bs : Fin (E + 1) → ℂ[X] := fun k =>
    Lagrange.basis Finset.univ (fun k : Fin (E + 1) => ((node E k : ℝ) : ℂ)) k
  have hKae : ∀ᵐ x ∂μ, ∀ k, ‖V x (node E k)‖ ≤ K := ae_all_iff.mpr hK
  have hcoeff : ∀ j, ∀ᵐ x ∂μ, ‖(interp E V x).coeff j‖ ≤ max K 0 * ∑ k, ‖(bs k).coeff j‖ := by
    intro j
    filter_upwards [hKae] with x hx
    rw [interp_coeff, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ((hx k).trans (le_max_left _ _)) (norm_nonneg _)
  have hvm : ∀ j, AEStronglyMeasurable (fun x => (interp E V x).coeff j) μ := fun j => by
    simp only [interp_coeff]
    exact Finset.aestronglyMeasurable_fun_sum _ fun k _ => (hVm k).mul aestronglyMeasurable_const
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hv0 : ∀ᵐ x ∂μ, c ≤ ‖(interp E V x).eval 0‖ := by
    filter_upwards [hV0] with x hx
    have := hV.eq_interp x 0 h0
    rw [ofReal_zero] at this
    rwa [← this]
  have hd := differentiableAt_integral_poly_div (N := N) (natDegree_interp_le (f := A))
    (natDegree_interp_le (f := V)) (integrable_interp_coeff hAi) hvm
    (fun j => mul_nonneg (le_max_right _ _) (Finset.sum_nonneg fun _ _ => norm_nonneg _))
    hcoeff hc hv0
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with u hu
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hA.eq_interp x u hu, hV.eq_interp x u hu]

end Core

end QED.GradedProof.SE2

end
