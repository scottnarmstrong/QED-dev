/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2DiffCore

/-!
# Differentiation under the integral sign, with the value of the derivative

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A2. The differentiability statements
`QED.GradedProof.SE2.differentiableAt_integral_poly_div` and `…_upoly` with the derivative
identified:

* `hasDerivAt_integral_poly_div`: for polynomial families `a(x, ·)`, `v(x, ·)` (integrable,
  resp. bounded, coefficients, `|v(x, 0)| ≥ c > 0`) the derivative at `0` of
  `u ↦ ∫ a(x, u) / v(x, u)ᴺ` is the integral of the derivative of the integrand;
* `hasDerivAt_integral_upoly`: the same for families given by node values (`IsUPoly`), with
  the derivative written as `∫ x, deriv (fun u => A x u / V x u ^ N) 0`.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set Polynomial Metric

namespace QED.GradedProof.WI2

open QED.TwoLoop.PauliZeroLimit

section Core

variable {ι : Type*} [MeasurableSpace ι] {μ : Measure ι}

/-- **The derivative of `u ↦ ∫ a(x, u) / v(x, u)ᴺ` at `0`** is the integral of the derivative. -/
theorem hasDerivAt_integral_poly_div {N D E : ℕ} {a v : ι → ℂ[X]}
    (ha : ∀ x, (a x).natDegree ≤ D) (hv : ∀ x, (v x).natDegree ≤ E)
    (hai : ∀ j, Integrable (fun x => (a x).coeff j) μ)
    (hvm : ∀ j, AEStronglyMeasurable (fun x => (v x).coeff j) μ) {K : ℕ → ℝ}
    (hK0 : ∀ j, 0 ≤ K j) (hK : ∀ j, ∀ᵐ x ∂μ, ‖(v x).coeff j‖ ≤ K j) {c : ℝ} (hc : 0 < c)
    (hv0 : ∀ᵐ x ∂μ, c ≤ ‖(v x).eval 0‖) :
    HasDerivAt (fun u : ℝ => ∫ x, (a x).eval (u : ℂ) / (v x).eval (u : ℂ) ^ N ∂μ)
      (∫ x, ((a x).derivative.eval ((0 : ℝ) : ℂ) * (v x).eval ((0 : ℝ) : ℂ) ^ N -
        (a x).eval ((0 : ℝ) : ℂ) * ((N : ℂ) * (v x).eval ((0 : ℝ) : ℂ) ^ (N - 1) *
          (v x).derivative.eval ((0 : ℝ) : ℂ))) / ((v x).eval ((0 : ℝ) : ℂ) ^ N) ^ 2 ∂μ) 0 := by
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
    refine ⟨?_, (SE2.norm_eval_le_of_natDegree (hv x) hu1).trans hsum,
      (SE2.norm_derivative_eval_le (hv x) hu1).trans
        (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hx _) (by positivity))⟩
    have h1 := SE2.norm_eval_sub_eval_zero_le (hv x) hu1
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
    (SE2.aestronglyMeasurable_eval ha (fun j => (hai j).1) _).div₀
      ((SE2.aestronglyMeasurable_eval hv hvm _).pow N)
  have hmeas' : AEStronglyMeasurable (F' 0) μ := by
    have hA := SE2.aestronglyMeasurable_eval ha (fun j => (hai j).1) ((0 : ℝ) : ℂ)
    have hA' := SE2.aestronglyMeasurable_derivative_eval ha (fun j => (hai j).1) ((0 : ℝ) : ℂ)
    have hV := SE2.aestronglyMeasurable_eval hv hvm ((0 : ℝ) : ℂ)
    have hV' := SE2.aestronglyMeasurable_derivative_eval hv hvm ((0 : ℝ) : ℂ)
    exact ((hA'.mul (hV.pow N)).sub (hA.mul ((aestronglyMeasurable_const.mul
      (hV.pow (N - 1))).mul hV'))).div₀ ((hV.pow N).pow 2)
  have hint : Integrable (F 0) μ := by
    refine (hBai.div_const (c ^ N)).mono' (hmeas 0) ?_
    filter_upwards [hv0] with x hx
    simp only [hF, ofReal_zero]
    rw [norm_div, norm_pow]
    have hA := SE2.norm_eval_le_of_natDegree (ha x) (u := 0) (by simp)
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
    have hA := SE2.norm_eval_le_of_natDegree (ha x) hu1
    have hA' := SE2.norm_derivative_eval_le (ha x) hu1
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
    (Eventually.of_forall hmeas) hint hmeas' hb hbi hd).2

/-- **The derivative at `0` of `u ↦ ∫ A(x, u) / V(x, u)ᴺ`** for polynomial families on
`(-1, 1)` with integrable (resp. bounded) node values and `|V(x, 0)| ≥ c > 0`: the integral of the
derivative of the integrand. -/
theorem hasDerivAt_integral_upoly {D E N : ℕ} {A V : ι → ℝ → ℂ} (hA : IsUPoly D A)
    (hAi : ∀ k, Integrable (fun x => A x (node D k)) μ) (hV : IsUPoly E V)
    (hVm : ∀ k, AEStronglyMeasurable (fun x => V x (node E k)) μ) {K c : ℝ}
    (hK : ∀ k, ∀ᵐ x ∂μ, ‖V x (node E k)‖ ≤ K) (hc : 0 < c) (hV0 : ∀ᵐ x ∂μ, c ≤ ‖V x 0‖) :
    HasDerivAt (fun u : ℝ => ∫ x, A x u / V x u ^ N ∂μ)
      (∫ x, deriv (fun u : ℝ => A x u / V x u ^ N) 0 ∂μ) 0 := by
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
  have hd := hasDerivAt_integral_poly_div (N := N) (natDegree_interp_le (f := A))
    (natDegree_interp_le (f := V)) (integrable_interp_coeff hAi) hvm
    (fun j => mul_nonneg (le_max_right _ _) (Finset.sum_nonneg fun _ _ => norm_nonneg _))
    hcoeff hc hv0
  have hIoo : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hloc : ∀ x, (fun u : ℝ => A x u / V x u ^ N) =ᶠ[𝓝 0]
      fun u : ℝ => (interp D A x).eval (u : ℂ) / (interp E V x).eval (u : ℂ) ^ N := fun x => by
    filter_upwards [hIoo] with u hu
    simp only [hA.eq_interp x u hu, hV.eq_interp x u hu]
  have hval : ∫ x, deriv (fun u : ℝ => A x u / V x u ^ N) 0 ∂μ =
      ∫ x, ((interp D A x).derivative.eval ((0 : ℝ) : ℂ) *
          (interp E V x).eval ((0 : ℝ) : ℂ) ^ N - (interp D A x).eval ((0 : ℝ) : ℂ) *
          ((N : ℂ) * (interp E V x).eval ((0 : ℝ) : ℂ) ^ (N - 1) *
            (interp E V x).derivative.eval ((0 : ℝ) : ℂ))) /
          ((interp E V x).eval ((0 : ℝ) : ℂ) ^ N) ^ 2 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hv0] with x hx
    have hne : (interp E V x).eval ((0 : ℝ) : ℂ) ≠ 0 := by
      intro h
      rw [ofReal_zero] at h
      rw [h, norm_zero] at hx
      linarith
    rw [(hloc x).deriv_eq]
    have h1 := Polynomial.hasDerivAt (interp D A x) ((0 : ℝ) : ℂ)
    have h2 := Polynomial.hasDerivAt ((interp E V x) ^ N) ((0 : ℝ) : ℂ)
    have hne' : ((interp E V x) ^ N).eval ((0 : ℝ) : ℂ) ≠ 0 := by
      rw [eval_pow]; exact pow_ne_zero _ hne
    have h3 := (h1.fun_div h2 hne').comp_ofReal
    simp only [eval_pow, derivative_pow, eval_mul, eval_C] at h3
    exact h3.deriv
  rw [hval]
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hIoo] with u hu
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hA.eq_interp x u hu, hV.eq_interp x u hu]

end Core

end QED.GradedProof.WI2

end
