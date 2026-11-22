/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroLimitCore

/-!
# A quantitative form of the second-order limit

Helper level for set (c) (gap 4 of stage L1: the `q → 0` bound uniform in the masses, for a
dispersion integral in a mass). `QED.TwoLoop.PauliZeroLimit.tendsto_even_div_sq` gives the limit
of the even quotient `(∫ f(u) + ∫ f(-u))/(2u²)` for `f(u) = A(·, u)/((1 - u²)ᵃ V(·, u)ᴺ)`. This file
bounds the quotient itself, for `0 < |u| ≤ 1/2`, and the limit, by the values of `A` at the
interpolation nodes:

* `lagConst D`: the sum of the absolute values of the coefficients of the Lagrange basis at the
  nodes `k/(D+1)` (a number depending on `D` only);
* `sum_norm_interp_coeff_le`: `∑ⱼ ‖aⱼ(x)‖ ≤ lagConst D · ∑ₖ ‖A(x, node k)‖`;
* **`norm_evenQuot_le`**: `‖(∫ f(u) + ∫ f(-u))/(2u²)‖ ≤ ∫ ∑ⱼ ‖aⱼ‖ / ((3/4)ᵃ cᴺ)`;
* **`norm_evenQuot_le_nodes`**: `≤ lagConst D · ∑ₖ ∫ ‖A(·, node k)‖ / ((3/4)ᵃ cᴺ)`;
* `norm_evenLimit_le_nodes`: the same bound (with `cᴺ`) for the limit `∫ a₂ / V(·, 0)ᴺ`.

So a bound `∫ ‖A(·, node k)‖ ≤ C(M)` polynomial in the masses (from the numerator, with `V ≥ c`
uniform) gives the `q → 0` quotients of a family of units a bound polynomial in the masses,
uniformly in `u`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Polynomial

namespace QED.ChainProof.SetCUnitM

open QED.TwoLoop.PauliZeroLimit

/-- The sum of the absolute values of the coefficients of the Lagrange basis at the nodes. -/
noncomputable def lagConst (D : ℕ) : ℝ :=
  ∑ k : Fin (D + 1), ∑ j ∈ Finset.range (D + 1),
    ‖(Lagrange.basis Finset.univ (fun k : Fin (D + 1) => ((node D k : ℝ) : ℂ)) k).coeff j‖

theorem lagConst_nonneg (D : ℕ) : 0 ≤ lagConst D :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

section Bound

variable {ι : Type*} {D : ℕ} {A : ι → ℝ → ℂ}

/-- **The coefficients of the interpolant are bounded by the node values.** -/
theorem sum_norm_interp_coeff_le (x : ι) :
    ∑ j ∈ Finset.range (D + 1), ‖(interp D A x).coeff j‖ ≤
      lagConst D * ∑ k : Fin (D + 1), ‖A x (node D k)‖ := by
  set b : Fin (D + 1) → ℕ → ℝ := fun k j =>
    ‖(Lagrange.basis Finset.univ (fun k : Fin (D + 1) => ((node D k : ℝ) : ℂ)) k).coeff j‖
  have h1 : ∀ j, ‖(interp D A x).coeff j‖ ≤ ∑ k, ‖A x (node D k)‖ * b k j := fun j => by
    rw [interp_coeff]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul]
  have hb0 : ∀ k j, 0 ≤ b k j := fun _ _ => norm_nonneg _
  calc ∑ j ∈ Finset.range (D + 1), ‖(interp D A x).coeff j‖
      ≤ ∑ j ∈ Finset.range (D + 1), ∑ k, ‖A x (node D k)‖ * b k j :=
        Finset.sum_le_sum fun j _ => h1 j
    _ = ∑ k, ‖A x (node D k)‖ * ∑ j ∈ Finset.range (D + 1), b k j := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ k, ‖A x (node D k)‖ * lagConst D := by
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun k => ∑ j ∈ Finset.range (D + 1), b k j)
          (fun k _ => Finset.sum_nonneg fun j _ => hb0 k j) (Finset.mem_univ k)
    _ = lagConst D * ∑ k, ‖A x (node D k)‖ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _

variable [MeasurableSpace ι] {μ : Measure ι} {a N : ℕ} {V : ι → ℝ → ℝ} {c : ℝ}
  {f : ℝ → ι → ℂ}

/-- **The even quotient is bounded**, for `0 < |u| ≤ 1/2`, by `∫ ∑ⱼ ‖aⱼ‖ / ((3/4)ᵃ cᴺ)`, under
the hypotheses of `tendsto_even_div_sq`. -/
theorem norm_evenQuot_le (hA : IsUPoly D A)
    (hAi : ∀ k, Integrable (fun x => A x (node D k)) μ) (hA0 : ∀ᵐ x ∂μ, A x 0 = 0)
    (hc : 0 < c) (hV : ∀ᵐ x ∂μ, ∀ u ∈ Ioo (-1 : ℝ) 1, c ≤ V x u)
    (hVeven : ∀ᵐ x ∂μ, ∀ u, V x (-u) = V x u) (hVcont : ∀ᵐ x ∂μ, ContinuousAt (V x) 0)
    (hVmeas : ∀ u, AEStronglyMeasurable (fun x => V x u) μ)
    (hf : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ᵐ x ∂μ, f u x = A x u / (wt u ^ a * (V x u : ℂ) ^ N))
    {u : ℝ} (hu0 : u ≠ 0) (hu : |u| ≤ 1 / 2) :
    ‖((∫ x, f u x ∂μ) + ∫ x, f (-u) x ∂μ) / (2 * (u : ℂ) ^ 2)‖ ≤
      (∫ x, ∑ j ∈ Finset.range (D + 1), ‖(interp D A x).coeff j‖ ∂μ) /
        ((3 / 4 : ℝ) ^ a * c ^ N) := by
  have hfi := (tendsto_even_div_sq hA hAi hA0 hc hV hVeven hVcont hVmeas hf).1
  have hcf : ∀ j, Integrable (fun x => (interp D A x).coeff j) μ := integrable_interp_coeff hAi
  set K : ι → ℝ := fun x => ∑ j ∈ Finset.range (D + 1), ‖(interp D A x).coeff j‖ with hK
  have hKi : Integrable K μ := integrable_finsetSum _ fun j _ => (hcf j).norm
  have hK0 : ∀ x, 0 ≤ K x := fun x => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hu1 : u ∈ Ioo (-1 : ℝ) 1 := by
    rw [abs_le] at hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hu' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu1.2], by linarith [hu1.1]⟩
  have hAeq : ∀ x, ∀ v ∈ Ioo (-1 : ℝ) 1,
      A x v = ∑ j ∈ Finset.range (D + 1), (interp D A x).coeff j * (v : ℂ) ^ j := fun x v hv => by
    rw [hA.eq_interp x v hv, eval_interp_eq_sum]
  set B : ι → ℂ := fun x =>
    ∑ j ∈ Finset.range (D + 1), (interp D A x).coeff j * evenCoeff j u with hB
  have h0 : ∀ᵐ x ∂μ, (interp D A x).coeff 0 = 0 := by
    filter_upwards [hA0] with x hx
    have := hA.eq_interp x 0 ⟨by norm_num, by norm_num⟩
    rw [hx, ofReal_zero, ← coeff_zero_eq_eval_zero] at this
    exact this.symm
  have hsym : ((∫ x, f u x ∂μ) + ∫ x, f (-u) x ∂μ) / (2 * (u : ℂ) ^ 2) =
      ∫ x, B x / (wt u ^ a * (V x u : ℂ) ^ N) ∂μ := by
    rw [← integral_add (hfi u hu1) (hfi (-u) hu'), div_eq_mul_inv, mul_comm,
      ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hf u hu1, hf (-u) hu', hVeven, h0] with x hx hx' hev hx0
    rw [hx, hx', hev, wt_neg]
    have hsum : A x u + A x (-u) = 2 * (u : ℂ) ^ 2 * B x := by
      rw [hAeq x u hu1, hAeq x (-u) hu', ← Finset.sum_add_distrib]
      simp only [hB, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_add, pow_add_neg_pow]
      split_ifs with hj
      · subst hj
        rw [hx0]
        ring
      · ring
    have hu2 : (u : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (ofReal_ne_zero.mpr hu0)
    have h2u : (2 * (u : ℂ) ^ 2) ≠ 0 := mul_ne_zero two_ne_zero hu2
    rw [← add_div, hsum, mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ h2u, one_mul]
  rw [hsym, ← integral_div]
  refine norm_integral_le_of_norm_le (hKi.div_const _) ?_
  filter_upwards [hV] with x hx
  have hcx := hx u hu1
  have hBn : ‖B x‖ ≤ K x := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_evenCoeff_le j (hu.trans (by norm_num)))
  have hw := norm_wt_ge hu
  rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hc.trans_le hcx)]
  exact div_le_div₀ (hK0 x) hBn (by positivity)
    (mul_le_mul (pow_le_pow_left₀ (by norm_num) hw a) (pow_le_pow_left₀ hc.le hcx N)
      (by positivity) (by positivity))

/-- **The even quotient is bounded by the node values**: for `0 < |u| ≤ 1/2`,
`‖(∫ f(u) + ∫ f(-u))/(2u²)‖ ≤ lagConst D · ∑ₖ ∫ ‖A(·, node k)‖ / ((3/4)ᵃ cᴺ)`. -/
theorem norm_evenQuot_le_nodes (hA : IsUPoly D A)
    (hAi : ∀ k, Integrable (fun x => A x (node D k)) μ) (hA0 : ∀ᵐ x ∂μ, A x 0 = 0)
    (hc : 0 < c) (hV : ∀ᵐ x ∂μ, ∀ u ∈ Ioo (-1 : ℝ) 1, c ≤ V x u)
    (hVeven : ∀ᵐ x ∂μ, ∀ u, V x (-u) = V x u) (hVcont : ∀ᵐ x ∂μ, ContinuousAt (V x) 0)
    (hVmeas : ∀ u, AEStronglyMeasurable (fun x => V x u) μ)
    (hf : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ᵐ x ∂μ, f u x = A x u / (wt u ^ a * (V x u : ℂ) ^ N))
    {u : ℝ} (hu0 : u ≠ 0) (hu : |u| ≤ 1 / 2) :
    ‖((∫ x, f u x ∂μ) + ∫ x, f (-u) x ∂μ) / (2 * (u : ℂ) ^ 2)‖ ≤
      lagConst D * (∑ k : Fin (D + 1), ∫ x, ‖A x (node D k)‖ ∂μ) /
        ((3 / 4 : ℝ) ^ a * c ^ N) := by
  refine (norm_evenQuot_le hA hAi hA0 hc hV hVeven hVcont hVmeas hf hu0 hu).trans ?_
  have hden : 0 < (3 / 4 : ℝ) ^ a * c ^ N := by positivity
  refine div_le_div_of_nonneg_right ?_ hden.le
  have hcf : ∀ j, Integrable (fun x => (interp D A x).coeff j) μ := integrable_interp_coeff hAi
  rw [← integral_finsetSum _ fun k _ => (hAi k).norm, ← integral_const_mul]
  exact integral_mono (integrable_finsetSum _ fun j _ => (hcf j).norm)
    ((integrable_finsetSum _ fun k _ => (hAi k).norm).const_mul _)
    fun x => sum_norm_interp_coeff_le x

/-- **The limit is bounded by the node values**: `‖∫ a₂ / V(·, 0)ᴺ‖ ≤ lagConst D ·
∑ₖ ∫ ‖A(·, node k)‖ / cᴺ`. -/
theorem norm_evenLimit_le_nodes (hAi : ∀ k, Integrable (fun x => A x (node D k)) μ) (hc : 0 < c)
    (hV0 : ∀ᵐ x ∂μ, c ≤ V x 0) :
    ‖∫ x, (interp D A x).coeff 2 / (V x 0 : ℂ) ^ N ∂μ‖ ≤
      lagConst D * (∑ k : Fin (D + 1), ∫ x, ‖A x (node D k)‖ ∂μ) / c ^ N := by
  have hcf : ∀ j, Integrable (fun x => (interp D A x).coeff j) μ := integrable_interp_coeff hAi
  have hc2 : ∀ x, ‖(interp D A x).coeff 2‖ ≤ lagConst D * ∑ k : Fin (D + 1), ‖A x (node D k)‖ :=
    fun x => by
      refine le_trans ?_ (sum_norm_interp_coeff_le x)
      by_cases h2 : 2 < D + 1
      · exact Finset.single_le_sum (f := fun j => ‖(interp D A x).coeff j‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr h2)
      · rw [coeff_eq_zero_of_natDegree_lt ((natDegree_interp_le x).trans_lt (by omega)),
          norm_zero]
        exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hI : Integrable (fun x => lagConst D * ∑ k : Fin (D + 1), ‖A x (node D k)‖) μ :=
    (integrable_finsetSum _ fun k _ => (hAi k).norm).const_mul _
  have hcN : 0 < c ^ N := pow_pos hc N
  rw [← integral_finsetSum _ fun k _ => (hAi k).norm, ← integral_const_mul, ← integral_div]
  refine norm_integral_le_of_norm_le (hI.div_const _) ?_
  filter_upwards [hV0] with x hx
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hc.trans_le hx)]
  exact div_le_div₀ (mul_nonneg (lagConst_nonneg D) (Finset.sum_nonneg fun _ _ => norm_nonneg _))
    (hc2 x) hcN (pow_le_pow_left₀ hc.le hx N)

end Bound

end QED.ChainProof.SetCUnitM

end
