/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5Ker
public import QED.ThreeLoopD.SetDMastersI5Wire
public import QED.ThreeLoopD.SetDMastersI13RemAnalytic

/-!
# Set (d), master `I₅`: the Taylor coefficients of `Rem`, given the bounds on its integrands

The subtraction `QED.ThreeLoopD.i5Asym = α₀ ε⁻¹ N(t, ε)`,
`N(t, ε) = t ^ (-1 - 2ε) / (1 - 2ε) - G t ^ (-1 - 3ε)` (`QED.ThreeLoopD.i5AsymN`), is `0/0` at
`ε = 0`: `N(t, 0) = 0`. Its holomorphic extension is `α₀ · dslope N(t, ·) 0`
(`QED.ThreeLoopD.i5AsymH`, equal to `i5Asym` off `ε = 0` by `QED.ThreeLoopD.i5AsymH_eq`). With it
the two integrands of `QED.ThreeLoopD.i5Rem`,

  `h₁(t, ε) = t ^ (1 - ε) b_ε(t) K_ε(t)` on `(0, 1)`,
  `h₂(t, ε) = h₁(t, ε) - α₀ dslope N` on `(1, ∞)`,

are holomorphic on `‖ε‖ < 1/5` and measurable in `t`. Given integrable bounds `M₁` on `(0, 1)`
and `M₂` on `(1, ∞)` on the circle `‖ε‖ = 1/10`, `QED.ThreeLoopD.hasTruncLaurent_integral_i13Dsl`
gives

  `Rem(ε) = c₀ + c₁ ε + c₂ ε² + ε³ R(ε)`, `R` holomorphic at `0`

(`QED.ThreeLoopD.hasTruncLaurent_i5Rem_coeff_of_bound`), with `cₖ = QED.ThreeLoopD.i5RemCoeff k`
the integrals of the pointwise Taylor coefficients. If moreover `c₀, c₁, c₂` take their target
values, `I₅ C⁻¹` has the LR96 expansion (`QED.ThreeLoopD.hasTruncLaurent_setDMasterI5_of_coeff`).
The bounds are the analytic input still to be proved: on `(1, ∞)` they need the large-`t`
expansion of the kernel, `K_ε(t) = ε⁻¹ (t⁻² / (1 - 2ε) - G t ^ (-2 - ε)) + O(t ^ (-3 + δ))`.

## Main results

* `QED.ThreeLoopD.i5AsymH_eq`, `QED.ThreeLoopD.hasTruncLaurent_i5Rem_coeff_of_bound`.
* `QED.ThreeLoopD.hasTruncLaurent_setDMasterI5_of_coeff`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter Topology

namespace QED.ThreeLoopD

/-- The numerator `t ^ (-1 - 2ε) / (1 - 2ε) - G t ^ (-1 - 3ε)` of `QED.ThreeLoopD.i5Asym`. -/
noncomputable def i5AsymN (t : ℝ) (ε : ℂ) : ℂ :=
  (t : ℂ) ^ (-1 - 2 * ε) / (1 - 2 * ε) - i13G ε * (t : ℂ) ^ (-1 - 3 * ε)

/-- The holomorphic extension of `QED.ThreeLoopD.i5Asym` across `ε = 0`. -/
noncomputable def i5AsymH (ε : ℂ) (t : ℝ) : ℂ := i13Al0 ε * dslope (i5AsymN t) 0 ε

theorem i5AsymN_zero (t : ℝ) : i5AsymN t 0 = 0 := by simp [i5AsymN, i13G]

theorem i5AsymH_eq {ε : ℂ} (h0 : ε ≠ 0) (t : ℝ) : i5AsymH ε t = i5Asym ε t := by
  rw [i5AsymH, dslope_of_ne _ h0, slope_def_field, i5AsymN_zero, i5Asym]
  simp only [sub_zero, i5AsymN]
  ring

theorem differentiableOn_i5AsymH {t : ℝ} (ht : 0 < t) :
    DifferentiableOn ℂ (fun ε => i5AsymH ε t) (ball 0 (1 / 5)) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hN : DifferentiableOn ℂ (i5AsymN t) (ball 0 (1 / 5)) := by
    intro ε hε
    rw [mem_ball, dist_zero_right] at hε
    have hG := differentiableAt_i13G (by linarith : ‖ε‖ < 1 / 2)
    have h12 := (i13_eps_facts (by linarith : ‖ε‖ < 1 / 2)).2.2.2.1
    unfold i5AsymN
    exact ((((by fun_prop : DifferentiableAt ℂ (fun ε : ℂ => -1 - 2 * ε) ε).const_cpow
      (Or.inl ht0)).div (by fun_prop) h12).sub (hG.mul
      ((by fun_prop : DifferentiableAt ℂ (fun ε : ℂ => -1 - 3 * ε) ε).const_cpow
        (Or.inl ht0)))).differentiableWithinAt
  have hD := (differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self
    (by norm_num : (0 : ℝ) < 1 / 5)))).mpr hN
  intro ε hε
  have hε' := hε
  rw [mem_ball, dist_zero_right] at hε'
  exact ((differentiableAt_i13_coeffs (by linarith)).1.differentiableWithinAt).mul (hD ε hε)

/-! ### The integrands -/

/-- The integrand `t ^ (1 - ε) b_ε(t) K_ε(t)` of `Rem` on `(0, 1)`. -/
noncomputable def i5RemInt1 (t : ℝ) (ε : ℂ) : ℂ := (t : ℂ) ^ (1 - ε) * i13Bub ε t * i5Ker ε t

/-- The subtracted integrand of `Rem` on `(1, ∞)`, holomorphic across `ε = 0`. -/
noncomputable def i5RemInt2 (t : ℝ) (ε : ℂ) : ℂ :=
  (t : ℂ) ^ (1 - ε) * i13Bub ε t * i5Ker ε t - i5AsymH ε t

/-- **The Taylor coefficients of `Rem`**, as integrals of the pointwise Taylor coefficients. -/
noncomputable def i5RemCoeff (k : ℕ) : ℂ :=
  (∫ t in Ioo (0 : ℝ) 1, i13Dsl (i5RemInt1 t) k 0) +
    ∫ t in Ioi (1 : ℝ), i13Dsl (i5RemInt2 t) k 0

theorem differentiableOn_i5RemInt1 {t : ℝ} (ht : 0 < t) :
    DifferentiableOn ℂ (i5RemInt1 t) (ball 0 (1 / 5)) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  intro ε hε
  rw [mem_ball, dist_zero_right] at hε
  unfold i5RemInt1
  exact (((Differentiable.const_cpow (by fun_prop) (Or.inl ht0)).differentiableAt.mul
    ((differentiable_i13Bub ht.le).differentiableAt)).mul
    (differentiableAt_i5Ker (by linarith) ht)).differentiableWithinAt

theorem differentiableOn_i5RemInt2 {t : ℝ} (ht : 0 < t) :
    DifferentiableOn ℂ (i5RemInt2 t) (ball 0 (1 / 5)) :=
  (differentiableOn_i5RemInt1 ht).sub (differentiableOn_i5AsymH ht)

theorem measurable_i5RemInt1 (ε : ℂ) : Measurable fun t => i5RemInt1 t ε := by
  unfold i5RemInt1
  exact ((measurable_ofReal.pow_const _).mul (measurable_i13Bub ε)).mul (measurable_i5Ker ε)

theorem measurable_i5RemInt2 {ε : ℂ} (h0 : ε ≠ 0) : Measurable fun t => i5RemInt2 t ε := by
  have h1 := measurable_i5RemInt1 ε
  unfold i5RemInt1 at h1
  unfold i5RemInt2
  simp_rw [i5AsymH_eq h0]
  unfold i5Asym
  have hc : ∀ c : ℂ, Measurable fun t : ℝ => (t : ℂ) ^ c := fun c =>
    measurable_ofReal.pow_const c
  exact h1.sub (measurable_const.mul (((hc _).div_const _).sub (measurable_const.mul (hc _))))

/-- Measurability at `ε = 0` from measurability off `0` and continuity in `ε`. -/
theorem i5_aesm_of_ne {α : Type*} [MeasurableSpace α] {μ : Measure α} {h : α → ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hd : ∀ᵐ t ∂μ, DifferentiableOn ℂ (h t) (ball 0 R))
    (hm : ∀ ε ∈ ball (0 : ℂ) R, ε ≠ 0 → AEStronglyMeasurable (fun t => h t ε) μ) :
    ∀ ε ∈ ball (0 : ℂ) R, AEStronglyMeasurable (fun t => h t ε) μ := by
  intro ε hε
  by_cases h0 : ε = 0
  swap
  · exact hm ε hε h0
  subst h0
  set s : ℕ → ℂ := fun n => ((R / 2 * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ) with hs
  have hpos : ∀ n : ℕ, 0 < R / 2 * (1 / ((n : ℝ) + 1)) := fun n => by positivity
  have hsb : ∀ n, s n ∈ ball (0 : ℂ) R := fun n => by
    rw [mem_ball, dist_zero_right, hs, norm_real, Real.norm_eq_abs, abs_of_pos (hpos n)]
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    nlinarith
  have hs0 : ∀ n, s n ≠ 0 := fun n => ofReal_ne_zero.mpr (hpos n).ne'
  have hlim : Tendsto s atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (R / 2))
    rw [mul_zero] at this
    have h2 := (continuous_ofReal.tendsto 0).comp this
    rw [ofReal_zero] at h2
    exact h2
  refine aestronglyMeasurable_of_tendsto_ae atTop (fun n => hm (s n) (hsb n) (hs0 n)) ?_
  filter_upwards [hd] with t ht
  exact ((ht.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hR))).tendsto).comp
    hlim

/-! ### The expansion -/

/-- **`Rem` to order `ε²`, given integrable bounds on the circle `‖ε‖ = 1/10`**:
`Rem(ε) = c₀ + c₁ ε + c₂ ε² + ε³ R(ε)`, `R` holomorphic at `0`, `cₖ = i5RemCoeff k`. -/
theorem hasTruncLaurent_i5Rem_coeff_of_bound {M₁ M₂ : ℝ → ℝ}
    (hM₁ : IntegrableOn M₁ (Ioo 0 1)) (hM₂ : IntegrableOn M₂ (Ioi 1))
    (hb₁ : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ ε : ℂ, ‖ε‖ = 1 / 10 →
      ‖(t : ℂ) ^ (1 - ε) * i13Bub ε t * i5Ker ε t‖ ≤ M₁ t)
    (hb₂ : ∀ t ∈ Ioi (1 : ℝ), ∀ ε : ℂ, ‖ε‖ = 1 / 10 →
      ‖(t : ℂ) ^ (1 - ε) * i13Bub ε t * i5Ker ε t - i5Asym ε t‖ ≤ M₂ t) :
    HasTruncLaurent i5Rem (fun ε => ∑ k ∈ Finset.range 3, i5RemCoeff k * ε ^ k) 3 := by
  have hd1 : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      DifferentiableOn ℂ (i5RemInt1 t) (ball 0 (1 / 5)) :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => differentiableOn_i5RemInt1 ht.1
  have hd2 : ∀ᵐ t ∂(volume.restrict (Ioi (1 : ℝ))),
      DifferentiableOn ℂ (i5RemInt2 t) (ball 0 (1 / 5)) :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      differentiableOn_i5RemInt2 (zero_lt_one.trans ht)
  have H1 := hasTruncLaurent_integral_i13Dsl (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (h := i5RemInt1) (R := 1 / 5) (ρ := 1 / 10) (M := M₁) (by norm_num) (by norm_num) hM₁ hd1
    (fun ε _ => (measurable_i5RemInt1 ε).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht ε hε => hb₁ t ht ε hε) 3
  have H2 := hasTruncLaurent_integral_i13Dsl (μ := volume.restrict (Ioi (1 : ℝ)))
    (h := i5RemInt2) (R := 1 / 5) (ρ := 1 / 10) (M := M₂) (by norm_num) (by norm_num) hM₂ hd2
    (i5_aesm_of_ne (by norm_num) hd2 fun ε _ h0 =>
      (measurable_i5RemInt2 h0).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ε hε => by
      have h0 : ε ≠ 0 := fun h => by rw [h, norm_zero] at hε; norm_num at hε
      rw [i5RemInt2, i5AsymH_eq h0]
      exact hb₂ t ht ε hε) 3
  obtain ⟨R1, hR1, e1⟩ := H1
  obtain ⟨R2, hR2, e2⟩ := H2
  refine ⟨fun ε => R1 ε + R2 ε, hR1.add hR2, ?_⟩
  filter_upwards [e1, e2, self_mem_nhdsWithin] with ε h1 h2 h0
  have h0 : ε ≠ 0 := h0
  have hI2 : ∫ t in Ioi (1 : ℝ), ((t : ℂ) ^ (1 - ε) * i13Bub ε t * i5Ker ε t - i5Asym ε t) =
      ∫ t in Ioi (1 : ℝ), i5RemInt2 t ε := by
    simp only [i5RemInt2, i5AsymH_eq h0]
  rw [show i5Rem ε = (∫ t in Ioo (0 : ℝ) 1, i5RemInt1 t ε) +
    ∫ t in Ioi (1 : ℝ), ((t : ℂ) ^ (1 - ε) * i13Bub ε t * i5Ker ε t - i5Asym ε t) from rfl,
    hI2, h1, h2]
  unfold i5RemCoeff
  simp only [add_mul, Finset.sum_add_distrib]
  ring

/-! ### From the coefficients to the master -/

section Coeff

open Real QED.Polylog

theorem i5RemLaurent_eq_sum {c : ℕ → ℂ} (h0 : c 0 = -1 / 3 * (π : ℂ) ^ 2 + 3)
    (h1 : c 1 = -4 / 45 * (π : ℂ) ^ 4 - 5 / 3 * (π : ℂ) ^ 2 - 5 * (zeta3 : ℂ) + 25)
    (h2 : c 2 = -29 / 40 * (π : ℂ) ^ 4 + 25 / 6 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
      + 4 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) - 37 / 6 * (π : ℂ) ^ 2 - 36 * (zeta3 : ℂ)
      - 49 / 2 * (zeta5 : ℂ) + 143)
    (ε : ℂ) : ∑ k ∈ Finset.range 3, c k * ε ^ k = i5RemLaurent ε := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, i5RemLaurent]
  ring

/-- **The master from the bounds and the coefficients**: given integrable bounds on the two
integrands of `Rem` on the circle `‖ε‖ = 1/10`, and the target values of `c₀, c₁, c₂`, `I₅ C⁻¹`
has the LR96 expansion through `ε²`. -/
theorem hasTruncLaurent_setDMasterI5_of_coeff {M₁ M₂ : ℝ → ℝ}
    (hM₁ : IntegrableOn M₁ (Ioo 0 1)) (hM₂ : IntegrableOn M₂ (Ioi 1))
    (hb₁ : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ ε : ℂ, ‖ε‖ = 1 / 10 →
      ‖(t : ℂ) ^ (1 - ε) * i13Bub ε t * i5Ker ε t‖ ≤ M₁ t)
    (hb₂ : ∀ t ∈ Ioi (1 : ℝ), ∀ ε : ℂ, ‖ε‖ = 1 / 10 →
      ‖(t : ℂ) ^ (1 - ε) * i13Bub ε t * i5Ker ε t - i5Asym ε t‖ ≤ M₂ t)
    (h0 : i5RemCoeff 0 = -1 / 3 * (π : ℂ) ^ 2 + 3)
    (h1 : i5RemCoeff 1 = -4 / 45 * (π : ℂ) ^ 4 - 5 / 3 * (π : ℂ) ^ 2 - 5 * (zeta3 : ℂ) + 25)
    (h2 : i5RemCoeff 2 = -29 / 40 * (π : ℂ) ^ 4 + 25 / 6 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
      + 4 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) - 37 / 6 * (π : ℂ) ^ 2 - 36 * (zeta3 : ℂ)
      - 49 / 2 * (zeta5 : ℂ) + 143) :
    HasTruncLaurent setDMasterI5 setDLaurentI5 2 := by
  refine hasTruncLaurent_setDMasterI5_of_Rem ?_
  have h := hasTruncLaurent_i5Rem_coeff_of_bound hM₁ hM₂ hb₁ hb₂
  have e : (fun ε => ∑ k ∈ Finset.range 3, i5RemCoeff k * ε ^ k) = i5RemLaurent :=
    funext (i5RemLaurent_eq_sum h0 h1 h2)
  rwa [e] at h

end Coeff

end QED.ThreeLoopD
