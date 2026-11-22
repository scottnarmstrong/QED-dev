/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5Tri

/-!
# Set (d), master `I₅`: the kernel is holomorphic in `ε` and measurable in `t`

On shell `w = t - 2 i √t z` has `re w = t` and `‖w‖ ≥ t` (`QED.ThreeLoopD.re_i5W`,
`QED.ThreeLoopD.le_norm_i5W`). By `QED.ThreeLoopD.norm_i5Tri_le` the integrand
`(1 - z²) ^ (1/2 - ε) i5Tri ε t w / w` of `QED.ThreeLoopD.i5Ker` is bounded by
`e ^ (π/8) ∫ i5TriDom t / t` uniformly in `z ∈ (-1, 1)` and `‖ε‖ ≤ 1/4`
(`QED.ThreeLoopD.norm_i5KerF_le`). So `ε ↦ i5Ker ε t` is holomorphic on `‖ε‖ < 1/4`
(`QED.ThreeLoopD.differentiableAt_i5Ker`); and `t ↦ i5Ker ε t` is measurable
(`QED.ThreeLoopD.measurable_i5Ker`), the nested integrals being integrals of jointly measurable
functions.

## Main results

* `QED.ThreeLoopD.differentiableAt_i5Ker`, `QED.ThreeLoopD.measurable_i5Ker`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric

namespace QED.ThreeLoopD

/-- The integrand of `QED.ThreeLoopD.i5Ker`. -/
noncomputable def i5KerF (ε : ℂ) (t z : ℝ) : ℂ :=
  ((1 - z ^ 2 : ℝ) : ℂ) ^ (1 / 2 - ε) * i5Tri ε t (i5W t z) / i5W t z

theorem i5Ker_eq (ε : ℂ) (t : ℝ) :
    i5Ker ε t = i5Nrm ε * ∫ z in Ioo (-1 : ℝ) 1, i5KerF ε t z := rfl

theorem re_i5W (t z : ℝ) : (i5W t z).re = t := by simp [i5W]

theorem le_norm_i5W (t z : ℝ) : t ≤ ‖i5W t z‖ := by
  have := re_le_norm (i5W t z)
  rwa [re_i5W] at this

theorem i5W_ne_zero {t : ℝ} (ht : 0 < t) (z : ℝ) : i5W t z ≠ 0 := fun h => by
  have := re_i5W t z
  rw [h, zero_re] at this
  linarith

/-- The uniform bound on the triangle, `e ^ (π/8) ∫ i5TriDom t`. -/
noncomputable def i5TriB (t : ℝ) : ℝ :=
  Real.exp (Real.pi / 8) * ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5TriDom t q

theorem i5_one_sub_sq_pos {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) : 0 < 1 - z ^ 2 := by
  nlinarith [hz.1, hz.2]

theorem norm_i5Wt_le {ε : ℂ} (hε : ε.re ≤ 1 / 2) {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) :
    ‖((1 - z ^ 2 : ℝ) : ℂ) ^ (1 / 2 - ε)‖ ≤ 1 := by
  rw [norm_cpow_eq_rpow_re_of_pos (i5_one_sub_sq_pos hz)]
  refine Real.rpow_le_one (i5_one_sub_sq_pos hz).le (by nlinarith [hz.1]) ?_
  rw [sub_re]; norm_num; linarith

theorem norm_i5KerF_le {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 4) {t : ℝ} (ht : 0 < t) {z : ℝ}
    (hz : z ∈ Ioo (-1 : ℝ) 1) : ‖i5KerF ε t z‖ ≤ i5TriB t / t := by
  unfold i5KerF
  rw [norm_div, norm_mul]
  have h1 := norm_i5Wt_le (ε := ε) (by linarith [re_le_norm ε]) hz
  have h2 := norm_i5Tri_le hε ht (re_i5W t z)
  have hB : 0 ≤ i5TriB t := (norm_nonneg _).trans h2
  calc ‖((1 - z ^ 2 : ℝ) : ℂ) ^ (1 / 2 - ε)‖ * ‖i5Tri ε t (i5W t z)‖ / ‖i5W t z‖ ≤
        1 * i5TriB t / t := by
        gcongr
        · exact h2
        · exact le_norm_i5W t z
    _ = i5TriB t / t := by ring

/-! ### Measurability -/

theorem measurable_i5TriF_uncurry (ε : ℂ) :
    Measurable fun p : (ℝ × ℝ) × (ℝ × ℝ) => i5TriF ε p.1.1 (i5W p.1.1 p.1.2) p.2 := by
  unfold i5TriF i5X i5W
  fun_prop

/-- `(t, z) ↦ i5Tri ε t (i5W t z)` is measurable. -/
theorem measurable_i5Tri_W (ε : ℂ) :
    Measurable fun p : ℝ × ℝ => i5Tri ε p.1 (i5W p.1 p.2) :=
  ((measurable_i5TriF_uncurry ε).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))).measurable

theorem measurable_i5KerF_uncurry (ε : ℂ) :
    Measurable fun p : ℝ × ℝ => i5KerF ε p.1 p.2 := by
  have h := measurable_i5Tri_W ε
  unfold i5KerF
  refine Measurable.div ?_ (by unfold i5W; fun_prop)
  exact (by fun_prop : Measurable fun p : ℝ × ℝ => ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ (1 / 2 - ε)).mul h

theorem measurable_i5Ker (ε : ℂ) : Measurable fun t => i5Ker ε t := by
  unfold i5Ker
  exact measurable_const.mul ((measurable_i5KerF_uncurry ε).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioo (-1 : ℝ) 1))).measurable

/-! ### Holomorphy -/

theorem differentiableAt_i5Nrm {ε : ℂ} (hε : ‖ε‖ < 1 / 2) : DifferentiableAt ℂ i5Nrm ε := by
  obtain ⟨d2, d3, -, n3, n1⟩ := i8_Gamma_facts hε
  unfold i5Nrm
  exact d2.div (d3.const_mul _) (mul_ne_zero n1 n3)

/-- **The kernel is holomorphic** in `ε` on `‖ε‖ < 1/4`. -/
theorem differentiableAt_i5Ker {ε₀ : ℂ} (h0 : ‖ε₀‖ < 1 / 4) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℂ (fun ε => i5Ker ε t) ε₀ := by
  have hsub : ball ε₀ (1 / 4 - ‖ε₀‖) ⊆ ball 0 (1 / 4) := fun ε hε => by
    rw [mem_ball, dist_eq_norm] at hε
    rw [mem_ball, dist_zero_right]
    have := norm_le_norm_add_norm_sub' ε ε₀
    linarith
  have hI : DifferentiableAt ℂ (fun ε => ∫ z in Ioo (-1 : ℝ) 1, i5KerF ε t z) ε₀ := by
    refine QED.DimReg.differentiableAt_integral_of_holomorphic (R := 1 / 4 - ‖ε₀‖)
      (by linarith) (b := fun _ => i5TriB t / t) (integrable_const _)
      (fun ε _ => ((measurable_i5KerF_uncurry ε).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable) ?_ ?_
    · refine ae_restrict_of_forall_mem measurableSet_Ioo fun z hz ε hε => ?_
      have := hsub hε
      rw [mem_ball, dist_zero_right] at this
      exact norm_i5KerF_le this.le ht hz
    · refine ae_restrict_of_forall_mem measurableSet_Ioo fun z hz => ?_
      have hT := (differentiableOn_i5Tri ht (re_i5W t z)).mono hsub
      have hw := i5W_ne_zero ht z
      intro ε hε
      have hTa := (hT ε hε).differentiableAt (isOpen_ball.mem_nhds hε)
      unfold i5KerF
      exact (((DifferentiableAt.const_cpow (by fun_prop)
        (Or.inl (ofReal_ne_zero.mpr (i5_one_sub_sq_pos hz).ne'))).mul hTa).div_const
          _).differentiableWithinAt
  exact (differentiableAt_i5Nrm (by linarith)).mul hI

end QED.ThreeLoopD
