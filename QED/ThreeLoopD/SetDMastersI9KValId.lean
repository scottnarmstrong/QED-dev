/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9KValM

/-!
# Set (d), master `I₉`: `K` in terms of `M` and `B`

For `0 < ε < 1/3` (`s = 1 - 3ε`, `c = x (1 - x)`, `P = c (1 - w)² + w`) and fixed `x`, the
function

  `G(w) = c ^ (2ε - 1) w ^ (2ε) (P ^ s - w ^ s) - c ^ (-ε) w ^ (2ε) (1 + s w² / (2 + 2ε))`

satisfies `G(0) = 0`, `G(1) = -c ^ (-ε) (3 - ε) / (2 + 2ε)` and

  `G'(w) = (1 - ε) c ^ (2ε - 1) w ^ (2ε - 1) (P ^ s - w ^ s - c ^ s)
    - s (1 - w²) w ^ (2ε - 1) (c ^ (2ε) P ^ (-3ε) - c ^ (-ε))`

(this uses `w P' + c (1 - w²) = P`). Integrating over the square (Fubini) gives, for real
`0 < ε < 1/20`, `(1 - ε) K(ε) - s M(ε) = -(3 - ε) B(ε) / (2 + 2ε)`, with `M`, `B` of
`QED.ThreeLoopD.SetDMastersI9KValM`. All three functions are analytic on `‖ε‖ < 1/40`, so the
identity holds there, and comparing Taylor coefficients gives

  `2 Kₖ - 2 Kₖ₋₂ = 2 Mₖ - 4 Mₖ₋₁ - 6 Mₖ₋₂ - 3 Bₖ + Bₖ₋₁`  (`k ≤ 3`).

## Main results

* `QED.ThreeLoopD.i9_fiber_identity`: the identity for fixed `x`.
* `QED.ThreeLoopD.i9KMB_eq_zero`: `(1 - ε)(2 + 2ε) K - (2 + 2ε)(1 - 3ε) M + (3 - ε) B = 0` on
  `‖ε‖ < 1/40`.
* `QED.ThreeLoopD.i9KCoeff_rel`: the relations between the coefficients through `ε³`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric

namespace QED.ThreeLoopD

/-! ### The real integrands -/

/-- The integrand of `K` at real `ε`: `c ^ (2ε - 1) w ^ (2ε - 1) (P ^ s - w ^ s - c ^ s)`. -/
noncomputable def i9KReal (e x w : ℝ) : ℝ :=
  (x * (1 - x)) ^ (2 * e - 1) * w ^ (2 * e - 1) *
    (i9Poly x w 1 ^ (1 - 3 * e) - w ^ (1 - 3 * e) - (x * (1 - x)) ^ (1 - 3 * e))

/-- The integrand of `M` at real `ε`:
`(1 - w²) / w (w ^ (2ε) c ^ (2ε) P ^ (-3ε) - w ^ (2ε) c ^ (-ε))`. -/
noncomputable def i9MReal (e x w : ℝ) : ℝ :=
  (1 - w ^ 2) / w * (w ^ (2 * e) * (x * (1 - x)) ^ (2 * e) * i9Poly x w 1 ^ (-3 * e) -
    w ^ (2 * e) * (x * (1 - x)) ^ (-e))

theorem i9K_integrand_ofReal {e x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    i9Wt (e : ℂ) x w * i9Psi (e : ℂ) x w 1 = (i9KReal e x w : ℂ) := by
  have hc := i9_c_pos hx
  have hP := i9Poly_one_pos hx hw
  have key : ∀ r : ℝ, 0 ≤ r → ∀ y : ℝ, (r : ℂ) ^ (y : ℂ) = ((r ^ y : ℝ) : ℂ) :=
    fun r hr y => (Complex.ofReal_cpow hr y).symm
  have e1 : (2 * (e : ℂ) - 1) = ((2 * e - 1 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (1 - 3 * (e : ℂ)) = ((1 - 3 * e : ℝ) : ℂ) := by push_cast; ring
  unfold i9Wt i9Psi i9KReal
  rw [e1, e2, key _ hc.le, key _ hw.1.le, key _ hP.le, key _ (by simpa using hw.1.le),
    key _ hc.le, mul_one]
  push_cast
  ring

theorem i9MD_ofReal {e x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    i9MD 0 (e : ℂ) (x, w) = (i9MReal e x w : ℂ) := by
  have hc := i9_c_pos hx
  have hP := i9Poly_one_pos hx hw
  have hw0 := hw.1
  unfold i9MD i9KExp
  simp only [pow_zero, one_mul]
  rw [show ((i9MA w : ℝ) : ℂ) + (e : ℂ) * (i9KB1 x w : ℂ) = ((i9MA w + e * i9KB1 x w : ℝ) : ℂ)
    by push_cast; ring,
    show ((i9MA w : ℝ) : ℂ) + (e : ℂ) * (i9KB3 x w : ℂ) = ((i9MA w + e * i9KB3 x w : ℝ) : ℂ)
    by push_cast; ring, ← Complex.ofReal_exp, ← Complex.ofReal_exp, ← Complex.ofReal_sub]
  congr 1
  unfold i9MReal
  rw [Real.exp_add, Real.exp_add, exp_i9MA hw, ← mul_sub]
  congr 1
  rw [Real.rpow_def_of_pos hw0, Real.rpow_def_of_pos hc, Real.rpow_def_of_pos hP,
    Real.rpow_def_of_pos hc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  unfold i9KB1 i9KB3
  congr 2 <;> ring

theorem i9BD_ofReal (e x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    i9BD 0 (e : ℂ) x = (((x * (1 - x)) ^ (-e) : ℝ) : ℂ) := by
  have hc := i9_c_pos hx
  unfold i9BD i9KExp
  rw [pow_zero, one_mul, Real.rpow_def_of_pos hc, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-! ### The identity for fixed `x` -/

/-- **The fibre identity**: for `0 < ε < 1/3` and `x ∈ (0, 1)`,
`∫₀¹ ((1 - ε) k - s m) dw = -c ^ (-ε) (3 - ε) / (2 + 2ε)` (`k`, `m` the integrands of `K`, `M`). -/
theorem i9_fiber_identity {e : ℝ} (he0 : 0 < e) (he1 : e < 1 / 3) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hint : IntegrableOn (fun w => (1 - e) * i9KReal e x w - (1 - 3 * e) * i9MReal e x w)
      (Ioo 0 1)) :
    ∫ w in Ioo (0 : ℝ) 1, ((1 - e) * i9KReal e x w - (1 - 3 * e) * i9MReal e x w) =
      -((x * (1 - x)) ^ (-e) * ((3 - e) / (2 + 2 * e))) := by
  have hc := i9_c_pos hx
  set c := x * (1 - x) with hcdef
  have hs : 0 < 1 - 3 * e := by linarith
  have h2e : 0 < 2 * e := by linarith
  set G : ℝ → ℝ := fun w => c ^ (2 * e - 1) * (w ^ (2 * e) *
      ((c * (1 - w) ^ 2 + w) ^ (1 - 3 * e) - w ^ (1 - 3 * e))) -
      c ^ (-e) * (w ^ (2 * e) * (1 + (1 - 3 * e) * w ^ 2 / (2 + 2 * e))) with hG
  have hcont : Continuous G := by
    have h1 : Continuous fun w : ℝ => w ^ (2 * e) := Real.continuous_rpow_const h2e.le
    have h2 : Continuous fun w : ℝ => w ^ (1 - 3 * e) := Real.continuous_rpow_const hs.le
    have h3 : Continuous fun w : ℝ => (c * (1 - w) ^ 2 + w) ^ (1 - 3 * e) :=
      (Real.continuous_rpow_const hs.le).comp (by fun_prop)
    exact (continuous_const.mul (h1.mul (h3.sub h2))).sub
      (continuous_const.mul (h1.mul (by fun_prop)))
  have hderiv : ∀ w ∈ Ioo (0 : ℝ) 1,
      HasDerivAt G ((1 - e) * i9KReal e x w - (1 - 3 * e) * i9MReal e x w) w := by
    intro w hw
    have hw0 := hw.1
    have hP : 0 < c * (1 - w) ^ 2 + w := by positivity
    have d1 : HasDerivAt (fun w : ℝ => w ^ (2 * e)) (2 * e * w ^ (2 * e - 1)) w :=
      Real.hasDerivAt_rpow_const (Or.inl hw0.ne')
    have dP : HasDerivAt (fun w : ℝ => c * (1 - w) ^ 2 + w) (-2 * c * (1 - w) + 1) w := by
      have h := ((hasDerivAt_pow 2 w).const_mul c).sub ((hasDerivAt_id' w).const_mul (2 * c - 1))
      have e : (fun w : ℝ => c * (1 - w) ^ 2 + w) =
          fun w => (c * w ^ 2 - (2 * c - 1) * w) + c := by funext w; ring
      rw [e]
      convert h.add_const c using 1
      push_cast
      ring
    have d2 := dP.rpow_const (p := 1 - 3 * e) (Or.inl hP.ne')
    have d3 : HasDerivAt (fun w : ℝ => w ^ (1 - 3 * e)) ((1 - 3 * e) * w ^ (1 - 3 * e - 1)) w :=
      Real.hasDerivAt_rpow_const (Or.inl hw0.ne')
    have d4 : HasDerivAt (fun w : ℝ => 1 + (1 - 3 * e) * w ^ 2 / (2 + 2 * e))
        ((1 - 3 * e) * (2 * w) / (2 + 2 * e)) w := by
      have h := ((hasDerivAt_pow 2 w).const_mul ((1 - 3 * e) / (2 + 2 * e))).const_add 1
      have e : (fun w : ℝ => 1 + (1 - 3 * e) * w ^ 2 / (2 + 2 * e)) =
          fun w => 1 + (1 - 3 * e) / (2 + 2 * e) * w ^ 2 := by funext w; ring
      rw [e]
      convert h using 1
      push_cast
      ring
    have dG := ((d1.mul (d2.sub d3)).const_mul (c ^ (2 * e - 1))).sub
      ((d1.mul d4).const_mul (c ^ (-e)))
    convert dG using 1
    have hPoly : i9Poly x w 1 = c * (1 - w) ^ 2 + w := by rw [i9Poly, hcdef]; ring
    unfold i9KReal i9MReal
    simp only [Pi.sub_apply]
    rw [hPoly, ← hcdef]
    set P := c * (1 - w) ^ 2 + w with hPdef
    have r1 : c ^ (2 * e - 1) = c ^ (-e) / c ^ (1 - 3 * e) := by
      rw [← Real.rpow_sub hc]; congr 1; ring
    have r2 : c ^ (2 * e) = c ^ (2 * e - 1) * c := by
      rw [← Real.rpow_add_one hc.ne']; congr 1; ring
    have r3 : P ^ (-3 * e) = P ^ (1 - 3 * e) / P := by
      rw [← Real.rpow_sub_one hP.ne']; congr 1; ring
    rw [Real.rpow_sub_one hw0.ne', Real.rpow_sub_one hw0.ne', Real.rpow_sub_one hP.ne', r3, r2,
      r1]
    have hcs : 0 < c ^ (1 - 3 * e) := Real.rpow_pos_of_pos hc _
    have h22 : (2 + 2 * e) ≠ 0 := by linarith
    field_simp
    rw [hPdef]
    ring
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont.continuousOn hderiv
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hint)]
  simp only [hG]
  rw [Real.zero_rpow h2e.ne', Real.one_rpow, Real.one_rpow]
  have h22 : (2 + 2 * e) ≠ 0 := by linarith
  norm_num [Real.zero_rpow h2e.ne', Real.zero_rpow hs.ne']
  field_simp
  ring_nf
  simp

/-! ### The identity on the square -/

theorem integrableOn_i9KReal {e : ℝ} (he0 : 0 < e) (he1 : e < 1 / 20) :
    IntegrableOn (fun z : ℝ × ℝ => i9KReal e z.1 z.2) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hbi : Integrable (fun z : ℝ × ℝ =>
      17 * ((z.1 * (1 - z.1)) ^ (-(17 / 20) : ℝ) * z.2 ^ (-(17 / 20) : ℝ)))
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) := by
    rw [volume_restrict_prod2]
    exact ((integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
      (integrableOn_rpow_Ioo (by norm_num))).const_mul 17
  have hm : Measurable (fun z : ℝ × ℝ => i9KReal e z.1 z.2) := by
    unfold i9KReal i9Poly
    fun_prop
  refine hbi.mono' hm.aestronglyMeasurable (ae_restrict_of_forall_mem hS fun z hz => ?_)
  have hε : ‖(e : ℂ)‖ < 1 / 20 := by
    rw [Complex.norm_real, Real.norm_of_nonneg he0.le]
    exact he1
  have h := norm_i9K_integrand_le hε hz.1 hz.2
  rwa [i9K_integrand_ofReal hz.1 hz.2, Complex.norm_real] at h

theorem integrableOn_i9MReal {e : ℝ} (he0 : 0 < e) (he1 : e < 1 / 20) :
    IntegrableOn (fun z : ℝ × ℝ => i9MReal e z.1 z.2) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hm : Measurable (fun z : ℝ × ℝ => i9MReal e z.1 z.2) := by
    unfold i9MReal i9Poly
    fun_prop
  refine integrable_i9M_bound.mono' hm.aestronglyMeasurable
    (ae_restrict_of_forall_mem hS fun z hz => ?_)
  have hε : ‖(e : ℂ)‖ < 1 / 20 := by
    rw [Complex.norm_real, Real.norm_of_nonneg he0.le]
    exact he1
  have h := norm_i9MD_le hε hz.1 hz.2
  rwa [i9MD_ofReal hz.1 hz.2, Complex.norm_real] at h

/-- **The identity at real `ε`**: `(1 - ε) K - s M = -(3 - ε) B / (2 + 2ε)` for `0 < ε < 1/20`. -/
theorem i9_real_identity {e : ℝ} (he0 : 0 < e) (he1 : e < 1 / 20) :
    (1 - e) * (∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i9KReal e z.1 z.2) -
      (1 - 3 * e) * (∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i9MReal e z.1 z.2) =
      -((3 - e) / (2 + 2 * e)) * ∫ x in Ioo (0 : ℝ) 1, (x * (1 - x)) ^ (-e) := by
  have hK := integrableOn_i9KReal he0 he1
  have hM := integrableOn_i9MReal he0 he1
  have hΦ : Integrable (fun z : ℝ × ℝ => (1 - e) * i9KReal e z.1 z.2 -
      (1 - 3 * e) * i9MReal e z.1 z.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    rw [← volume_restrict_prod2]
    exact (hK.const_mul _).sub (hM.const_mul _)
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_sub (hK.const_mul _) (hM.const_mul _), volume_restrict_prod2,
    integral_prod _ hΦ, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hΦ.prod_right_ae, ae_restrict_mem measurableSet_Ioo] with x hx hxI
  rw [i9_fiber_identity he0 (by linarith) hxI hx]
  ring

/-- `(1 - ε)(2 + 2ε) K(ε) - (2 + 2ε)(1 - 3ε) M(ε) + (3 - ε) B(ε)`. -/
noncomputable def i9KMB (ε : ℂ) : ℂ :=
  (1 - ε) * (2 + 2 * ε) * i9K ε - (2 + 2 * ε) * (1 - 3 * ε) * i9M ε + (3 - ε) * i9B ε

theorem i9KMB_ofReal {e : ℝ} (he0 : 0 < e) (he1 : e < 1 / 20) : i9KMB (e : ℂ) = 0 := by
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hK : i9K e = ((∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i9KReal e z.1 z.2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact setIntegral_congr_fun hS fun z hz => i9K_integrand_ofReal hz.1 hz.2
  have hM : i9M e = ((∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i9MReal e z.1 z.2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact setIntegral_congr_fun hS fun z hz => i9MD_ofReal (x := z.1) (w := z.2) hz.1 hz.2
  have hB : i9B e = ((∫ x in Ioo (0 : ℝ) 1, (x * (1 - x)) ^ (-e) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact setIntegral_congr_fun measurableSet_Ioo fun x hx => i9BD_ofReal e x hx
  rw [i9KMB, hK, hM, hB]
  have h := i9_real_identity he0 he1
  have h22 : (2 + 2 * e) ≠ 0 := by linarith
  have hdiv : (2 + 2 * e) * ((3 - e) / (2 + 2 * e)) = 3 - e := mul_div_cancel₀ _ h22
  set Kr := ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i9KReal e z.1 z.2
  set Mr := ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i9MReal e z.1 z.2
  set Br := ∫ x in Ioo (0 : ℝ) 1, (x * (1 - x)) ^ (-e)
  have h2 : (1 - e) * (2 + 2 * e) * Kr - (2 + 2 * e) * (1 - 3 * e) * Mr + (3 - e) * Br = 0 := by
    linear_combination (2 + 2 * e) * h - Br * hdiv
  have h3 := congrArg (fun r : ℝ => (r : ℂ)) h2
  push_cast at h3
  linear_combination h3

theorem analyticOnNhd_i9KMB : AnalyticOnNhd ℂ i9KMB (ball 0 (1 / 40)) := fun ε hε => by
  have hK := analyticOnNhd_i9K ε hε
  have hM := analyticOnNhd_i9M ε hε
  have hB := analyticOnNhd_i9B ε hε
  unfold i9KMB
  fun_prop

/-- **The identity**: `(1 - ε)(2 + 2ε) K - (2 + 2ε)(1 - 3ε) M + (3 - ε) B = 0` on
`‖ε‖ < 1/40`. -/
theorem i9KMB_eq_zero {ε : ℂ} (hε : ε ∈ ball (0 : ℂ) (1 / 40)) : i9KMB ε = 0 := by
  have h0 : ((1 / 80 : ℝ) : ℂ) ∈ ball (0 : ℂ) (1 / 40) := by
    rw [mem_ball_zero_iff, Complex.norm_real]
    norm_num
  have hfreq : ∃ᶠ z in 𝓝[≠] ((1 / 80 : ℝ) : ℂ), i9KMB z = 0 := by
    set u : ℕ → ℂ := fun n => ((1 / 80 + 1 / 100 * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ) with hu_def
    have hu : Tendsto u atTop (𝓝[≠] ((1 / 80 : ℝ) : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h : Tendsto (fun n : ℕ => (1 / 80 + 1 / 100 * (1 / ((n : ℝ) + 1)) : ℝ)) atTop
            (𝓝 (1 / 80 + 1 / 100 * 0)) :=
          tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _)
        rw [mul_zero, add_zero] at h
        exact (Complex.continuous_ofReal.tendsto _).comp h
      · have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        simp only [hu_def, mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj]
        intro h
        linarith
    refine hu.frequently (Frequently.of_forall fun n => ?_)
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [n.cast_nonneg (α := ℝ)]
    exact i9KMB_ofReal (by positivity) (by linarith)
  exact analyticOnNhd_i9KMB.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball _ _).isPreconnected h0 hfreq hε

/-! ### Comparing the Taylor coefficients -/

theorem i9_coeff_step {a : ℂ} {g : ℂ → ℂ} (hg : ContinuousAt g 0)
    (h : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), a + ε * g ε = 0) :
    a = 0 ∧ ∀ᶠ ε in 𝓝[≠] (0 : ℂ), g ε = 0 := by
  have ht : Tendsto (fun ε => a + ε * g ε) (𝓝[≠] 0) (𝓝 a) := by
    have hc : ContinuousAt (fun ε => a + ε * g ε) 0 :=
      continuousAt_const.add (continuousAt_id.mul hg)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have ha : a = 0 := tendsto_nhds_unique ht (tendsto_const_nhds.congr' (h.mono fun ε hε => hε.symm))
  refine ⟨ha, ?_⟩
  filter_upwards [h, self_mem_nhdsWithin] with ε hε hne
  rw [ha, zero_add] at hε
  exact (mul_eq_zero.mp hε).resolve_left hne

/-- **The coefficients of `K` in terms of those of `M` and `B`**, through `ε³`:
`2 Kₖ - 2 Kₖ₋₂ - 2 Mₖ + 4 Mₖ₋₁ + 6 Mₖ₋₂ + 3 Bₖ - Bₖ₋₁ = 0`. -/
theorem i9KCoeff_rel :
    2 * i9KCoeff 0 - 2 * i9MCoeff 0 + 3 * i9BCoeff 0 = 0 ∧
    2 * i9KCoeff 1 - 2 * i9MCoeff 1 + 4 * i9MCoeff 0 + 3 * i9BCoeff 1 - i9BCoeff 0 = 0 ∧
    2 * i9KCoeff 2 - 2 * i9KCoeff 0 - 2 * i9MCoeff 2 + 4 * i9MCoeff 1 + 6 * i9MCoeff 0 +
      3 * i9BCoeff 2 - i9BCoeff 1 = 0 ∧
    2 * i9KCoeff 3 - 2 * i9KCoeff 1 - 2 * i9MCoeff 3 + 4 * i9MCoeff 2 + 6 * i9MCoeff 1 +
      3 * i9BCoeff 3 - i9BCoeff 2 = 0 := by
  obtain ⟨RK, hRK, hK⟩ := hasTruncLaurent_i9K_coeff 4
  obtain ⟨RM, hRM, hM⟩ := hasTruncLaurent_i9M_coeff 4
  obtain ⟨RB, hRB, hB⟩ := hasTruncLaurent_i9B_coeff 4
  have cK := hRK.continuousAt
  have cM := hRM.continuousAt
  have cB := hRB.continuousAt
  have hZ : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), i9KMB ε = 0 := nhdsWithin_le_nhds (by
    filter_upwards [ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 40)] with ε hε
    exact i9KMB_eq_zero hε)
  set K0 : ℂ := ((i9KCoeff 0 : ℝ) : ℂ)
  set K1 : ℂ := ((i9KCoeff 1 : ℝ) : ℂ)
  set K2 : ℂ := ((i9KCoeff 2 : ℝ) : ℂ)
  set K3 : ℂ := ((i9KCoeff 3 : ℝ) : ℂ)
  set M0 : ℂ := ((i9MCoeff 0 : ℝ) : ℂ)
  set M1 : ℂ := ((i9MCoeff 1 : ℝ) : ℂ)
  set M2 : ℂ := ((i9MCoeff 2 : ℝ) : ℂ)
  set M3 : ℂ := ((i9MCoeff 3 : ℝ) : ℂ)
  set B0 : ℂ := ((i9BCoeff 0 : ℝ) : ℂ)
  set B1 : ℂ := ((i9BCoeff 1 : ℝ) : ℂ)
  set B2 : ℂ := ((i9BCoeff 2 : ℝ) : ℂ)
  set B3 : ℂ := ((i9BCoeff 3 : ℝ) : ℂ)
  have hev : ∀ᶠ ε in 𝓝[≠] (0 : ℂ),
      (2 * K0 - 2 * M0 + 3 * B0) + ε * ((2 * K1 - 2 * M1 + 4 * M0 + 3 * B1 - B0) +
      ε * ((2 * K2 - 2 * K0 - 2 * M2 + 4 * M1 + 6 * M0 + 3 * B2 - B1) +
      ε * ((2 * K3 - 2 * K1 - 2 * M3 + 4 * M2 + 6 * M1 + 3 * B3 - B2) +
      ε * ((-2 * K2 + 6 * M2 + 4 * M3 - B3) + (-2 * K3 + 6 * M3) * ε +
        (2 - 2 * ε ^ 2) * RK ε - (2 - 4 * ε - 6 * ε ^ 2) * RM ε + (3 - ε) * RB ε)))) = 0 := by
    filter_upwards [hZ, hK, hM, hB] with ε hz hk hm hb
    unfold i9KMB at hz
    rw [hk, hm, hb] at hz
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hz
    linear_combination hz
  obtain ⟨h0, ev1⟩ := i9_coeff_step (by fun_prop) hev
  obtain ⟨h1, ev2⟩ := i9_coeff_step (by fun_prop) ev1
  obtain ⟨h2, ev3⟩ := i9_coeff_step (by fun_prop) ev2
  obtain ⟨h3, -⟩ := i9_coeff_step (by fun_prop) ev3
  simp only [K0, K1, K2, K3, M0, M1, M2, M3, B0, B1, B2, B3] at h0 h1 h2 h3
  exact ⟨by exact_mod_cast h0, by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

end QED.ThreeLoopD
