/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5CoV

/-!
# Set (d), master `I₅`: the large-`t` expansion of the triangle at `w = t`

Averaging the fibre expansion `QED.ThreeLoopD.norm_i5Fib_sub_le` against `(1 + r)⁻² dr`, with
`∫₀^∞ (1 + r) ^ c dr = -1/(c + 1)` (`QED.ThreeLoopD.i5_integral_one_add_cpow`) at `c = -2` and
`c = -2 + 2ε`, gives, for `t ≥ 1` and `0 < ‖ε‖ ≤ 1/10`,

  `‖i5Tri ε t t - (t⁻¹ / (ε (1 - 2ε)) - (G / ε) t ^ (-1 - ε))‖ ≤ C t ^ (-7/5)`
  (`QED.ThreeLoopD.norm_i5Tri_sub_asym_le`).

The two terms are the soft (on-shell bubble) and hard (massless) regions.

## Main results

* `QED.ThreeLoopD.i5_integral_one_add_cpow`, `QED.ThreeLoopD.norm_i5Tri_sub_asym_le`.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology

namespace QED.ThreeLoopD

/-- **`∫₀^∞ (1 + r) ^ c dr = -1/(c + 1)`** for `re c < -1`, with integrability. -/
theorem i5_integral_one_add_cpow {c : ℂ} (hc : c.re < -1) :
    IntegrableOn (fun r : ℝ => ((1 + r : ℝ) : ℂ) ^ c) (Ioi 0) ∧
      ∫ r in Ioi (0 : ℝ), ((1 + r : ℝ) : ℂ) ^ c = -1 / (c + 1) := by
  have hc1 : c + 1 ≠ 0 := fun h => by
    have := congr_arg re h; simp at this; linarith
  have hm : Measurable fun r : ℝ => ((1 + r : ℝ) : ℂ) ^ c := i5_measurable_cpow_one_add c
  have hI : IntegrableOn (fun r : ℝ => ((1 + r : ℝ) : ℂ) ^ c) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    refine IntegrableOn.union ?_ ?_
    · refine (integrableOn_const (C := (1 : ℝ)) (by simp)).mono'
        hm.aestronglyMeasurable.restrict
        (ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => ?_)
      rw [norm_cpow_eq_rpow_re_of_pos (by linarith [hr.1])]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hr.1]) (by linarith)
    · refine (integrableOn_Ioi_rpow_of_lt hc one_pos).mono' hm.aestronglyMeasurable.restrict
        (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_)
      have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
      rw [norm_cpow_eq_rpow_re_of_pos (by linarith)]
      exact Real.rpow_le_rpow_of_nonpos hr0 (by linarith) (by linarith)
  refine ⟨hI, ?_⟩
  set F : ℝ → ℂ := fun r => ((1 + 1 * r : ℝ) : ℂ) ^ (c + 1) / (c + 1) with hF
  have hd : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt F (((1 + r : ℝ) : ℂ) ^ c) r := fun r hr => by
    have hr' : (0 : ℝ) < r := hr
    have hr0 : (0 : ℝ) < 1 + 1 * r := by linarith
    refine ((i5_hasDerivAt_cpow_affine 1 1 (c + 1) hr0).div_const (c + 1)).congr_deriv ?_
    rw [add_sub_cancel_right, one_mul, ofReal_one, mul_one]
    field_simp
  have hcont : ContinuousWithinAt F (Ici 0) 0 :=
    ((i5_hasDerivAt_cpow_affine 1 1 (c + 1) (by norm_num : (0 : ℝ) < 1 + 1 * 0)).div_const
      (c + 1)).continuousAt.continuousWithinAt
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hT : Tendsto (fun r : ℝ => (1 + r) ^ (-(-(c.re + 1))) / ‖c + 1‖) atTop (𝓝 0) := by
      have := ((tendsto_rpow_neg_atTop (by linarith : 0 < -(c.re + 1))).comp
        (tendsto_atTop_add_const_left atTop 1 tendsto_id)).div_const ‖c + 1‖
      simpa using this
    refine squeeze_zero_norm' ?_ (by simpa using hT)
    filter_upwards [eventually_gt_atTop 0] with r hr
    rw [hF, norm_div, norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simp
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hI hlim
  rw [h, hF]
  simp
  ring

theorem i5Bm_pos (r : ℝ) (hr : 0 ≤ r) : 0 < i5Bm r := by unfold i5Bm; positivity

theorem i5Bm_le_one {r : ℝ} (hr : 0 ≤ r) : i5Bm r ≤ 1 := by
  unfold i5Bm
  exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith))

theorem i5Bm_eq_cpow {r : ℝ} (hr : 0 ≤ r) : (i5Bm r : ℂ) = ((1 + r : ℝ) : ℂ) ^ (-2 : ℂ) := by
  have h : ((1 + r : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  rw [cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast, i5Bm]
  push_cast
  rw [inv_pow]

theorem i5Bm_mul_cpow {r : ℝ} (hr : 0 ≤ r) (ε : ℂ) :
    (i5Bm r : ℂ) * (((i5Bm r)⁻¹ : ℝ) : ℂ) ^ ε = ((1 + r : ℝ) : ℂ) ^ (-2 + 2 * ε) := by
  have h1 : (0 : ℝ) < 1 + r := by linarith
  have h : ((1 + r : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h1.ne'
  have e : (i5Bm r)⁻¹ = (1 + r) * (1 + r) := by
    unfold i5Bm; rw [inv_pow, inv_inv]; ring
  rw [e, ofReal_mul, mul_cpow_ofReal_nonneg h1.le h1.le, i5Bm_eq_cpow hr,
    show (-2 : ℂ) + 2 * ε = -2 + ε + ε by ring, cpow_add _ _ h, cpow_add _ _ h]
  ring

/-- The two-region expansion of the triangle at `w = t`. -/
noncomputable def i5TriAs (ε : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ)⁻¹ / (ε * (1 - 2 * ε)) - i13G ε / ε * (t : ℂ) ^ (-1 - ε)

/-- The fibre expansion. -/
noncomputable def i5FibAs (ε : ℂ) (t m : ℝ) : ℂ :=
  (t : ℂ)⁻¹ * ((m⁻¹ : ℝ) : ℂ) ^ ε / ε - i13G ε / ε * (t : ℂ) ^ (-1 - ε)

theorem integral_i5FibAs {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) (h0 : ε ≠ 0) (t : ℝ) :
    IntegrableOn (fun r => (i5Bm r : ℂ) * i5FibAs ε t (i5Bm r)) (Ioi 0) ∧
      ∫ r in Ioi (0 : ℝ), (i5Bm r : ℂ) * i5FibAs ε t (i5Bm r) = i5TriAs ε t := by
  obtain ⟨-, h1, h2⟩ := i5_re_facts hε
  obtain ⟨I1, J1⟩ := i5_integral_one_add_cpow (c := -2 + 2 * ε) (by simp; linarith)
  obtain ⟨I2, J2⟩ := i5_integral_one_add_cpow (c := -2) (by simp)
  have h12 : (1 : ℂ) - 2 * ε ≠ 0 := (i13_eps_facts (by linarith)).2.2.2.1
  have e : EqOn (fun r => (i5Bm r : ℂ) * i5FibAs ε t (i5Bm r))
      (fun r => (t : ℂ)⁻¹ / ε * ((1 + r : ℝ) : ℂ) ^ (-2 + 2 * ε) -
        i13G ε / ε * (t : ℂ) ^ (-1 - ε) * ((1 + r : ℝ) : ℂ) ^ (-2 : ℂ)) (Ioi 0) :=
    fun r hr => by
      have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
      simp only [i5FibAs]
      rw [← i5Bm_mul_cpow hr0, ← i5Bm_eq_cpow hr0]
      ring
  have hI : IntegrableOn (fun r => (t : ℂ)⁻¹ / ε * ((1 + r : ℝ) : ℂ) ^ (-2 + 2 * ε) -
      i13G ε / ε * (t : ℂ) ^ (-1 - ε) * ((1 + r : ℝ) : ℂ) ^ (-2 : ℂ)) (Ioi 0) :=
    (I1.const_mul _).sub (I2.const_mul _)
  refine ⟨hI.congr_fun e.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_sub (I1.const_mul _) (I2.const_mul _),
    integral_const_mul, integral_const_mul, J1, J2, i5TriAs,
    show (-2 : ℂ) + 2 * ε + 1 = -(1 - 2 * ε) by ring]
  generalize (t : ℂ)⁻¹ = u
  generalize (t : ℂ) ^ (-1 - ε) = T
  field_simp
  ring

/-- **The large-`t` expansion of the triangle at `w = t`.** -/
theorem norm_i5Tri_sub_asym_le {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) (h0 : ε ≠ 0) {t : ℝ} (ht : 1 ≤ t) :
    ‖i5Tri ε t (t : ℂ) - i5TriAs ε t‖ ≤ i5CF * t ^ (-(7 / 5 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have hε4 : ‖ε‖ ≤ 1 / 4 := by linarith
  obtain ⟨IA, JA⟩ := integral_i5FibAs hε h0 t
  have IF := integrableOn_i5_fib hε4 ht0
  obtain ⟨I2, J2⟩ := i5_integral_one_add_cpow (c := -2) (by simp)
  have hBc : IntegrableOn (fun r => (i5Bm r : ℂ)) (Ioi 0) :=
    I2.congr_fun (fun r hr => (i5Bm_eq_cpow (le_of_lt hr)).symm) measurableSet_Ioi
  have hBr : IntegrableOn i5Bm (Ioi 0) := by
    have := hBc.re
    simpa using this
  have hB1 : ∫ r in Ioi (0 : ℝ), i5Bm r = 1 := by
    have e : ∫ r in Ioi (0 : ℝ), (i5Bm r : ℂ) = 1 := by
      rw [setIntegral_congr_fun measurableSet_Ioi (fun r hr => i5Bm_eq_cpow (le_of_lt hr)), J2]
      norm_num
    rw [integral_complex_ofReal] at e
    exact_mod_cast e
  rw [i5Tri_eq_integral_fib hε4 ht0, ← JA, ← integral_sub IF IA]
  calc ‖∫ r in Ioi (0 : ℝ), ((i5Bm r : ℂ) * i5Fib ε t (i5Bm r) -
          (i5Bm r : ℂ) * i5FibAs ε t (i5Bm r))‖ ≤
        ∫ r in Ioi (0 : ℝ), i5Bm r * (i5CF * t ^ (-(7 / 5 : ℝ))) := by
        refine norm_integral_le_of_norm_le (hBr.mul_const _)
          (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_)
        have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
        rw [← mul_sub, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (i5Bm_pos r hr0)]
        exact mul_le_mul_of_nonneg_left (norm_i5Fib_sub_le hε h0 ht (i5Bm_pos r hr0)
          (i5Bm_le_one hr0)) (i5Bm_pos r hr0).le
    _ = i5CF * t ^ (-(7 / 5 : ℝ)) := by rw [integral_mul_const, hB1, one_mul]

end QED.ThreeLoopD
