/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI10KaFactor
import QED.ThreeLoopE.SetEMastersI10KabVal
import QED.Polylog.ExtraIntegrals
import QED.Polylog.LogLogSq
import QED.ThreeLoopD.SetDMastersI9KValB

/-!
# The differentiated bubble factor of the cubic coefficient of `Kₐ`

After integrating out the joining variable, the derivative of the bubble
factor generates a mixed logarithmic square moment. Integration by parts
reduces the moment to integrals of weights three and four.
-/

public section

open Real Set MeasureTheory Filter Topology QED.Polylog QED.ThreeLoopD

namespace QED.ThreeLoopE

private theorem i10Ka_reflect_interval {f : ℝ → ℝ} {v : ℝ}
    (h : IntervalIntegrable f volume 0 1 ∧ ∫ x in (0 : ℝ)..1, f x = v) :
    IntervalIntegrable (fun x => f (1 - x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, f (1 - x) = v := by
  refine ⟨?_, ?_⟩
  · simpa only [sub_self, sub_zero] using (h.1.symm.comp_sub_left 1)
  · rw [intervalIntegral.integral_comp_sub_left, sub_self, sub_zero]
    exact h.2

private theorem intervalIntegrable_and_integral_i10Ka_logSq :
    IntervalIntegrable (fun x : ℝ => log x ^ 2) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, log x ^ 2 = 2 := by
  let F := fun x : ℝ => x * (log x ^ 2 - 2 * log x + 2)
  have hd {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt F (log x ^ 2) x := by
    have hl := hasDerivAt_log hx.1.ne'
    refine ((hasDerivAt_id' x).mul (((hl.pow 2).sub (hl.const_mul 2)).add_const 2)).congr_deriv ?_
    simp only [Pi.sub_apply, Pi.pow_apply]
    field_simp [hx.1.ne']
    ring
  have hx : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h0 : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_mul_log_sq_zero.sub (tendsto_mul_log_zero.const_mul 2)).add
      (hx.const_mul 2)
    rw [show (0 : ℝ) - 2 * 0 + 2 * 0 = 0 by ring] at h
    exact h.congr fun x => by dsimp [F]; ring
  have h1 : Tendsto F (𝓝[<] 1) (𝓝 2) := by
    have hc : ContinuousAt F 1 :=
      continuousAt_id.mul
        ((((continuousAt_log one_ne_zero).pow 2).sub
          ((continuousAt_log one_ne_zero).const_mul 2)).add_const 2)
    have hv : F 1 = 2 := by simp [F]
    rw [← hv]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [sub_zero] using
    intervalIntegrable_and_integral_eq_of_nonneg (fun _ => hd) (fun x _ => sq_nonneg (log x)) h0 h1

/-- The mixed logarithmic square without a rational weight. -/
theorem intervalIntegrable_and_integral_i10Ka_logSqMulLogSq :
    IntervalIntegrable (fun x => log x ^ 2 * log (1 - x) ^ 2) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, log x ^ 2 * log (1 - x) ^ 2 =
        24 - 4 * π ^ 2 / 3 - 8 * zeta3 - π ^ 4 / 90 := by
  let A := fun x : ℝ => log x ^ 2 * log (1 - x) ^ 2
  let B := fun x : ℝ => log x * log x * log (1 - x)
  let C := fun x : ℝ => log x * log (1 - x) ^ 2 / x
  let F := fun x : ℝ => x * A x
  have hCont : ContinuousOn A (Ioo 0 1) :=
    ((continuousOn_log.mono fun x hx => hx.1.ne').pow 2).mul
      ((((continuousOn_const.sub continuousOn_id).log fun x (hx : x ∈ Ioo _ _) =>
          (sub_pos.mpr hx.2).ne')).pow 2)
  have hAl : Tendsto A (𝓝[>] 0) (𝓝 0) := by
    simpa only [A, mul_pow, zero_pow (by decide : 2 ≠ 0)] using
      tendsto_log_mul_log_one_sub_zero.pow 2
  have hAr : Tendsto A (𝓝[<] 1) (𝓝 0) := by
    simpa only [A, mul_pow, zero_pow (by decide : 2 ≠ 0)] using
      tendsto_log_mul_log_one_sub_one.pow 2
  have hI : IntervalIntegrable A volume 0 1 := by
    have h := continuousOn_Icc_extendFrom_Ioo hCont hAl hAr
    apply (h.mono (by rw [uIcc_of_le zero_le_one])).intervalIntegrable.congr_uIoo
    intro x hx
    rw [uIoo_of_le zero_le_one] at hx
    exact extendFrom_extends hCont x hx
  have hB : IntervalIntegrable B volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, B x = 2 * zeta3 - 6 + π ^ 2 / 3 :=
    i9_integral_log_sq_mul_log_one_sub
  have hC : IntervalIntegrable C volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, C x = -(π ^ 4 / 180) :=
    intervalIntegrable_and_integral_log_mul_log_one_sub_sq_div
  have hBr := i10Ka_reflect_interval hB
  have hCr := i10Ka_reflect_interval hC
  have hD {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt F (((A x + 2 * B (1 - x)) - 2 * C (1 - x)) + 2 * B x) x := by
    have hc := (sub_pos.mpr hx.2).ne'
    have h1 := (hasDerivAt_log hx.1.ne').pow 2
    have h2 := (((hasDerivAt_id' x).const_sub 1).log hc).pow 2
    refine ((hasDerivAt_id' x).mul (h1.mul h2)).congr_deriv ?_
    simp only [A, B, C, sub_sub_cancel, Pi.mul_apply, Pi.pow_apply]
    field_simp [hx.1.ne', hc]
    ring
  have hJ := (((hI.add (hBr.1.const_mul 2)).sub (hCr.1.const_mul 2)).add (hB.1.const_mul 2))
  have hF0 : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    simpa only [F, id_eq, mul_zero] using
      ((tendsto_id (x := 𝓝[>] (0 : ℝ))).mono_right nhdsWithin_le_nhds).mul hAl
  have hF1 : Tendsto F (𝓝[<] 1) (𝓝 0) := by
    simpa only [F, id_eq, mul_zero] using
      ((tendsto_id (x := 𝓝[<] (1 : ℝ))).mono_right nhdsWithin_le_nhds).mul hAr
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun x hx => hD hx) hJ hF0 hF1
  rw [intervalIntegral.integral_add ((hI.add (hBr.1.const_mul 2)).sub (hCr.1.const_mul 2))
    (hB.1.const_mul 2), intervalIntegral.integral_sub (hI.add (hBr.1.const_mul 2))
    (hCr.1.const_mul 2), intervalIntegral.integral_add hI (hBr.1.const_mul 2)] at h
  simp only [intervalIntegral.integral_const_mul, hBr.2, hCr.2, hB.2, sub_zero] at h
  refine ⟨hI, ?_⟩
  linarith only [h]

/-- The reduced cubic contribution from differentiating the bubble factor. -/
theorem integral_i10Ka_cubic_bubble :
    ∫ r in Ioo (0 : ℝ) 1, log (1 - r) ^ 2 / 2 *
      (π ^ 2 / 6 + log r ^ 2 / 2 + (1 + log r) / r) =
        6 - π ^ 2 / 6 - zeta3 - π ^ 4 / 180 := by
  obtain ⟨ha, hva⟩ := i10_ioo_of_interval
    (i10Ka_reflect_interval intervalIntegrable_and_integral_i10Ka_logSq)
  obtain ⟨hb, hvb⟩ := i10_ioo_of_interval intervalIntegrable_and_integral_i10Ka_logSqMulLogSq
  obtain ⟨hc, hvc⟩ := i10_ioo_of_interval intervalIntegrable_and_integral_log_one_sub_sq_div
  obtain ⟨hd, hvd⟩ := i10_ioo_of_interval intervalIntegrable_and_integral_log_mul_log_one_sub_sq_div
  calc
    _ = ∫ r in Ioo (0 : ℝ) 1, ((π ^ 2 / 12 * log (1 - r) ^ 2 +
        1 / 4 * (log r ^ 2 * log (1 - r) ^ 2)) + 1 / 2 * (log (1 - r) ^ 2 / r)) +
          1 / 2 * (log r * log (1 - r) ^ 2 / r) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      field_simp [hr.1.ne']
      ring
    _ = _ := by
      have h1 := ha.const_mul (π ^ 2 / 12)
      have h2 := hb.const_mul (1 / 4)
      have h3 := hc.const_mul (1 / 2)
      have h4 := hd.const_mul (1 / 2)
      have e1 := integral_add ((h1.add h2).add h3) h4
      have e2 := integral_add (h1.add h2) h3
      have e3 := integral_add h1 h2
      simp only [Pi.add_apply] at e1 e2
      rw [e1, e2, e3]
      simp only [integral_const_mul, hva, hvb, hvc, hvd]
      ring

private theorem norm_log_one_sub_div_two_le_rpow {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    ‖((-log (1 - r) / 2 : ℝ) : ℂ)‖ ≤ 2 * (r * (1 - r)) ^ (-(1 / 4) : ℝ) := by
  have hc := sub_pos.mpr hr.2
  have hr₁ : 1 - r ≤ 1 := by linarith [hr.1]
  have h := log_le_sub_one_of_pos (rpow_pos_of_pos hc (-(1 / 4) : ℝ))
  rw [log_rpow hc] at h
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith [log_nonpos hc.le hr₁])]
  have hm : (1 - r) ^ (-(1 / 4) : ℝ) ≤ (r * (1 - r)) ^ (-(1 / 4) : ℝ) := by
    apply rpow_le_rpow_of_nonpos (mul_pos hr.1 hc) _ (by norm_num)
    exact mul_le_of_le_one_left hc.le hr.2.le
  linarith

/-- The bubble-factor term in the derivative of the original divided integrand. -/
theorem integral_i10Ka_cubic_bubble_prod :
    ∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
      ((-log (1 - q.2) / 2 : ℝ) : ℂ) * i10KaH 0 q =
        ((6 - π ^ 2 / 6 - zeta3 - π ^ 4 / 180 : ℝ) : ℂ) := by
  let S := Ioo (0 : ℝ) 1
  let F := fun q : ℝ × ℝ => ((-log (1 - q.2) / 2 : ℝ) : ℂ) * i10KaH 0 q
  have hS : MeasurableSet S := measurableSet_Ioo
  have hB : IntegrableOn (fun q : ℝ × ℝ => 136 * ((q.1 * (1 - q.1)) ^ (-(3 / 5) : ℝ) *
      (q.2 * (1 - q.2)) ^ (-(4 / 5) : ℝ))) (S ×ˢ S) := by
    rw [IntegrableOn, volume_restrict_prod2]
    exact ((integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
      (integrableOn_mul_one_sub_rpow_Ioo (by norm_num))).const_mul 136
  have hF : IntegrableOn F (S ×ˢ S) := by
    refine hB.mono' ?_ (ae_restrict_of_forall_mem (hS.prod hS) fun q hq => ?_)
    · exact ((by fun_prop : Measurable
        (fun q : ℝ × ℝ => ((-log (1 - q.2) / 2 : ℝ) : ℂ))).mul
          (measurable_i10KaH 0)).aestronglyMeasurable
    · have hr := mul_pos hq.2.1 (sub_pos.mpr hq.2.2)
      have hz := mul_pos hq.1.1 (sub_pos.mpr hq.1.2)
      unfold F
      rw [norm_mul]
      refine (mul_le_mul (norm_log_one_sub_div_two_le_rpow hq.2)
        (norm_i10KaH_le (by norm_num) hq) (norm_nonneg _) (by positivity)).trans_eq ?_
      rw [show (-(4 / 5) : ℝ) = -(1 / 4) + -(11 / 20) by norm_num, rpow_add hr]
      ring
  rw [IntegrableOn, volume_restrict_prod2] at hF
  change (∫ q in S ×ˢ S, F q) = _
  rw [volume_restrict_prod2, ← integral_prod_swap, integral_prod (fun q => F q.swap) hF.swap]
  rw [← integral_i10Ka_cubic_bubble, ← integral_complex_ofReal]
  apply setIntegral_congr_fun hS
  intro r hr
  let g := fun z : ℝ => ((log (1 - z * (1 - r)) - log (z * r)) / (1 - z) +
    (1 - z) * log (z * r) - z / r) / (z * (1 - z))
  have e : (∫ z in S, F (z, r)) = ∫ z in S, ((log (1 - r) ^ 2 / 2 * g z : ℝ) : ℂ) := by
    apply setIntegral_congr_fun hS
    intro z hz
    dsimp only [F, g, i10KaH]
    rw [i10D_zero hr.2, i10W, zero_sub, Complex.cpow_neg_one, i10KaB_zero hz hr]
    push_cast
    ring
  change (∫ z in S, F (z, r)) = _
  rw [e, integral_complex_ofReal, integral_const_mul]
  dsimp only [g, S]
  rw [integral_i10Ka_leading_join hr]

end QED.ThreeLoopE
