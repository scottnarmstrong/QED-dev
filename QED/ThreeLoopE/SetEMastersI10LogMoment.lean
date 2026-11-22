/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.ExtraIntegralsC
import QED.Polylog.Deriv
import QED.ThreeLoopE.SetEMastersI10KabVal
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# A regularized logarithmic moment for the second remainder of `I₁₀`

The subtraction of the linear term of the logarithm makes the moment
integrable at zero. An antiderivative in terms of the dilogarithm gives
the exact value.
-/

public section

open Real Set Filter Topology MeasureTheory QED.Polylog

namespace QED.ThreeLoopE

private noncomputable def i10LogMomentPrim (x : ℝ) : ℝ :=
  (log x + 1) * (-((1 - x) * log (1 - x)) / x - 1) + Li₂ x

private theorem hasDerivAt_i10LogMomentPrim {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i10LogMomentPrim (log x * (log (1 - x) + x) / x ^ 2) x := by
  have hc : 1 - x ≠ 0 := (sub_pos.mpr hx.2).ne'
  have hs : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id' x).const_sub 1
  have hp := (((hs.mul (hs.log hc)).neg.div (hasDerivAt_id' x) hx.1.ne').sub_const 1)
  have hd := ((((hasDerivAt_id' x).log hx.1.ne').add_const 1).mul hp).add
    (hasDerivAt_Li₂' hx)
  refine hd.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.neg_apply, Pi.div_apply]
  field_simp [hx.1.ne', hc]
  ring

private theorem tendsto_i10LogMomentPrim_zero :
    Tendsto i10LogMomentPrim (𝓝[>] 0) (𝓝 0) := by
  have hx : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hc := tendsto_const_nhds.sub hx (f := fun _ => (1 : ℝ))
  have hlog : Tendsto (fun x : ℝ => log (1 - x) / x) (𝓝[>] 0) (𝓝 (-1)) :=
    tendsto_log_one_sub_div_zero'
  have hp := ((hc.mul hlog).neg.sub tendsto_const_nhds (g := fun _ => (1 : ℝ)))
  have hprod : Tendsto (fun x : ℝ =>
      -(1 - x) * (log x * (log (1 - x) + x) / x) - x * log x) (𝓝[>] 0) (𝓝 0) := by
    convert (hc.neg.mul tendsto_log_mul_log_one_sub_add_div_zero).sub tendsto_mul_log_zero
      using 1
    norm_num
  have hli : Tendsto Li₂ (𝓝[>] 0) (𝓝 0) := by
    simpa only [Li₂_zero] using (hasDerivAt_Li₂_zero.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  have h := (hprod.add hp).add hli
  simp only [sub_zero, mul_neg, mul_one, neg_neg, sub_self, add_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  unfold i10LogMomentPrim
  field_simp [hx.ne']
  ring

private theorem tendsto_i10LogMomentPrim_one :
    Tendsto i10LogMomentPrim (𝓝[<] 1) (𝓝 (π ^ 2 / 6 - 1)) := by
  have hlog : Tendsto (fun x : ℝ => log x) (𝓝[<] 1) (𝓝 0) := by
    simpa only [log_one] using ((continuousAt_log one_ne_zero).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (1 : ℝ))))
  have hmul : Tendsto (fun x : ℝ => (1 - x) * log (1 - x)) (𝓝[<] 1) (𝓝 0) := by
    have hc : Continuous (fun x : ℝ => (1 - x) * log (1 - x)) :=
      continuous_mul_log.comp (continuous_const.sub continuous_id)
    have h := (hc.continuousAt (x := 1)).tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
    simpa only [sub_self, zero_mul] using h
  have hx : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h := ((hlog.add_const 1).mul
    ((hmul.neg.div hx one_ne_zero).sub_const 1)).add tendsto_Li₂_one_left
  unfold i10LogMomentPrim
  simpa only [Pi.div_apply, add_comm (π ^ 2 / 6), zero_add,
    neg_zero, zero_div, zero_sub, one_mul, sub_eq_add_neg] using h

/-- The moment of the quadratically vanishing logarithmic remainder. -/
theorem intervalIntegrable_and_integral_i10_logMulLogRemainder :
    IntervalIntegrable (fun x => log x * (log (1 - x) + x) / x ^ 2) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, log x * (log (1 - x) + x) / x ^ 2 = π ^ 2 / 6 - 1 := by
  have h := intervalIntegrable_and_integral_eq_of_nonneg
    (fun x hx => hasDerivAt_i10LogMomentPrim hx) (fun x hx => ?_)
    tendsto_i10LogMomentPrim_zero tendsto_i10LogMomentPrim_one
  · simpa only [sub_zero] using h
  · apply div_nonneg _ (sq_nonneg x)
    apply mul_nonneg_of_nonpos_of_nonpos (log_nonpos hx.1.le hx.2.le)
    have hc := log_le_sub_one_of_pos (sub_pos.mpr hx.2)
    linarith

private theorem integral_i10K2_logOneSubSq :
    IntervalIntegrable (fun x : ℝ => log (1 - x) ^ 2) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, log (1 - x) ^ 2 = 2 := by
  let F := fun x : ℝ => -(1 - x) * (log (1 - x) ^ 2 - 2 * log (1 - x) + 2)
  have hd {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt F (log (1 - x) ^ 2) x := by
    have hc := (sub_pos.mpr hx.2).ne'
    have hs := (hasDerivAt_id' x).const_sub (1 : ℝ)
    have hb := hs.log hc
    refine (hs.neg.mul (((hb.pow 2).sub (hb.const_mul 2)).add_const 2)).congr_deriv ?_
    simp only [Pi.neg_apply, Pi.sub_apply, Pi.pow_apply]
    field_simp [hc]
    ring
  have h0 : Tendsto F (𝓝[>] 0) (𝓝 (-2)) := by
    have hs : ContinuousAt (fun x : ℝ => 1 - x) 0 := continuous_const.sub continuous_id
      |>.continuousAt
    have hb := hs.log (by norm_num)
    have h : ContinuousAt F 0 :=
      hs.neg.mul (((hb.pow 2).sub (hb.const_mul 2)).add_const 2)
    have hv : F 0 = -2 := by norm_num [F]
    rw [← hv]
    exact h.tendsto.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto F (𝓝[<] 1) (𝓝 0) := by
    have hx : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have h := (tendsto_mul_log_sq_zero.neg.add (tendsto_mul_log_zero.const_mul 2)).sub
      (hx.const_mul 2)
    simp only [neg_zero, mul_zero, add_zero, sub_zero] at h
    exact (h.comp tendsto_one_sub_nhdsLT_one).congr fun x => by dsimp [F]; ring
  simpa only [zero_sub, neg_neg] using intervalIntegrable_and_integral_eq_of_nonneg
    (fun _ => hd) (fun x _ => sq_nonneg (log (1 - x))) h0 h1

private theorem integral_i10K2_logOneSubSqDivSq :
    IntervalIntegrable (fun x : ℝ => log (1 - x) ^ 2 / x ^ 2) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, log (1 - x) ^ 2 / x ^ 2 = π ^ 2 / 3 := by
  let F := fun x : ℝ => -((1 - x) * log (1 - x) ^ 2) / x + 2 * Li₂ x
  have hd {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt F (log (1 - x) ^ 2 / x ^ 2) x := by
    have hc := (sub_pos.mpr hx.2).ne'
    have hs := (hasDerivAt_id' x).const_sub (1 : ℝ)
    have hb := (hs.log hc).pow 2
    refine ((((hs.mul hb).neg.div (hasDerivAt_id' x) hx.1.ne').add
      ((hasDerivAt_Li₂' hx).const_mul 2))).congr_deriv ?_
    simp only [Pi.mul_apply, Pi.neg_apply, Pi.pow_apply]
    field_simp [hx.1.ne', hc]
    ring
  have hli : Tendsto Li₂ (𝓝[>] 0) (𝓝 0) := by
    simpa only [Li₂_zero] using (hasDerivAt_Li₂_zero.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h0 : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    have hs := tendsto_const_nhds.sub hx0 (f := fun _ => (1 : ℝ))
    have h := (((hs.mul hx0).mul (tendsto_log_one_sub_div_zero'.pow 2)).neg).add (hli.const_mul 2)
    simp only [mul_zero, zero_mul, neg_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    dsimp [F]
    field_simp [hx.ne']
  have hx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto F (𝓝[<] 1) (𝓝 (π ^ 2 / 3)) := by
    have h := ((tendsto_mul_log_sq_zero.comp tendsto_one_sub_nhdsLT_one).neg.div hx1
      one_ne_zero).add (tendsto_Li₂_one_left.const_mul 2)
    rw [neg_zero, zero_div, zero_add, show 2 * (π ^ 2 / 6) = π ^ 2 / 3 by ring] at h
    exact h.congr fun _ => rfl
  simpa only [sub_zero] using intervalIntegrable_and_integral_eq_of_nonneg
    (fun _ => hd) (fun x _ => div_nonneg (sq_nonneg _) (sq_nonneg x)) h0 h1

/-- The moment in the unweighted joining density applied to the first inner coefficient. -/
theorem integral_i10K2_linear_moment :
    let f := fun x : ℝ => (1 - x) * (log (1 - x) - log x) *
      (x + (1 - x) * log (1 - x)) / x ^ 2
    IntegrableOn f (Ioo 0 1) ∧ ∫ x in Ioo (0 : ℝ) 1, f x = 1 + π ^ 2 / 6 - 2 * zeta3 := by
  dsimp only
  obtain ⟨hA, vA⟩ := i10_ioo_of_interval intervalIntegrable_and_integral_log_one_sub_div
  obtain ⟨hB, vB⟩ := i10_ioo_of_interval integral_i10K2_logOneSubSqDivSq
  obtain ⟨hC, vC⟩ := i10_ioo_of_interval intervalIntegrable_and_integral_log_one_sub_sq_div
  obtain ⟨hD, vD⟩ := i10_ioo_of_interval integral_i10K2_logOneSubSq
  obtain ⟨hE, vE⟩ := i10_ioo_of_interval intervalIntegrable_and_integral_i10_logMulLogRemainder
  obtain ⟨hF, vF⟩ := i10_ioo_of_interval intervalIntegrable_and_integral_log_mul_log_one_sub_div
  obtain ⟨hG, vG⟩ := i10_ioo_of_interval intervalIntegrable_and_integral_log_mul_log_one_sub
  have hlog : IntervalIntegrable (fun x : ℝ => log x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, log x = -1 :=
    ⟨intervalIntegral.intervalIntegrable_log', by rw [integral_log]; simp⟩
  obtain ⟨hH, vH⟩ := i10_ioo_of_interval hlog
  have hL := i10_integrableOn_log_one_sub
  have vL := i10_integral_log_one_sub
  have hC2 := hC.const_mul 2
  have hF2 := hF.const_mul 2
  have hFound := ((((hA.sub hL).add hB).sub hC2).add hD).sub
    (((hE.sub hF2).add hG).sub hH)
  have he (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      (1 - x) * (log (1 - x) - log x) * (x + (1 - x) * log (1 - x)) / x ^ 2 =
        (((log (1 - x) / x - log (1 - x) + log (1 - x) ^ 2 / x ^ 2) -
          2 * (log (1 - x) ^ 2 / x)) + log (1 - x) ^ 2) -
        (((log x * (log (1 - x) + x) / x ^ 2 - 2 * (log x * log (1 - x) / x)) +
          log x * log (1 - x)) - log x) := by
    field_simp [hx.1.ne']
    ring
  refine ⟨hFound.congr_fun (fun x hx => (he x hx).symm) measurableSet_Ioo, ?_⟩
  calc
    _ = _ := setIntegral_congr_fun measurableSet_Ioo he
    _ = _ := by
      have e1 := integral_sub ((((hA.sub hL).add hB).sub hC2).add hD)
        (((hE.sub hF2).add hG).sub hH)
      have e2 := integral_add (((hA.sub hL).add hB).sub hC2) hD
      have e3 := integral_sub ((hA.sub hL).add hB) hC2
      have e4 := integral_add (hA.sub hL) hB
      have e5 := integral_sub ((hE.sub hF2).add hG) hH
      have e6 := integral_add (hE.sub hF2) hG
      simp only [Pi.add_apply, Pi.sub_apply] at e1 e2 e3 e4 e5 e6
      rw [e1, e2, e3, e4, e5, e6, integral_sub hA hL, integral_sub hE hF2]
      simp only [integral_const_mul, vA, vB, vC, vD, vE, vF, vG, vH, vL]
      ring

private theorem integral_i10K2_density_log :
    ∫ x in (0 : ℝ)..1, 2 * (1 - x) * (log (1 - x) - log x) = 1 := by
  have hA : IntervalIntegrable (fun x : ℝ => x * log x) volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'.continuousOn_mul continuousOn_id
  have hB : IntervalIntegrable (fun x : ℝ => (1 - x) * log x) volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'.continuousOn_mul
      (continuousOn_const.sub continuousOn_id)
  have hR := hA.symm.comp_sub_left 1
  simp only [sub_self, sub_zero] at hR
  have e : (fun x : ℝ => 2 * (1 - x) * (log (1 - x) - log x)) =
      fun x => 2 * ((1 - x) * log (1 - x) - (1 - x) * log x) := by
    funext x
    ring
  rw [e, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hR hB,
    intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x * log x) _]
  simp only [sub_self, sub_zero]
  rw [← intervalIntegral.integral_sub hA hB]
  let F := fun x : ℝ => (x ^ 2 - x) * log x - x ^ 2 / 2 + x
  have hD {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt F (x * log x - (1 - x) * log x) x := by
    have h := (hasDerivAt_id' x).pow 2
    refine (((h.sub (hasDerivAt_id' x)).mul (hasDerivAt_log hx.1.ne')).sub
      (h.div_const 2) |>.add (hasDerivAt_id' x)).congr_deriv ?_
    simp only [Pi.sub_apply, Pi.pow_apply]
    field_simp [hx.1.ne']
    ring
  have hx : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h0 : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    have h := ((((hx.sub_const 1).mul tendsto_mul_log_zero).sub
      ((hx.pow 2).div_const 2)).add hx)
    norm_num at h
    exact h.congr fun _ => by dsimp [F]; ring
  have h1 : Tendsto F (𝓝[<] 1) (𝓝 (1 / 2)) := by
    have hC : ContinuousAt F 1 :=
      ((((continuousAt_id.pow 2).sub continuousAt_id).mul (continuousAt_log one_ne_zero)).sub
        ((continuousAt_id.pow 2).div_const 2)).add continuousAt_id
    have hF : F 1 = 1 / 2 := by norm_num [F]
    rw [← hF]
    exact hC.tendsto.mono_left nhdsWithin_le_nhds
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun _ hx => hD hx) (hA.sub hB) h0 h1]
  norm_num

/-- The linear coefficient after transferring the derivative to the unweighted density. -/
theorem integral_i10K2_linear_density :
    let ψ := fun t : ℝ => -log t / 2 - 3 / 2 + 3 / (2 * t) +
      3 / 2 * ((1 - t) ^ 2 * log (1 - t)) / t ^ 2
    ∫ t in Ioo (0 : ℝ) 1, 2 * t * (1 - t) * (log (1 - t) - log t) * deriv ψ t =
      -5 - π ^ 2 + 12 * zeta3 := by
  let M := fun t : ℝ => (1 - t) * (log (1 - t) - log t) *
    (t + (1 - t) * log (1 - t)) / t ^ 2
  let ψ := fun t : ℝ => -log t / 2 - 3 / 2 + 3 / (2 * t) +
    3 / 2 * ((1 - t) ^ 2 * log (1 - t)) / t ^ 2
  have he {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
      2 * t * (1 - t) * (log (1 - t) - log t) * deriv ψ t =
        2 * (1 - t) * (log (1 - t) - log t) - 6 * M t := by
    have hc := (sub_pos.mpr ht.2).ne'
    have dt := hasDerivAt_id' t
    have dc := dt.const_sub (1 : ℝ)
    have h1 := (((hasDerivAt_log ht.1.ne').neg.div_const 2).sub_const (3 / 2)).add
      ((hasDerivAt_const t (3 : ℝ)).div (dt.const_mul 2)
        (mul_ne_zero two_ne_zero ht.1.ne'))
    have h2 := (((dc.pow 2).mul (dc.log hc)).const_mul (3 / 2)).div (dt.pow 2)
      (pow_ne_zero 2 ht.1.ne')
    have hψ : HasDerivAt ψ _ t := h1.add h2
    rw [hψ.deriv]
    simp only [M, Pi.pow_apply, Pi.mul_apply]
    field_simp [ht.1.ne', hc]
    ring
  have hL := intervalIntegral.intervalIntegrable_log'
    (a := (0 : ℝ)) (b := (1 : ℝ))
  have hR := hL.symm.comp_sub_left 1
  simp only [sub_self, sub_zero] at hR
  have hW : ContinuousOn (fun t : ℝ => 2 * (1 - t)) (uIcc 0 1) :=
    (continuousOn_const.mul (continuousOn_const.sub continuousOn_id))
  have hI := (hR.sub hL).continuousOn_mul hW
  obtain ⟨hI', hV⟩ := i10_ioo_of_interval ⟨hI, integral_i10K2_density_log⟩
  obtain ⟨hM, hMV⟩ := integral_i10K2_linear_moment
  dsimp only
  change (∫ t in Ioo (0 : ℝ) 1,
    2 * t * (1 - t) * (log (1 - t) - log t) * deriv ψ t) = _
  rw [setIntegral_congr_fun measurableSet_Ioo (fun _ ht => he ht)]
  rw [integral_sub hI' (hM.const_mul 6), integral_const_mul, hV, hMV]
  ring

end QED.ThreeLoopE
