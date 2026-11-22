/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI10Asm
public import QED.ThreeLoopE.SetEMastersI10K2Weighted
import QED.ThreeLoopE.SetEMastersI10K2Linear
import QED.ThreeLoopE.SetEMastersI10K2Radial
import QED.Polylog.ParamHPLLog
import QED.Polylog.Reflection
import QED.Polylog.Deriv
import QED.Polylog.LiCalculus
import QED.Polylog.ExtraIntegralsC
import Mathlib.Analysis.Calculus.LHopital

/-!
# The quadratic coefficient of the second I10 remainder

Fubini transfers the integral over the ordered bubble parameters to an integral
over the cut. A sum of squared logarithms bounds the integrand absolutely.
The bubble moments and radial joining integral give the density evaluated
by the harmonic polylogarithm primitive in `SetEMastersI10K2Weighted`.
See `scripts/numerics/three_loop_masters/i10coefficients.py` for numerical checks.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog

namespace QED.ThreeLoopE

/-! ## Endpoint bounds for the quadratic moment -/

private theorem tendsto_cut_zero : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
  tendsto_id.mono_left nhdsWithin_le_nhds

private noncomputable def logRemainder (x : ℝ) : ℝ := (log (1 - x) + x) / x ^ 2

private noncomputable def dilogRemainder (x : ℝ) : ℝ := (Li₂ x - x) / x ^ 2

private theorem hasDerivAt_cut_sq (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x :=
  ((hasDerivAt_id' x).pow 2).congr_deriv (by simp)

private theorem tendsto_logRemainder_zero :
    Tendsto logRemainder (𝓝[>] 0) (𝓝 (-(1 / 2))) := by
  have hN : Tendsto (fun x => log (1 - x) + x) (𝓝[>] 0) (𝓝 0) := by
    simpa only [add_zero] using tendsto_log_one_sub_zero.add tendsto_cut_zero
  have hC : Tendsto (fun x : ℝ => 2 * (1 - x)) (𝓝[>] 0) (𝓝 2) := by
    simpa only [sub_zero, mul_one] using (tendsto_cut_zero.const_sub 1).const_mul 2
  have hV : Tendsto (fun x : ℝ => (-(1 - x)⁻¹ + 1) / (2 * x)) (𝓝[>] 0)
      (𝓝 (-(1 / 2))) := by
    have h := (tendsto_const_nhds (x := (-1 : ℝ))).div hC two_ne_zero
    rw [show (-1 : ℝ) / 2 = -(1 / 2) by norm_num] at h
    refine h.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with x hx
    change (-1 : ℝ) / (2 * (1 - x)) = _
    field_simp [hx.1.ne', (sub_pos.mpr hx.2).ne']
    ring
  exact HasDerivAt.lhopital_zero_right_on_Ioo zero_lt_one
    (fun x hx => ((((hasDerivAt_id' x).const_sub 1).log (sub_pos.mpr hx.2).ne').add
      (hasDerivAt_id' x)).congr_deriv (by ring))
    (fun x _ => hasDerivAt_cut_sq x) (fun x hx => mul_ne_zero two_ne_zero hx.1.ne') hN
    (by simpa only [zero_pow two_ne_zero] using tendsto_cut_zero.pow 2) hV

private theorem tendsto_dilogRemainder_zero :
    Tendsto dilogRemainder (𝓝[>] 0) (𝓝 (1 / 4)) := by
  have hN : Tendsto (fun x => Li₂ x - x) (𝓝[>] 0) (𝓝 0) := by
    have h := hasDerivAt_Li₂_zero.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [Li₂_zero] at h
    simpa only [sub_zero] using h.sub tendsto_cut_zero
  have hV : Tendsto (fun x : ℝ => (-log (1 - x) / x - 1) / (2 * x)) (𝓝[>] 0)
      (𝓝 (1 / 4)) := by
    have h := tendsto_logRemainder_zero.const_mul (-(1 / 2))
    rw [show -(1 / 2 : ℝ) * -(1 / 2) = 1 / 4 by norm_num] at h
    refine h.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with x hx
    unfold logRemainder
    field_simp [hx.1.ne']
    ring
  exact HasDerivAt.lhopital_zero_right_on_Ioo zero_lt_one
    (fun _ hx => (hasDerivAt_Li₂' hx).sub (hasDerivAt_id' _))
    (fun x _ => hasDerivAt_cut_sq x) (fun x hx => mul_ne_zero two_ne_zero hx.1.ne') hN
    (by simpa only [zero_pow two_ne_zero] using tendsto_cut_zero.pow 2) hV

private theorem exists_abs_bound_of_endpoint_limits {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Ioo 0 1))
    (ha : Tendsto f (𝓝[>] 0) (𝓝 a)) (hb : Tendsto f (𝓝[<] 1) (𝓝 b)) :
    ∃ C, ∀ t ∈ Ioo (0 : ℝ) 1, |f t| ≤ C := by
  have h := continuousOn_Icc_extendFrom_Ioo hf ha hb
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn h
  refine ⟨C, fun t ht => ?_⟩
  simpa only [extendFrom_extends hf t ht, Real.norm_eq_abs] using
    hC t (Ioo_subset_Icc_self ht)

private noncomputable def scaledLogRemainder (t : ℝ) : ℝ :=
  (1 - t) * logRemainder t

private noncomputable def scaledLogRemainderSq (t : ℝ) : ℝ :=
  (1 - t) * t ^ 2 * logRemainder t ^ 2

private noncomputable def scaledDilogRemainder (t : ℝ) : ℝ :=
  (1 - t) * dilogRemainder t

private theorem scaled_remainders_one :
    Tendsto scaledLogRemainder (𝓝[<] 1) (𝓝 0) ∧
    Tendsto scaledLogRemainderSq (𝓝[<] 1) (𝓝 0) ∧
    Tendsto scaledDilogRemainder (𝓝[<] 1) (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t) (𝓝[<] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h10 : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] 1) (𝓝 0) := by
    simpa only [sub_self] using h1.const_sub 1
  have hl := tendsto_mul_log_zero.comp tendsto_one_sub_nhdsLT_one
  have hll := tendsto_mul_log_sq_zero.comp tendsto_one_sub_nhdsLT_one
  have hE₁ : Tendsto scaledLogRemainder (𝓝[<] 1) (𝓝 0) := by
    have h := (hl.add (h10.mul h1)).div (h1.pow 2) (by norm_num)
    simp only [zero_mul, add_zero, one_pow, zero_div] at h
    refine h.congr fun t => ?_
    simp only [scaledLogRemainder, logRemainder, Function.comp_apply, Pi.div_apply,
      ← mul_add, mul_div_assoc]
  have hF₁ : Tendsto scaledLogRemainderSq (𝓝[<] 1) (𝓝 0) := by
    have h := ((hll.add ((hl.mul h1).const_mul 2)).add
      (h10.mul (h1.pow 2))).div (h1.pow 2) (by norm_num)
    simp only [zero_mul, mul_zero, add_zero, one_pow, zero_div] at h
    refine h.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    simp only [scaledLogRemainderSq, logRemainder, Function.comp_apply, Pi.div_apply]
    field_simp [ht.1.ne']
    ring
  have hG₁ : Tendsto scaledDilogRemainder (𝓝[<] 1) (𝓝 0) := by
    have h := h10.mul ((tendsto_Li₂_one_left.sub h1).div (h1.pow 2) (by norm_num))
    change Tendsto (fun t => (1 - t) * ((Li₂ t - t) / t ^ 2)) (𝓝[<] 1) (𝓝 0)
    simpa only [zero_mul, Pi.div_apply] using h
  exact ⟨hE₁, hF₁, hG₁⟩

private theorem continuousOn_logRemainder : ContinuousOn logRemainder (Ioo 0 1) := by
  intro t ht
  have h₀ := pow_ne_zero 2 ht.1.ne'
  have hc := (sub_pos.mpr ht.2).ne'
  apply ContinuousAt.continuousWithinAt
  unfold logRemainder
  fun_prop

private theorem continuousOn_dilogRemainder : ContinuousOn dilogRemainder (Ioo 0 1) := by
  intro t ht
  have h₀ := pow_ne_zero 2 ht.1.ne'
  have hU := (hasDerivAt_Li₂' ht).continuousAt
  apply ContinuousAt.continuousWithinAt
  unfold dilogRemainder
  fun_prop

private theorem scaled_remainders_bounded :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioo (0 : ℝ) 1,
      |scaledLogRemainder t| ≤ C ∧ |scaledLogRemainderSq t| ≤ C ∧
        |scaledDilogRemainder t| ≤ C := by
  have hc : ContinuousOn (fun t : ℝ => 1 - t) (Ioo 0 1) :=
    continuousOn_const.sub continuousOn_id
  have ht : ContinuousOn (fun t : ℝ => t) (Ioo 0 1) := continuousOn_id
  have hE : ContinuousOn scaledLogRemainder (Ioo 0 1) := hc.mul continuousOn_logRemainder
  have hF : ContinuousOn scaledLogRemainderSq (Ioo 0 1) :=
    (hc.mul (ht.pow 2)).mul (continuousOn_logRemainder.pow 2)
  have hG : ContinuousOn scaledDilogRemainder (Ioo 0 1) := hc.mul continuousOn_dilogRemainder
  have h0 := tendsto_cut_zero
  have h01 := h0.const_sub 1
  have hE₀ : Tendsto scaledLogRemainder (𝓝[>] 0) (𝓝 (-(1 / 2))) := by
    unfold scaledLogRemainder
    simpa only [sub_zero, one_mul] using h01.mul tendsto_logRemainder_zero
  have hF₀ : Tendsto scaledLogRemainderSq (𝓝[>] 0) (𝓝 0) := by
    unfold scaledLogRemainderSq
    simpa only [sub_zero, zero_pow two_ne_zero, mul_zero, zero_mul] using
      (h01.mul (h0.pow 2)).mul (tendsto_logRemainder_zero.pow 2)
  have hG₀ : Tendsto scaledDilogRemainder (𝓝[>] 0) (𝓝 (1 / 4)) := by
    unfold scaledDilogRemainder
    simpa only [sub_zero, one_mul] using h01.mul tendsto_dilogRemainder_zero
  obtain ⟨hE₁, hF₁, hG₁⟩ := scaled_remainders_one
  obtain ⟨A, hA⟩ := exists_abs_bound_of_endpoint_limits hE hE₀ hE₁
  obtain ⟨B, hB⟩ := exists_abs_bound_of_endpoint_limits hF hF₀ hF₁
  obtain ⟨D, hD⟩ := exists_abs_bound_of_endpoint_limits hG hG₀ hG₁
  refine ⟨max 0 (max A (max B D)), le_max_left _ _, fun t ht => ⟨?_, ?_, ?_⟩⟩
  · exact (hA t ht).trans (le_max_left _ _ |>.trans (le_max_right _ _))
  · exact (hB t ht).trans (le_max_left _ _ |>.trans
      (le_max_right _ _ |>.trans (le_max_right _ _)))
  · exact (hD t ht).trans (le_max_right _ _ |>.trans
      (le_max_right _ _ |>.trans (le_max_right _ _)))

private theorem scaled_derivative_bound {t E F G l C : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C)
    (hE : |E| ≤ C) (hF : |F| ≤ C) (hG : |G| ≤ C) :
    |(-2 - 3 * E) * l + (6 * F - 3 * (3 * t + 2) * E + 3 * G - 3 * (t + 1))| ≤
      (6 + 24 * C) * (1 + |l|) := by
  have hA : |(-2 : ℝ) - 3 * E| ≤ 2 + 3 * C := by
    calc
      _ ≤ |-2| + |3 * E| := abs_sub _ _
      _ = 2 + 3 * |E| := by rw [abs_mul]; norm_num
      _ ≤ _ := by linarith
  have ht0 := ht.1
  have hM : |3 * (3 * t + 2) * E| ≤ 15 * C := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_left hE (by positivity)).trans
      (mul_le_mul_of_nonneg_right (by linarith [ht.2]) hC)
  have hB : |6 * F - 3 * (3 * t + 2) * E + 3 * G - 3 * (t + 1)| ≤ 6 + 24 * C := by
    calc
      _ ≤ ((|6 * F| + |3 * (3 * t + 2) * E|) + |3 * G|) + |3 * (t + 1)| :=
        (abs_sub _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
      _ = ((6 * |F| + |3 * (3 * t + 2) * E|) + 3 * |G|) + 3 * (t + 1) := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 3 * (t + 1)), abs_mul 6 F, abs_mul 3 G]
        norm_num
      _ ≤ _ := by linarith [ht.2]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul ((-2 : ℝ) - 3 * E) l, mul_add (6 + 24 * C), mul_one,
    add_comm (6 + 24 * C)]
  exact add_le_add (mul_le_mul_of_nonneg_right (hA.trans (by linarith)) (abs_nonneg _)) hB

private theorem abs_i10K2PsiTwoDeriv_le :
    ∃ C > (0 : ℝ), ∀ t ∈ Ioo (0 : ℝ) 1,
      |i10K2PsiTwoDeriv t| ≤ C * (1 + |log t|) / t := by
  obtain ⟨C, hC, h⟩ := scaled_remainders_bounded
  refine ⟨6 + 24 * C, by positivity, fun t ht => (le_div_iff₀ ht.1).2 ?_⟩
  obtain ⟨hE, hF, hG⟩ := h t ht
  have hnorm : |i10K2PsiTwoDeriv t| * t = |t * i10K2PsiTwoDeriv t| := by
    rw [abs_mul, abs_of_pos ht.1, mul_comm]
  rw [hnorm]
  have he : t * i10K2PsiTwoDeriv t =
      (-2 - 3 * scaledLogRemainder t) * log t +
      (6 * scaledLogRemainderSq t - 3 * (3 * t + 2) * scaledLogRemainder t +
        3 * scaledDilogRemainder t - 3 * (t + 1)) := i10K2PsiTwoDeriv_scaled ht
  rw [he]
  exact scaled_derivative_bound ht hC hE hF hG


/-! ## Bubble-log moments -/

private noncomputable def bubbleLanden (y : ℝ) : ℝ :=
  Li₂ y + log (1 - y) ^ 2 / 2

private theorem hasDerivAt_bubbleLanden {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt bubbleLanden (-log (1 - y) / (y * (1 - y))) y := by
  have hc := (sub_pos.mpr hy.2).ne'
  have h := (((hasDerivAt_id' y).const_sub 1).log hc).pow 2
  refine ((hasDerivAt_Li₂' hy).add (h.div_const 2)).congr_deriv ?_
  field_simp [hy.1.ne', hc]
  ring

private theorem hasDerivAt_bubbleLanden_comp {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    HasDerivAt (fun x => bubbleLanden (x / (c + x)))
      ((log (c + a) - log c) / a) a := by
  have hp := add_pos hc ha
  have hy : a / (c + a) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos ha hp, (div_lt_one hp).2 (by linarith)⟩
  have hn := hasDerivAt_id' a
  have hd := (hasDerivAt_bubbleLanden hy).comp a (hn.div (hn.const_add c) hp.ne')
  refine hd.congr_deriv ?_
  rw [show 1 - a / (c + a) = c / (c + a) by field_simp; ring, log_div hc.ne' hp.ne']
  field_simp [hc.ne', ha.ne', hp.ne']
  ring

private noncomputable def bubbleLogPrimitive (c a : ℝ) : ℝ :=
  -(log (c + a) * (a * (log a - 1))) + a * (log a - 2) -
    c * ((log a - 1) * (log (c + a) - log c) - bubbleLanden (a / (c + a)))

private theorem hasDerivAt_bubbleLogPrimitive {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    HasDerivAt (bubbleLogPrimitive c) (-log (c + a) * log a) a := by
  have hp := add_pos hc ha
  have dx := hasDerivAt_id' a
  have dl := hasDerivAt_log ha.ne'
  have dk := (dx.const_add c).log hp.ne'
  have h₁ := (dk.mul (dx.mul (dl.sub_const 1))).neg
  have h₂ := dx.mul (dl.sub_const 2)
  have h₃ := ((dl.sub_const 1).mul (dk.sub_const (log c))).sub
    (hasDerivAt_bubbleLanden_comp hc ha)
  refine ((h₁.add h₂).sub (h₃.const_mul c)).congr_deriv ?_
  simp only [Pi.mul_apply]
  field_simp [ha.ne', hp.ne']
  ring

private theorem tendsto_bubbleLanden_comp_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun a => bubbleLanden (a / (c + a))) (𝓝[>] 0) (𝓝 0) := by
  have hL : ContinuousAt bubbleLanden 0 := by
    unfold bubbleLanden
    refine hasDerivAt_Li₂_zero.continuousAt.add ?_
    exact (((hasDerivAt_id' (0 : ℝ)).const_sub 1).log (by norm_num)).continuousAt.pow 2
      |>.div_const 2
  have hq : ContinuousAt (fun a : ℝ => a / (c + a)) 0 :=
    continuousAt_id.div (continuousAt_const.add continuousAt_id) (by simpa using hc.ne')
  have h := (hL.comp_of_eq hq (by simp)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  change Tendsto (bubbleLanden ∘ fun a : ℝ => a / (c + a)) (𝓝[>] 0) (𝓝 0)
  simpa only [Function.comp_apply, bubbleLanden, sub_zero, log_one, Li₂_zero,
    zero_pow two_ne_zero, zero_div, add_zero] using h

private theorem tendsto_bubbleLogPrimitive_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (bubbleLogPrimitive c) (𝓝[>] 0) (𝓝 0) := by
  have dk := ((hasDerivAt_id' (0 : ℝ)).const_add c).log (by simpa using hc.ne')
  have hk : Tendsto (fun a : ℝ => log (c + a)) (𝓝[>] 0) (𝓝 (log c)) := by
    simpa only [add_zero] using dk.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hs : Tendsto (fun a : ℝ => (log (c + a) - log c) / a) (𝓝[>] 0) (𝓝 c⁻¹) := by
    have h := dk.tendsto_slope_zero_right
    simpa only [add_zero, zero_add, one_mul, mul_one, smul_eq_mul, div_eq_inv_mul, one_div] using h
  have hl (k : ℝ) : Tendsto (fun a : ℝ => a * (log a - k)) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_mul_log_zero.sub (tendsto_cut_zero.mul_const k)
    simpa only [zero_mul, sub_zero, mul_sub] using h
  have hpro : Tendsto (fun a : ℝ => (log a - 1) * (log (c + a) - log c))
      (𝓝[>] 0) (𝓝 0) := by
    have h := (hl 1).mul hs
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha0 : 0 < a := ha
    field_simp [ha0.ne']
  have h := ((hk.mul (hl 1)).neg.add (hl 2)).sub
    ((hpro.sub (tendsto_bubbleLanden_comp_zero hc)).const_mul c)
  unfold bubbleLogPrimitive
  simpa only [mul_zero, neg_zero, add_zero, sub_zero] using h

private theorem bubble_log_left_integrable {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun a => -log (1 - t + a) * log a) volume 0 t := by
  have hc : 0 < 1 - t := sub_pos.mpr ht.2
  have h : ContinuousOn (fun a => -log (1 - t + a)) (uIcc 0 t) := by
    rw [uIcc_of_le ht.1.le]
    intro a ha
    exact (((hasDerivAt_id' a).const_add (1-t)).log (add_pos_of_pos_of_nonneg hc ha.1).ne'
      ).neg.continuousAt.continuousWithinAt
  exact intervalIntegral.intervalIntegrable_log'.continuousOn_mul h

private theorem bubble_log_left_moment {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ a in 0..t, -log (1 - t + a) * log a) =
      t * (log t - 2) + (1 - t) * log (1 - t) * (log t - 1) +
        (1 - t) * (Li₂ t + log (1 - t) ^ 2 / 2) := by
  have hc := sub_pos.mpr ht.2
  have hR := (hasDerivAt_bubbleLogPrimitive hc ht.1).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := Iio t))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht.1
    (fun a ha => hasDerivAt_bubbleLogPrimitive hc ha.1) (bubble_log_left_integrable ht)
    (tendsto_bubbleLogPrimitive_zero hc) hR]
  simp only [bubbleLogPrimitive, bubbleLanden, sub_add_cancel, log_one, div_one, zero_mul,
    neg_zero, zero_add, sub_zero]
  ring

private theorem bubble_log_left_mass (t : ℝ) :
    (∫ a in 0..t, -log (1 - t + a)) = t + (1 - t) * log (1 - t) := by
  rw [intervalIntegral.integral_neg]
  simp_rw [add_comm (1 - t)]
  rw [intervalIntegral.integral_comp_add_right, zero_add, add_sub_cancel]
  rw [integral_log]
  simp only [log_one, mul_zero]
  ring

private theorem bubble_log_right_mass {c : ℝ} (hc : 0 < c) :
    (∫ b in 0..c, -log (c - b)) = c * (1 - log c) := by
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left, sub_self,
    sub_zero, integral_log_from_zero_of_pos hc]
  ring

private theorem bubble_log_right_scaled {c y : ℝ} (hc : 0 < c) (hy : y ∈ Ioo (0 : ℝ) 1) :
    -log (c - c * y) * log (c * y) =
      -(log c)^2 - log c * log y - log c * log (1 - y) - log y * log (1 - y) := by
  rw [show c - c * y = c * (1 - y) by ring, log_mul hc.ne' hy.1.ne',
    log_mul hc.ne' (sub_pos.mpr hy.2).ne']
  ring

private theorem bubble_log_right_terms (c : ℝ) :
    IntervalIntegrable (fun y : ℝ =>
      -(log c)^2 - log c * log y - log c * log (1 - y) - log y * log (1 - y)) volume 0 1 := by
  have hl : IntervalIntegrable log volume (0 : ℝ) 1 := intervalIntegral.intervalIntegrable_log'
  have hr := hl.symm.comp_sub_left 1
  simp only [sub_self, sub_zero] at hr
  exact ((intervalIntegrable_const.sub (hl.const_mul _)).sub (hr.const_mul _)).sub
    intervalIntegrable_and_integral_log_mul_log_one_sub.1

private theorem bubble_log_right_integrable {c : ℝ} (hc : 0 < c) :
    IntervalIntegrable (fun b => -log (c - b) * log b) volume 0 c := by
  have h := (bubble_log_right_terms c).congr_uIoo (g := fun y : ℝ =>
    -log (c - c * y) * log (c * y)) (by
      intro y hy
      rw [uIoo_of_le zero_le_one] at hy
      exact (bubble_log_right_scaled hc hy).symm)
  have hi := h.comp_mul_left (c := c⁻¹)
  simpa only [zero_div, one_div, inv_inv, mul_inv_cancel_left₀ hc.ne', mul_assoc] using hi

private theorem bubble_log_right_moment {c : ℝ} (hc : 0 < c) :
    (∫ b in 0..c, -log (c - b) * log b) =
      -c * (log c ^ 2 - 2 * log c + 2 - π ^ 2 / 6) := by
  let f := fun b => -log (c - b) * log b
  have h := intervalIntegral.mul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (c := c) (f := f)
  simp only [mul_zero, mul_one] at h
  change (∫ b in 0..c, f b) = _
  rw [← h]
  have hl : IntervalIntegrable log volume (0 : ℝ) 1 := intervalIntegral.intervalIntegrable_log'
  have hr := hl.symm.comp_sub_left 1
  simp only [sub_self, sub_zero] at hr
  have e : (∫ y in (0 : ℝ)..1, log (1 - y)) = -1 := by
    rw [intervalIntegral.integral_comp_sub_left, sub_self, sub_zero,
      integral_log_from_zero_of_pos zero_lt_one]
    simp
  have e' : (∫ y in (0 : ℝ)..1, log y) = -1 := by
    rw [integral_log_from_zero_of_pos zero_lt_one]
    simp
  rw [neg_mul, neg_mul_eq_mul_neg]
  apply congrArg (c * ·)
  calc
    (∫ y in (0 : ℝ)..1, f (c * y)) =
          ∫ y in (0 : ℝ)..1,
            -(log c)^2 - log c * log y - log c * log (1 - y) - log y * log (1 - y) := by
        apply intervalIntegral.integral_congr_uIoo
        intro y hy
        rw [uIoo_of_le zero_le_one] at hy
        exact bubble_log_right_scaled hc hy
      _ = _ := by
        have h₀ : IntervalIntegrable (fun _ => -(log c)^2) volume (0 : ℝ) 1 :=
          intervalIntegrable_const
        have h₁ := hl.const_mul (log c)
        have h₂ := hr.const_mul (log c)
        rw [intervalIntegral.integral_sub ((h₀.sub h₁).sub h₂)
          intervalIntegrable_and_integral_log_mul_log_one_sub.1,
          intervalIntegral.integral_sub (h₀.sub h₁) h₂,
          intervalIntegral.integral_sub h₀ h₁, intervalIntegral.integral_const,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, e, e',
          intervalIntegrable_and_integral_log_mul_log_one_sub.2]
        simp only [sub_zero, smul_eq_mul, one_mul]
        ring

/-! ## Densities on the cut rectangle -/

private abbrev unitInterval : Set ℝ := Ioo 0 1

private def cutRectangle (t : ℝ) : Set (ℝ × ℝ) := Ioo t 1 ×ˢ Ioo 0 t

private def cutRegion : Set (ℝ × (ℝ × ℝ)) := {q | q.2 ∈ cutRectangle q.1}

private theorem measurableSet_cutRegion : MeasurableSet cutRegion := by
  change MeasurableSet
    ({q : ℝ × (ℝ × ℝ) | q.1 < q.2.1} ∩ {q | q.2.1 < 1} ∩
      ({q | 0 < q.2.2} ∩ {q | q.2.2 < q.1}))
  exact ((measurableSet_lt measurable_fst measurable_snd.fst).inter
    (measurableSet_lt measurable_snd.fst measurable_const)).inter
    ((measurableSet_lt measurable_const measurable_snd.snd).inter
      (measurableSet_lt measurable_snd.snd measurable_fst))

private theorem cut_rectangle_integral {t : ℝ} (ht : t ∈ unitInterval)
    {f : ℝ × ℝ → ℝ} (hf : IntegrableOn f (cutRectangle t)) :
    (∫ p in cutRectangle t, f p) =
      ∫ a in (0 : ℝ)..t, ∫ b in (0 : ℝ)..(1 - t), f (b + t, t - a) := by
  have hi : Integrable f ((volume.restrict (Ioo t 1)).prod (volume.restrict (Ioo 0 t))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hf
  unfold cutRectangle
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ hi,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.1.le]
  simp_rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.2.le]
  symm
  let G := fun s => ∫ b in (0 : ℝ)..(1 - t), f (b + t, s)
  change (∫ a in (0 : ℝ)..t, G (t - a)) = _
  rw [intervalIntegral.integral_comp_sub_left, sub_self, sub_zero]
  apply intervalIntegral.integral_congr
  intro s _
  let H := fun b => f (b, s)
  change (∫ b in (0 : ℝ)..(1 - t), H (b + t)) = _
  rw [intervalIntegral.integral_comp_add_right, zero_add, sub_add_cancel]


private theorem integrableOn_cut_product {t : ℝ} {f g : ℝ → ℝ}
    (hf : IntegrableOn f (Ioo t 1)) (hg : IntegrableOn g (Ioo 0 t)) :
    IntegrableOn (fun p : ℝ × ℝ => f p.1 * g p.2) (cutRectangle t) := by
  rw [IntegrableOn, cutRectangle, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact hf.mul_prod hg

private theorem integrableOn_cut_fst {t : ℝ} {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioo t 1)) :
    IntegrableOn (fun p : ℝ × ℝ => f p.1) (cutRectangle t) := by
  have h := integrableOn_cut_product hf
    (integrableOn_const (C := (1 : ℝ)) measure_Ioo_lt_top.ne :
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 t))
  exact h.congr (ae_of_all _ fun p => mul_one (f p.1))

private theorem integrableOn_cut_snd {t : ℝ} {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioo 0 t)) :
    IntegrableOn (fun p : ℝ × ℝ => f p.2) (cutRectangle t) := by
  have h := integrableOn_cut_product
    (integrableOn_const (C := (1 : ℝ)) measure_Ioo_lt_top.ne :
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo t 1)) hf
  exact h.congr (ae_of_all _ fun p => one_mul (f p.2))

private noncomputable def cutBubble (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  (-log (1 - p.1) - log (1 - p.2)) * (log (p.1 - t) - log (t - p.2))

private theorem bubble_log_left_weight_integrable {t : ℝ} (ht : t ∈ unitInterval) :
    IntervalIntegrable (fun a => -log (1 - t + a)) volume 0 t := by
  have hc := sub_pos.mpr ht.2
  have h : ContinuousOn (fun a => -log (1 - t + a)) (uIcc 0 t) := by
    rw [uIcc_of_le ht.1.le]
    intro a ha
    exact (((hasDerivAt_id' a).const_add (1 - t)).log (add_pos_of_pos_of_nonneg hc ha.1).ne'
      ).neg.continuousAt.continuousWithinAt
  exact h.intervalIntegrable

private theorem integral_cutBubble {t : ℝ} (ht : t ∈ unitInterval)
    (hi : IntegrableOn (cutBubble t) (cutRectangle t)) :
    let c := 1 - t
    (∫ p in cutRectangle t, cutBubble t p) =
      c * (log c - 1) * (t + c * log c) -
      c * (t * (log t - 2) + c * log c * (log t - 1) +
        c * (Li₂ t + log c ^ 2 / 2)) -
      t * (c * (log c ^ 2 - 2 * log c + 2 - π ^ 2 / 6)) -
      t * (log t - 1) * (c * (1 - log c)) := by
  dsimp only
  rw [cut_rectangle_integral ht hi]
  let c := 1 - t
  have hc : 0 < c := sub_pos.mpr ht.2
  have hL : IntervalIntegrable log volume (0 : ℝ) c := intervalIntegral.intervalIntegrable_log'
  have hR : IntervalIntegrable (fun b => -log (c - b)) volume 0 c := by
    have h := hL.symm.comp_sub_left c
    simp only [sub_self, sub_zero] at h
    exact h.neg
  have hb (a : ℝ) :
      (∫ b in 0..c, cutBubble t (b + t, t - a)) =
        ((c * (log c - 1)) * (-log (c + a)) - c * (-log (c + a) * log a)) -
        c * (log c ^ 2 - 2 * log c + 2 - π ^ 2 / 6) -
        (c * (1 - log c)) * log a := by
    calc
      _ = ∫ b in 0..c, ((-log (c + a)) * log b - (-log (c + a) * log a)) +
          (-log (c - b) * log b) - (-log (c - b)) * log a := by
        apply intervalIntegral.integral_congr
        intro b _
        simp only [cutBubble, add_sub_cancel_right, sub_sub_cancel]
        rw [show 1 - (b + t) = c - b by dsimp [c]; ring,
          show 1 - (t - a) = c + a by dsimp [c]; ring]
        ring
      _ = _ := by
        have h₁ := hL.const_mul (-log (c + a))
        have h₂ : IntervalIntegrable (fun _ => -log (c + a) * log a) volume 0 c :=
          intervalIntegrable_const
        have h₃ := bubble_log_right_integrable hc
        rw [intervalIntegral.integral_sub ((h₁.sub h₂).add h₃) (hR.mul_const _),
          intervalIntegral.integral_add (h₁.sub h₂) h₃, intervalIntegral.integral_sub h₁ h₂,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
          intervalIntegral.integral_mul_const, bubble_log_right_moment hc,
          bubble_log_right_mass hc, integral_log_from_zero_of_pos hc]
        simp only [sub_zero, smul_eq_mul]
        ring
  change (∫ a in 0..t, ∫ b in 0..c, cutBubble t (b + t, t - a)) = _
  simp_rw [hb]
  have h₁ := (bubble_log_left_weight_integrable ht).const_mul (c * (log c - 1))
  have h₂ := (bubble_log_left_integrable ht).const_mul c
  have h₃ : IntervalIntegrable (fun _ => c * (log c ^ 2 - 2 * log c + 2 - π ^ 2 / 6))
      volume 0 t := intervalIntegrable_const
  have h₄ := (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := t)).const_mul
    (c * (1 - log c))
  rw [intervalIntegral.integral_sub ((h₁.sub h₂).sub h₃) h₄,
    intervalIntegral.integral_sub (h₁.sub h₂) h₃, intervalIntegral.integral_sub h₁ h₂,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    bubble_log_left_mass, bubble_log_left_moment ht,
    intervalIntegral.integral_const_mul (c * (1 - log c)) log,
    integral_log_from_zero_of_pos ht.1]
  simp only [sub_zero, smul_eq_mul, c]
  ring

private theorem integral_cutJoin {t : ℝ} (ht : t ∈ unitInterval)
    (hi : IntegrableOn (fun p : ℝ × ℝ => i10K2JoinLog ((t - p.2) / (p.1 - p.2)))
      (cutRectangle t)) :
    2 * (∫ p in cutRectangle t, i10K2JoinLog ((t - p.2) / (p.1 - p.2))) =
      t ^ 2 * (1 - i10K2JoinLogRadialPrim t) -
        (1 - t) ^ 2 * (1 - i10K2JoinLogRadialPrim (1 - t)) := by
  rw [← integral_i10K2JoinLog_rectangle ht, cut_rectangle_integral ht hi]
  congr 1
  have h := integrableOn_i10K2JoinLog_rectangle t
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ h,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.1.le]
  simp_rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le
    (sub_nonneg.mpr ht.2.le)]
  apply intervalIntegral.integral_congr
  intro a _
  apply intervalIntegral.integral_congr
  intro b _
  change i10K2JoinLog ((t - (t - a)) / (b + t - (t - a))) = _
  rw [sub_sub_cancel, show b + t - (t - a) = a + b by ring]

private theorem bubble_radial_density {t : ℝ} (ht : t ∈ unitInterval) :
    let c := 1 - t
    t ^ 2 * (1 - i10K2JoinLogRadialPrim t) -
        c ^ 2 * (1 - i10K2JoinLogRadialPrim c) +
      2 * (c * (log c - 1) * (t + c * log c) -
        c * (t * (log t - 2) + c * log c * (log t - 1) +
          c * (Li₂ t + log c ^ 2 / 2)) -
        t * (c * (log c ^ 2 - 2 * log c + 2 - π ^ 2 / 6)) -
        t * (log t - 1) * (c * (1 - log c))) = i10K2DensityTwo t := by
  have hc := sub_pos.mpr ht.2
  have h := Li₂_add_Li₂_one_sub ht.1.le ht.2.le
  have e : Li₂ (1 - t) = π ^ 2 / 6 - Li₂ t - log t * log (1 - t) := by linarith
  simp only [i10K2JoinLogRadialPrim, i10K2JoinLog, i10K2DensityTwo, sub_sub_cancel, e]
  field_simp [ht.1.ne', hc.ne']
  ring


/-! ## Absolute integrability on the ordered region -/

private noncomputable def logSqPrim (x : ℝ) : ℝ :=
  x * log x ^ 2 - 2 * (x * log x) + 2 * x

private theorem log_sq_moment {d : ℝ} (hd : 0 < d) :
    IntervalIntegrable (fun x : ℝ => log x ^ 2) volume 0 d ∧
      (∫ x in 0..d, log x ^ 2) = logSqPrim d := by
  have hdiff (x : ℝ) (hx : 0 < x) : HasDerivAt logSqPrim (log x ^ 2) x := by
    have dh := hasDerivAt_log hx.ne'
    have dx := hasDerivAt_id' x
    refine (((dx.mul (dh.pow 2)).sub ((dx.mul dh).const_mul 2)).add
      (dx.const_mul 2)).congr_deriv ?_
    simp only [Pi.pow_apply]
    field_simp [hx.ne']
    ring
  have h0 : Tendsto logSqPrim (𝓝[>] 0) (𝓝 0) := by
    unfold logSqPrim
    simpa only [mul_zero, sub_zero, add_zero] using
      (tendsto_mul_log_sq_zero.sub (tendsto_mul_log_zero.const_mul 2)).add
        (tendsto_cut_zero.const_mul 2)
  have h := intervalIntegrable_and_integral_eq_of_nonneg' hd
    (fun x hx => hdiff x hx.1) (fun x _ => sq_nonneg (log x)) h0
    ((hdiff d hd).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [sub_zero] using h

private noncomputable def cutLogs (q : ℝ × (ℝ × ℝ)) : ℝ :=
  log (q.2.1 - q.1) - log (q.1 - q.2.2)

private noncomputable def cutJoin (q : ℝ × (ℝ × ℝ)) : ℝ :=
  i10K2JoinLog ((q.1 - q.2.2) / (q.2.1 - q.2.2))

private noncomputable def cutQuadratic (q : ℝ × (ℝ × ℝ)) : ℝ :=
  i10K2PsiTwoDeriv q.1 * cutLogs q +
    deriv i10K2PsiOne q.1 * (cutBubble q.1 q.2 + cutJoin q)

private noncomputable def cutLogSum (q : ℝ × (ℝ × ℝ)) : ℝ :=
  1 + log q.1 ^ 2 + log (1 - q.1) ^ 2 +
    log (q.1 - q.2.2) ^ 2 + log (q.2.1 - q.1) ^ 2 + log (1 - q.2.1) ^ 2

private noncomputable def cutMajorant (C : ℝ) (q : ℝ × (ℝ × ℝ)) : ℝ :=
  (C / q.1) * cutLogSum q

private theorem cutLogSum_section {t : ℝ} (ht : t ∈ unitInterval) :
    IntegrableOn (fun p => cutLogSum (t, p)) (cutRectangle t) := by
  have hc := sub_pos.mpr ht.2
  have hb := (log_sq_moment hc).1.comp_sub_right t
  have ha := (log_sq_moment ht.1).1.symm.comp_sub_left t
  have hr := (log_sq_moment hc).1.symm.comp_sub_left 1
  simp only [zero_add, sub_add_cancel, sub_self, sub_zero, sub_sub_cancel] at ha hb hr
  have hA := integrableOn_cut_snd
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1.le).1 ha)
  have hB := integrableOn_cut_fst
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.2.le).1 hb)
  have hR := integrableOn_cut_fst
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.2.le).1 hr)
  have hC : IntegrableOn (fun _ : ℝ × ℝ => 1 + log t ^ 2 + log (1 - t) ^ 2)
      (cutRectangle t) :=
    (integrableOn_const (C := 1 + log t ^ 2 + log (1 - t) ^ 2)
      ((isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne) :
      IntegrableOn _ (Icc t 1 ×ˢ Icc 0 t)).mono_set
        (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  exact ((hC.add hA).add hB).add hR

private theorem integral_cutLogSum {t : ℝ} (ht : t ∈ unitInterval) :
    let c := 1 - t
    (∫ p in cutRectangle t, cutLogSum (t, p)) =
      t * c * (7 + 2 * log t ^ 2 + 3 * log c ^ 2 - 2 * log t - 4 * log c) := by
  dsimp only
  rw [cut_rectangle_integral ht (cutLogSum_section ht)]
  let c := 1 - t
  have hc : 0 < c := sub_pos.mpr ht.2
  have hb := (log_sq_moment hc).1
  have hr : IntervalIntegrable (fun b : ℝ => log (c - b) ^ 2) volume 0 c := by
    simpa only [sub_self, sub_zero] using hb.symm.comp_sub_left c
  have e (a : ℝ) : (∫ b in (0 : ℝ)..c, cutLogSum (t, b + t, t - a)) =
      ((1 + log t ^ 2 + log c ^ 2) * c + c * log a ^ 2) + 2 * logSqPrim c := by
    have hC : IntervalIntegrable (fun _ => 1 + log t ^ 2 + log c ^ 2 + log a ^ 2) volume 0 c :=
      intervalIntegrable_const
    simp only [cutLogSum, sub_sub_cancel, add_sub_cancel_right]
    simp_rw [show ∀ b : ℝ, 1 - (b + t) = c - b by intro b; dsimp only [c]; ring]
    rw [intervalIntegral.integral_add (hC.add hb) hr,
      intervalIntegral.integral_add hC hb, intervalIntegral.integral_const,
      intervalIntegral.integral_comp_sub_left (f := fun x => log x ^ 2) c,
      sub_self, sub_zero, (log_sq_moment hc).2]
    simp only [smul_eq_mul, c]
    ring
  change (∫ a in (0 : ℝ)..t, ∫ b in (0 : ℝ)..c, cutLogSum (t, b + t, t - a)) = _
  simp_rw [e]
  have ha := (log_sq_moment ht.1).1.const_mul c
  rw [intervalIntegral.integral_add (intervalIntegrable_const.add ha) intervalIntegrable_const,
    intervalIntegral.integral_add intervalIntegrable_const ha,
    intervalIntegral.integral_const_mul c (fun x => log x ^ 2), (log_sq_moment ht.1).2]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, logSqPrim, c]
  ring

private theorem integrable_cutMajorant {C : ℝ} (hC : 0 ≤ C) :
    Integrable (cutRegion.indicator (cutMajorant C))
      ((volume.restrict unitInterval).prod volume) := by
  have hm : Measurable (cutMajorant C) := by
    unfold cutMajorant cutLogSum
    fun_prop
  apply (integrable_prod_iff (hm.indicator measurableSet_cutRegion).aestronglyMeasurable).2
  have hs (t : ℝ) : MeasurableSet (cutRectangle t) := measurableSet_Ioo.prod measurableSet_Ioo
  constructor
  · apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    exact (integrable_indicator_iff (hs t)).2 ((cutLogSum_section ht).const_mul (C / t))
  · let m := fun t : ℝ =>
      C * (1 - t) * (7 + 2 * log t ^ 2 + 3 * log (1 - t) ^ 2 - 2 * log t - 4 * log (1 - t))
    have hm₀ : Measurable m := by unfold m; fun_prop
    have hi : IntegrableOn m unitInterval := by
      apply ParamHPL.integrableOn_Ioo_of_abs_le_logs (C := 1) (D := 18 * C)
        zero_le_one (by positivity) 2 hm₀.aestronglyMeasurable
      intro t ht
      have ht₀ := ht.1
      have ht₁ := ht.2
      have hct := sub_pos.mpr ht₁
      have hl := log_nonpos ht₀.le ht₁.le
      have hr := log_nonpos hct.le (sub_le_self _ ht₀.le)
      have hll := sq_nonneg (log t)
      have hrr := sq_nonneg (log (1 - t))
      have he : 0 ≤ 7 + 2 * log t ^ 2 + 3 * log (1 - t) ^ 2 -
          2 * log t - 4 * log (1 - t) := by nlinarith only [hl, hr, hll, hrr]
      unfold m
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg hC hct.le) he),
        abs_of_nonpos hl, abs_of_nonpos hr, mul_comm 18 C, mul_assoc, mul_assoc C 18]
      apply mul_le_mul_of_nonneg_left _ hC
      refine (mul_le_of_le_one_left he (by linarith only [ht₀])).trans ?_
      have hcross := mul_nonneg (neg_nonneg.mpr hl) (neg_nonneg.mpr hr)
      nlinarith only [hl, hr, hll, hrr, hcross]
    apply hi.congr
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    change m t = ∫ p, ‖(cutRectangle t).indicator (fun p => cutMajorant C (t, p)) p‖
    have hnorm (p : ℝ × ℝ) :
        ‖(cutRectangle t).indicator (fun p => cutMajorant C (t, p)) p‖ =
          (cutRectangle t).indicator (fun p => cutMajorant C (t, p)) p := by
      by_cases hp : p ∈ cutRectangle t
      · rw [indicator_of_mem hp, Real.norm_eq_abs, abs_of_nonneg]
        have ht₀ := ht.1
        unfold cutMajorant cutLogSum
        positivity
      · rw [indicator_of_notMem hp, norm_zero]
    simp_rw [hnorm]
    rw [integral_indicator (hs t)]
    change m t = ∫ p in cutRectangle t, (C / t) * cutLogSum (t, p)
    rw [integral_const_mul, integral_cutLogSum ht]
    unfold m
    field_simp [ht.1.ne']


private theorem measurable_Li₂ : Measurable Li₂ := by
  unfold Li₂
  exact Measurable.tsum fun _ => by fun_prop

private theorem measurable_cutLogs : Measurable cutLogs := by unfold cutLogs; fun_prop

private theorem measurable_cutJoin : Measurable cutJoin := by
  let x := fun q : ℝ × (ℝ × ℝ) => (q.1 - q.2.2) / (q.2.1 - q.2.2)
  have hx : Measurable x := by unfold x; fun_prop
  have hy : Measurable (fun q => 1 - x q) := measurable_const.sub hx
  unfold cutJoin i10K2JoinLog
  exact ((((hy.log.pow_const 2).sub (hx.log.pow_const 2)).div_const 2).add
    (measurable_Li₂.comp hx)).sub (measurable_Li₂.comp hy)

private theorem measurable_cutBubble : Measurable (fun q : ℝ × (ℝ × ℝ) => cutBubble q.1 q.2) := by
  unfold cutBubble
  fun_prop

private theorem measurable_cutQuadratic : Measurable cutQuadratic := by
  have hD := measurable_deriv (f := i10K2PsiOne)
  have hL := measurable_Li₂
  have h₂ : Measurable i10K2PsiTwoDeriv := by
    unfold i10K2PsiTwoDeriv
    fun_prop (disch := assumption)
  unfold cutQuadratic
  exact (h₂.comp measurable_fst |>.mul measurable_cutLogs).add
    ((hD.comp measurable_fst).mul (measurable_cutBubble.add measurable_cutJoin))

private theorem abs_log_decreases {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    |log b| ≤ |log a| := by
  have hb0 := ha.le.trans hab
  rw [abs_of_nonpos (log_nonpos hb0 hb), abs_of_nonpos (log_nonpos ha.le (hab.trans hb))]
  exact neg_le_neg (log_le_log ha hab)

private theorem cutJoin_bound {t : ℝ} {p : ℝ × ℝ} (hp : p ∈ cutRectangle t)
    {D : ℝ} (hD : ∀ x ∈ Icc (0 : ℝ) 1, |Li₂ x| ≤ D) :
    |cutJoin (t, p)| ≤ (log (t - p.2) ^ 2 + log (p.1 - t) ^ 2) / 2 + 2 * D := by
  let a := t - p.2
  let b := p.1 - t
  have hA : 0 < a := sub_pos.mpr hp.2.2
  have hB : 0 < b := sub_pos.mpr hp.1.1
  have hSum := add_pos hA hB
  have hSum₁ : a + b ≤ 1 := by dsimp [a, b]; linarith only [hp.1.2, hp.2.1]
  have hx : a / (a + b) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hA hSum, (div_lt_one hSum).2 (lt_add_of_pos_right _ hB)⟩
  have hy : 1 - a / (a + b) ∈ Ioo (0 : ℝ) 1 :=
    ⟨sub_pos.mpr hx.2, sub_lt_self _ hx.1⟩
  have he : 1 - a / (a + b) = b / (a + b) := by
    field_simp [hSum.ne']
    ring
  have ha := abs_log_decreases hA ((le_div_iff₀ hSum).2 (mul_le_of_le_one_right hA.le hSum₁))
    hx.2.le
  have hb := abs_log_decreases hB ((le_div_iff₀ hSum).2 (mul_le_of_le_one_right hB.le hSum₁))
    (he ▸ hy.2.le)
  have hsa := pow_le_pow_left₀ (abs_nonneg _) ha 2
  have hsb := pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [sq_abs, sq_abs] at hsa hsb
  have e : p.1 - p.2 = a + b := by dsimp [a, b]; ring
  unfold cutJoin
  change |i10K2JoinLog (a / (p.1 - p.2))| ≤ _
  rw [e, i10K2JoinLog]
  have h₁ := hD _ (Ioo_subset_Icc_self hx)
  have h₂ := hD _ (Ioo_subset_Icc_self hy)
  have hSquare : |(log (1 - a / (a + b)) ^ 2 - log (a / (a + b)) ^ 2) / 2| ≤
      (log b ^ 2 + log a ^ 2) / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), he]
    exact div_le_div_of_nonneg_right ((abs_sub _ _).trans (by
      rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
      exact add_le_add hsb hsa)) (by norm_num)
  refine (abs_sub _ _).trans ?_
  have hA₁ := abs_add_le
    ((log (1 - a / (a + b)) ^ 2 - log (a / (a + b)) ^ 2) / 2) (Li₂ (a / (a + b)))
  linarith only [hSquare, h₁, h₂, hA₁]

private theorem cutBubble_bound {t : ℝ} (ht : t ∈ unitInterval) {p : ℝ × ℝ}
    (hp : p ∈ cutRectangle t) : |cutBubble t p| ≤ cutLogSum (t, p) := by
  have hc := sub_pos.mpr ht.2
  have hcs : 1 - t ≤ 1 - p.2 := sub_le_sub_left hp.2.2.le _
  have hcs₁ : 1 - p.2 ≤ 1 := sub_le_self _ hp.2.1.le
  have hcs' := abs_log_decreases hc hcs hcs₁
  have hL := abs_sub (log (p.1 - t)) (log (t - p.2))
  have hW := abs_sub (-log (1 - p.1)) (log (1 - p.2))
  rw [abs_neg] at hW
  rw [cutBubble, abs_mul]
  refine (mul_le_mul (hW.trans (add_le_add le_rfl hcs')) hL (abs_nonneg _)
    (add_nonneg (abs_nonneg _) (abs_nonneg _))).trans ?_
  unfold cutLogSum
  simp only
  have hsq := sq_nonneg
    (|log (1 - p.1)| + |log (1 - t)| - (|log (p.1 - t)| + |log (t - p.2)|))
  have hsq₁ := sq_nonneg (|log (1 - p.1)| - |log (1 - t)|)
  have hsq₂ := sq_nonneg (|log (p.1 - t)| - |log (t - p.2)|)
  rw [← sq_abs (log (1 - p.1)), ← sq_abs (log (1 - t)),
    ← sq_abs (log (p.1 - t)), ← sq_abs (log (t - p.2))]
  nlinarith only [hsq, hsq₁, hsq₂, sq_nonneg (log t)]

private theorem cutWeightedLogs_bound (t : ℝ) (p : ℝ × ℝ) :
    (1 + |log t|) * |cutLogs (t, p)| ≤ 2 * cutLogSum (t, p) := by
  unfold cutLogs
  refine (mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)).trans ?_
  unfold cutLogSum
  simp only
  have hsq := sq_nonneg (1 + |log t| - (|log (p.1 - t)| + |log (t - p.2)|))
  have hsq₁ := sq_nonneg (1 - |log t|)
  have hsq₂ := sq_nonneg (|log (p.1 - t)| - |log (t - p.2)|)
  rw [← sq_abs (log t), ← sq_abs (log (p.1 - t)), ← sq_abs (log (t - p.2))]
  nlinarith only [hsq, hsq₁, hsq₂, sq_nonneg (log (1 - t)), sq_nonneg (log (1 - p.1))]

private theorem cutJoin_bound_sum {t : ℝ} {p : ℝ × ℝ} (hp : p ∈ cutRectangle t)
    {D : ℝ} (hD₀ : 0 ≤ D) (hD : ∀ x ∈ Icc (0 : ℝ) 1, |Li₂ x| ≤ D) :
    |cutJoin (t, p)| ≤ (1 + 2 * D) * cutLogSum (t, p) := by
  refine (cutJoin_bound hp hD).trans ?_
  have hS : 1 ≤ cutLogSum (t, p) := by
    unfold cutLogSum
    linarith only [sq_nonneg (log t), sq_nonneg (log (1 - t)), sq_nonneg (log (t - p.2)),
      sq_nonneg (log (p.1 - t)), sq_nonneg (log (1 - p.1))]
  have hB : (log (t - p.2) ^ 2 + log (p.1 - t) ^ 2) / 2 ≤ cutLogSum (t, p) := by
    unfold cutLogSum
    linarith only [sq_nonneg (log t), sq_nonneg (log (1 - t)), sq_nonneg (log (t - p.2)),
      sq_nonneg (log (p.1 - t)), sq_nonneg (log (1 - p.1))]
  rw [add_mul, one_mul]
  exact add_le_add hB (le_mul_of_one_le_right (by positivity) hS)

private theorem exists_dilog_bound : ∃ D ≥ (0 : ℝ), ∀ x ∈ Icc (0 : ℝ) 1, |Li₂ x| ≤ D := by
  have h : ContinuousOn Li₂ (Icc (0 : ℝ) 1) :=
    continuousOn_Li₂.mono (Icc_subset_Icc_left (by norm_num))
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn h
  exact ⟨max 0 D, le_max_left _ _, fun x hx =>
    (by simpa only [Real.norm_eq_abs] using hD x hx : |Li₂ x| ≤ D).trans (le_max_right _ _)⟩

private theorem cutQuadratic_bound :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ unitInterval, ∀ p ∈ cutRectangle t,
      ‖cutQuadratic (t, p)‖ ≤ cutMajorant C (t, p) := by
  obtain ⟨A, hA₀, hA⟩ := abs_i10K2PsiTwoDeriv_le
  obtain ⟨D, hD₀, hD⟩ := exists_dilog_bound
  refine ⟨2 * A + 4 + 4 * D, by positivity, fun t ht p hp => ?_⟩
  have ht₀ := ht.1
  change |i10K2PsiTwoDeriv t * cutLogs (t, p) +
    deriv i10K2PsiOne t * (cutBubble t p + cutJoin (t, p))| ≤ _
  have h₁ : |i10K2PsiTwoDeriv t * cutLogs (t, p)| ≤
      (A / t) * (2 * cutLogSum (t, p)) := by
    rw [abs_mul]
    calc
      _ ≤ (A * (1 + |log t|) / t) * |cutLogs (t, p)| :=
        mul_le_mul_of_nonneg_right (hA t ht) (abs_nonneg _)
      _ = (A / t) * ((1 + |log t|) * |cutLogs (t, p)|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (cutWeightedLogs_bound t p) (by positivity)
  have h₂ : |deriv i10K2PsiOne t * (cutBubble t p + cutJoin (t, p))| ≤
      (2 / t) * (cutLogSum (t, p) + (1 + 2 * D) * cutLogSum (t, p)) := by
    rw [abs_mul]
    exact mul_le_mul (abs_deriv_i10K2PsiOne_le ht)
      ((abs_add_le _ _).trans (add_le_add (cutBubble_bound ht hp) (cutJoin_bound_sum hp hD₀ hD)))
      (abs_nonneg _) (by positivity)
  refine (abs_add_le _ _).trans ((add_le_add h₁ h₂).trans (le_of_eq ?_))
  unfold cutMajorant
  change _ = ((2 * A + 4 + 4 * D) / t) * cutLogSum (t, p)
  ring

private theorem integrable_cutQuadratic :
    Integrable (cutRegion.indicator cutQuadratic) ((volume.restrict unitInterval).prod volume) := by
  obtain ⟨C, hC₀, hC⟩ := cutQuadratic_bound
  have hm : Measurable (cutMajorant C) := by unfold cutMajorant cutLogSum; fun_prop
  have hq := measurable_cutQuadratic.indicator measurableSet_cutRegion
  refine (integrable_cutMajorant hC₀).mono' hq.aestronglyMeasurable ?_
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le
    hq.norm (hm.indicator measurableSet_cutRegion))).2
  apply ae_restrict_of_forall_mem measurableSet_Ioo
  intro t ht
  filter_upwards [] with p
  by_cases hp : (t, p) ∈ cutRegion
  · simpa only [indicator_of_mem hp] using hC t ht p hp
  · simp only [indicator_of_notMem hp, norm_zero, le_refl]


/-! ## Exchange of the bubble and cut integrals -/

private theorem intervalIntegrable_joinLog :
    IntervalIntegrable i10K2JoinLog volume (0 : ℝ) 1 := by
  have h₁ := (log_sq_moment zero_lt_one).1
  have h₂ := h₁.symm.comp_sub_left 1
  simp only [sub_self, sub_zero] at h₂
  have hC : ContinuousOn Li₂ (Icc (0 : ℝ) 1) :=
    continuousOn_Li₂.mono (Icc_subset_Icc_left (by norm_num))
  have hCr : ContinuousOn (fun x => Li₂ (1 - x)) (Icc (0 : ℝ) 1) :=
    hC.comp (continuousOn_const.sub continuousOn_id)
      (fun x hx => ⟨sub_nonneg.mpr hx.2, sub_le_self _ hx.1⟩)
  rw [← uIcc_of_le zero_le_one] at hC hCr
  exact (((h₂.sub h₁).div_const 2).add hC.intervalIntegrable).sub hCr.intervalIntegrable

private theorem intervalIntegrable_joinLog_comp (s r : ℝ) :
    IntervalIntegrable (fun t => i10K2JoinLog ((t - s) / (r - s))) volume s r := by
  have h := (intervalIntegrable_joinLog.comp_mul_right (c := (r - s)⁻¹)).comp_sub_right s
  simpa only [inv_inv, zero_mul, one_mul, zero_add, sub_add_cancel, div_eq_mul_inv] using h

private theorem continuousOn_i10K2PsiOne_deriv :
    ContinuousOn (deriv i10K2PsiOne) (Ioo (0 : ℝ) 1) := by
  have hc : ContinuousOn (fun t : ℝ => 1 / t - 3 * (t + (1 - t) * log (1 - t)) / t ^ 3)
      (Ioo (0 : ℝ) 1) := by
    intro t ht
    have ht₀ := ht.1.ne'
    have ht₃ := pow_ne_zero 3 ht₀
    have hc := (sub_pos.mpr ht.2).ne'
    apply ContinuousAt.continuousWithinAt
    fun_prop
  exact hc.congr (fun _ ht => (hasDerivAt_i10K2PsiOne ht).deriv)


private noncomputable def orientedQuadratic (p : ℝ × ℝ) : ℝ :=
  ∫ t in p.2..p.1, cutQuadratic (t, p)

private noncomputable def joinedQuadratic (p : ℝ × ℝ) : ℝ :=
  (∫ t in p.2..p.1, i10K2PsiTwoDeriv t * cutLogs (t, p)) -
    (log (1 - p.1) + log (1 - p.2)) *
      (∫ t in p.2..p.1, deriv i10K2PsiOne t * cutLogs (t, p)) +
    ∫ t in p.2..p.1, deriv i10K2PsiOne t * cutJoin (t, p)

private theorem orientedQuadratic_eq_joined_of_lt {r s : ℝ}
    (hr : r ∈ unitInterval) (hs : s ∈ unitInterval) (hsr : s < r) :
    orientedQuadratic (r, s) = joinedQuadratic (r, s) := by
  have hL : IntervalIntegrable (fun t => cutLogs (t, r, s)) volume s r := by
    have h := intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := r - s)
    have h₁ := h.symm.comp_sub_left r
    have h₂ := h.comp_sub_right s
    simp only [zero_add, sub_sub_cancel, sub_zero, sub_add_cancel] at h₁ h₂
    exact h₁.sub h₂
  have hsub : uIcc s r ⊆ unitInterval := by
    rw [uIcc_of_le hsr.le]
    exact fun _ hx => ⟨hs.1.trans_le hx.1, hx.2.trans_lt hr.2⟩
  have h₁ := hL.continuousOn_mul (continuousOn_i10K2PsiTwoDeriv.mono hsub)
  have h₂ := hL.continuousOn_mul (continuousOn_i10K2PsiOne_deriv.mono hsub)
  have h₃ : IntervalIntegrable (fun t => deriv i10K2PsiOne t * cutJoin (t, r, s))
      volume s r := (intervalIntegrable_joinLog_comp s r).continuousOn_mul
    (continuousOn_i10K2PsiOne_deriv.mono hsub)
  unfold orientedQuadratic joinedQuadratic
  calc
    _ = ∫ t in s..r, (i10K2PsiTwoDeriv t * cutLogs (t, r, s) -
        (log (1 - r) + log (1 - s)) * (deriv i10K2PsiOne t * cutLogs (t, r, s))) +
        deriv i10K2PsiOne t * cutJoin (t, r, s) := by
      apply intervalIntegral.integral_congr
      intro t _
      unfold cutQuadratic cutBubble cutLogs
      dsimp only
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (h₁.sub (h₂.const_mul _)) h₃,
        intervalIntegral.integral_sub h₁ (h₂.const_mul _), intervalIntegral.integral_const_mul]

private theorem cutLogs_swap (t : ℝ) (p : ℝ × ℝ) :
    cutLogs (t, p.swap) = -cutLogs (t, p) := by
  rcases p with ⟨r, s⟩
  change log (s - t) - log (t - r) = -(log (r - t) - log (t - s))
  rw [show s - t = -(t - s) by ring, show t - r = -(r - t) by ring,
    log_neg_eq_log, log_neg_eq_log]
  ring

private theorem cutJoin_swap (t : ℝ) (p : ℝ × ℝ) (h : p.1 ≠ p.2) :
    cutJoin (t, p.swap) = -cutJoin (t, p) := by
  rcases p with ⟨r, s⟩
  change i10K2JoinLog ((t - r) / (s - r)) = -i10K2JoinLog ((t - s) / (r - s))
  have he : (t - r) / (s - r) = 1 - (t - s) / (r - s) := by
    field_simp [sub_ne_zero.mpr h, sub_ne_zero.mpr h.symm]
    ring
  rw [he]
  simp only [i10K2JoinLog, sub_sub_cancel]
  ring

private theorem orientedQuadratic_swap (p : ℝ × ℝ) :
    orientedQuadratic p.swap = orientedQuadratic p := by
  rcases eq_or_ne p.1 p.2 with h | h
  · simp only [orientedQuadratic, Prod.fst_swap, Prod.snd_swap, h,
      intervalIntegral.integral_same]
  · unfold orientedQuadratic
    rw [Prod.fst_swap, Prod.snd_swap, intervalIntegral.integral_symm,
      ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    have hb : cutBubble t p.swap = -cutBubble t p := by
      change (-log (1 - p.2) - log (1 - p.1)) * cutLogs (t, p.swap) = _
      rw [cutLogs_swap]
      unfold cutBubble cutLogs
      ring
    simp only [cutQuadratic, cutLogs_swap, cutJoin_swap t p h, hb]
    ring

private theorem joinedQuadratic_swap (p : ℝ × ℝ) :
    joinedQuadratic p.swap = joinedQuadratic p := by
  rcases eq_or_ne p.1 p.2 with h | h
  · simp only [joinedQuadratic, Prod.fst_swap, Prod.snd_swap, h,
      intervalIntegral.integral_same]
  · have hL (f : ℝ → ℝ) :
        (∫ t in p.1..p.2, f t * cutLogs (t, p.swap)) =
          ∫ t in p.2..p.1, f t * cutLogs (t, p) := by
      simp_rw [cutLogs_swap, mul_neg, intervalIntegral.integral_neg,
        intervalIntegral.integral_symm (a := p.1) (b := p.2)]
    have hJ :
        (∫ t in p.1..p.2, deriv i10K2PsiOne t * cutJoin (t, p.swap)) =
          ∫ t in p.2..p.1, deriv i10K2PsiOne t * cutJoin (t, p) := by
      simp_rw [fun t => cutJoin_swap t p h, mul_neg, intervalIntegral.integral_neg,
        intervalIntegral.integral_symm (a := p.1) (b := p.2)]
    simp only [joinedQuadratic, Prod.fst_swap, Prod.snd_swap, hL, hJ]
    rw [add_comm (log (1 - p.2))]

private theorem joinedQuadratic_eq_oriented {p : ℝ × ℝ}
    (hp : p ∈ unitInterval ×ˢ unitInterval) :
    joinedQuadratic p = orientedQuadratic p := by
  rcases lt_trichotomy p.2 p.1 with h | h | h
  · exact (orientedQuadratic_eq_joined_of_lt hp.1 hp.2 h).symm
  · simp only [joinedQuadratic, orientedQuadratic, h, intervalIntegral.integral_same,
      mul_zero, sub_zero, add_zero]
  · rw [← joinedQuadratic_swap p, ← orientedQuadratic_swap p]
    exact (orientedQuadratic_eq_joined_of_lt hp.2 hp.1 h).symm

private theorem integral_cutQuadratic_bubbles :
    (∫ q, cutRegion.indicator cutQuadratic q ∂(volume.restrict unitInterval).prod volume) =
      ∫ p in unitInterval ×ˢ unitInterval,
        {p : ℝ × ℝ | p.2 < p.1}.indicator orientedQuadratic p := by
  rw [integral_prod_symm _ integrable_cutQuadratic, ← integral_indicator
    (measurableSet_Ioo.prod measurableSet_Ioo)]
  apply integral_congr_ae
  filter_upwards [] with p
  by_cases hp : p ∈ unitInterval ×ˢ unitInterval
  · rw [indicator_of_mem hp]
    by_cases h : p.2 < p.1
    · rw [indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.2 < p.1} from h)]
      unfold orientedQuadratic
      rw [intervalIntegral.integral_of_le h.le, integral_Ioc_eq_integral_Ioo,
        ← integral_indicator measurableSet_Ioo, ← integral_indicator measurableSet_Ioo]
      apply integral_congr_ae
      filter_upwards [] with t
      by_cases ht : t ∈ Ioo p.2 p.1
      · have ht' : t ∈ unitInterval := ⟨hp.2.1.trans ht.1, ht.2.trans hp.1.2⟩
        have hq : (t, p) ∈ cutRegion := ⟨⟨ht.2, hp.1.2⟩, ⟨hp.2.1, ht.1⟩⟩
        simp only [indicator_of_mem ht, indicator_of_mem ht', indicator_of_mem hq]
      · have hq : (t, p) ∉ cutRegion := fun hq => ht ⟨hq.2.2, hq.1.1⟩
        simp [indicator_of_notMem ht, indicator_of_notMem hq, indicator_apply]
    · rw [indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.2 < p.1} from h)]
      apply integral_eq_zero_of_ae
      apply ae_restrict_of_forall_mem measurableSet_Ioo
      intro t _
      exact indicator_of_notMem (fun hq => h (hq.2.2.trans hq.1.1)) _
  · rw [indicator_of_notMem hp]
    apply integral_eq_zero_of_ae
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    exact indicator_of_notMem (fun hq =>
      hp ⟨⟨ht.1.trans hq.1.1, hq.1.2⟩, ⟨hq.2.1, hq.2.2.trans ht.2⟩⟩) _


private theorem integral_orientedQuadratic (hi : IntegrableOn orientedQuadratic
    (unitInterval ×ˢ unitInterval)) :
    (∫ p in unitInterval ×ˢ unitInterval, orientedQuadratic p) =
      2 * (∫ q, cutRegion.indicator cutQuadratic q
        ∂(volume.restrict unitInterval).prod volume) := by
  let T := {p : ℝ × ℝ | p.2 < p.1}
  let U := {p : ℝ × ℝ | p.1 < p.2}
  have hT : MeasurableSet T := measurableSet_lt measurable_snd measurable_fst
  have hU : MeasurableSet U := measurableSet_lt measurable_fst measurable_snd
  have hsum (p : ℝ × ℝ) :
      orientedQuadratic p = T.indicator orientedQuadratic p + U.indicator orientedQuadratic p := by
    rcases lt_trichotomy p.2 p.1 with h | h | h
    · have h₁ : p ∈ T := h
      have h₂ : p ∉ U := h.asymm
      simp only [indicator_of_mem h₁, indicator_of_notMem h₂, add_zero]
    · have h₁ : p ∉ T := by simp [T, h]
      have h₂ : p ∉ U := by simp [U, h]
      simp only [indicator_of_notMem h₁, indicator_of_notMem h₂, add_zero,
        orientedQuadratic, h, intervalIntegral.integral_same]
    · have h₁ : p ∉ T := h.asymm
      have h₂ : p ∈ U := h
      simp only [indicator_of_mem h₂, indicator_of_notMem h₁, zero_add]
  have hswap : (∫ p in unitInterval ×ˢ unitInterval, U.indicator orientedQuadratic p) =
      ∫ p in unitInterval ×ˢ unitInterval, T.indicator orientedQuadratic p := by
    simp only [Measure.volume_eq_prod]
    rw [← setIntegral_prod_swap]
    apply integral_congr_ae
    filter_upwards [] with p
    by_cases hp : p ∈ T
    · rw [indicator_of_mem hp, indicator_of_mem (show p.swap ∈ U from hp), orientedQuadratic_swap]
    · rw [indicator_of_notMem hp, indicator_of_notMem (show p.swap ∉ U from hp)]
  calc
    _ = 2 * (∫ p in unitInterval ×ˢ unitInterval, T.indicator orientedQuadratic p) := by
      simp_rw [hsum]
      rw [integral_add (hi.indicator hT) (hi.indicator hU), hswap, two_mul]
    _ = 2 * (∫ q, cutRegion.indicator cutQuadratic q
      ∂(volume.restrict unitInterval).prod volume) :=
      congrArg (2 * ·) integral_cutQuadratic_bubbles.symm


private theorem integrableOn_cut_of_abs_le {t : ℝ} (ht : t ∈ unitInterval)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ p ∈ cutRectangle t, |f p| ≤ C * cutLogSum (t, p)) :
    IntegrableOn f (cutRectangle t) :=
  ((cutLogSum_section ht).const_mul C).mono' hf.aestronglyMeasurable
    (ae_restrict_of_forall_mem (measurableSet_Ioo.prod measurableSet_Ioo)
      fun p hp => by simpa only [Real.norm_eq_abs] using hb p hp)

private theorem cutLogs_section {t : ℝ} (ht : t ∈ unitInterval) :
    IntegrableOn (fun p => cutLogs (t, p)) (cutRectangle t) := by
  apply integrableOn_cut_of_abs_le ht
    (measurable_cutLogs.comp (measurable_const.prodMk measurable_id)) (C := 2)
  intro p _
  exact (le_mul_of_one_le_left (abs_nonneg _) (le_add_of_nonneg_right (abs_nonneg _))).trans
    (cutWeightedLogs_bound t p)

private theorem cutBubble_section {t : ℝ} (ht : t ∈ unitInterval) :
    IntegrableOn (cutBubble t) (cutRectangle t) := by
  apply integrableOn_cut_of_abs_le ht
    (measurable_cutBubble.comp (measurable_const.prodMk measurable_id)) (C := 1)
  intro p hp
  change |cutBubble t p| ≤ 1 * cutLogSum (t, p)
  simpa only [one_mul] using cutBubble_bound ht hp

private theorem cutJoin_section {t : ℝ} (ht : t ∈ unitInterval) :
    IntegrableOn (fun p => cutJoin (t, p)) (cutRectangle t) := by
  obtain ⟨D, hD₀, hD⟩ := exists_dilog_bound
  exact integrableOn_cut_of_abs_le ht
    (measurable_cutJoin.comp (measurable_const.prodMk measurable_id))
    (fun p hp => cutJoin_bound_sum hp hD₀ hD)

private theorem integral_cutLogs {t : ℝ} (ht : t ∈ unitInterval) :
    2 * (∫ p in cutRectangle t, cutLogs (t, p)) = i10K2DensityOne t := by
  rw [cut_rectangle_integral ht (cutLogs_section ht)]
  simpa only [cutLogs, add_sub_cancel_right, sub_sub_cancel, i10K2DensityOne] using
    integral_i10K2Join_density ht

private theorem integral_cutBubble_add_cutJoin {t : ℝ} (ht : t ∈ unitInterval) :
    2 * (∫ p in cutRectangle t, cutBubble t p + cutJoin (t, p)) = i10K2DensityTwo t := by
  have hv := integral_cutJoin ht (cutJoin_section ht)
  change 2 * (∫ p in cutRectangle t, cutJoin (t, p)) = _ at hv
  rw [integral_add (cutBubble_section ht) (cutJoin_section ht), mul_add,
    add_comm, hv, integral_cutBubble ht (cutBubble_section ht)]
  exact bubble_radial_density ht

private theorem integral_cutQuadratic_section {t : ℝ} (ht : t ∈ unitInterval) :
    2 * (∫ p, cutRegion.indicator cutQuadratic (t, p)) = i10K2QuadraticReduced t := by
  change 2 * (∫ p, (cutRectangle t).indicator (fun p => cutQuadratic (t, p)) p) = _
  have hs : MeasurableSet (cutRectangle t) := measurableSet_Ioo.prod measurableSet_Ioo
  rw [integral_indicator hs]
  unfold cutQuadratic
  dsimp only
  have h₁ := (cutLogs_section ht).const_mul (i10K2PsiTwoDeriv t)
  have h₂ : IntegrableOn (fun p => deriv i10K2PsiOne t * (cutBubble t p + cutJoin (t, p)))
      (cutRectangle t) :=
    ((cutBubble_section ht).add (cutJoin_section ht)).const_mul (deriv i10K2PsiOne t)
  rw [integral_add h₁ h₂,
    integral_const_mul, integral_const_mul, mul_add,
    mul_left_comm 2 (i10K2PsiTwoDeriv t), mul_left_comm 2 (deriv i10K2PsiOne t),
    integral_cutLogs ht, integral_cutBubble_add_cutJoin ht]
  unfold i10K2QuadraticReduced
  ring

/-- The reduced quadratic coefficient is absolutely integrable on the cut interval. -/
theorem integrableOn_i10K2QuadraticReduced :
    IntegrableOn i10K2QuadraticReduced (Ioo (0 : ℝ) 1) := by
  exact (integrable_cutQuadratic.integral_prod_left.const_mul 2).congr
    (ae_restrict_of_forall_mem measurableSet_Ioo fun _ ht => integral_cutQuadratic_section ht)

/-- The quadratic coefficient of the subtracted second remainder. -/
theorem integral_i10K2CoeffTwo :
    ∫ p in i10K2Domain, i10K2CoeffTwo p =
      121 * π ^ 4 / 60 - 10 * π ^ 2 - 38 * zeta3 - 49 := by
  obtain ⟨hi, he⟩ := integral_i10K2CoeffTwo_joined
  change IntegrableOn joinedQuadratic (unitInterval ×ˢ unitInterval) at hi
  have hS : MeasurableSet (unitInterval ×ˢ unitInterval) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hio := hi.congr (ae_restrict_of_forall_mem hS fun _ hp => joinedQuadratic_eq_oriented hp)
  rw [he]
  change (∫ p in unitInterval ×ˢ unitInterval, joinedQuadratic p) = _
  rw [setIntegral_congr_fun hS (fun _ hp => joinedQuadratic_eq_oriented hp),
    integral_orientedQuadratic hio, integral_prod _ integrable_cutQuadratic, ← integral_const_mul]
  exact (setIntegral_congr_fun measurableSet_Ioo (fun _ ht =>
    integral_cutQuadratic_section ht)).trans
    (integral_i10K2QuadraticReduced integrableOn_i10K2QuadraticReduced)

/-! ## Laurent assembly -/

/-- The Laurent truncation of the second subtracted remainder through order two. -/
theorem hasTruncLaurent_i10K2 : QED.ThreeLoopD.HasTruncLaurent i10K2 i10K2Laurent 3 := by
  have h := hasTruncLaurent_i10K2_log_integrals
  rw [integral_i10K2CoeffOne, integral_i10K2CoeffTwo] at h
  convert h using 2 with ε
  unfold i10K2Laurent
  push_cast
  ring

/-- The assembled Laurent truncation of the set (e) master integral I10. -/
theorem hasTruncLaurent_setEMasterI10 :
    QED.ThreeLoopD.HasTruncLaurent setEMasterI10 setELaurentI10 2 :=
  hasTruncLaurent_setEMasterI10_of_Ka_K2 hasTruncLaurent_i10Ka hasTruncLaurent_i10K2

end QED.ThreeLoopE
