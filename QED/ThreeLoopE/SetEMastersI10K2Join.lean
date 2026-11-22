/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.ExtraIntegrals
import QED.Polylog.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import QED.ThreeLoopD.SetDMastersI9RemKuIBP

/-!
# The logarithmic joining kernel of the second remainder of `I₁₀`

At a cut in the joining interval the two sides of the interpolation subtraction
contribute with opposite signs. The unweighted kernel is a difference of
logarithms. The joining weight's logarithmic variation replaces it by a
difference of logarithmic squares and dilogarithms.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog

namespace QED.ThreeLoopE

/-- The joining kernel with the logarithm of the joining weight inserted. -/
noncomputable def i10K2JoinLog (x : ℝ) : ℝ :=
  (log (1 - x) ^ 2 - log x ^ 2) / 2 + Li₂ x - Li₂ (1 - x)

theorem integral_i10K2Join {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (∫ z in x..1, z⁻¹) - (∫ z in 0..x, (1 - z)⁻¹) = log (1 - x) - log x := by
  have hc : 0 < 1 - x := sub_pos.mpr hx.2
  have h := intervalIntegral.integral_comp_sub_left (f := fun z : ℝ => z⁻¹)
    (a := 0) (b := x) 1
  rw [sub_zero] at h
  rw [h, integral_inv_of_pos hx.1 zero_lt_one, integral_inv_of_pos hc zero_lt_one,
    one_div, one_div, log_inv, log_inv]
  ring

private noncomputable def i10K2JoinLogPrim (x : ℝ) : ℝ := log x ^ 2 / 2 - Li₂ x

private theorem hasDerivAt_i10K2JoinLogPrim {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i10K2JoinLogPrim (log (x * (1 - x)) / x) x := by
  have hc := sub_pos.mpr hx.2
  rw [log_mul hx.1.ne' hc.ne']
  refine ((((hasDerivAt_log hx.1.ne').pow 2).div_const 2).sub
    (hasDerivAt_Li₂' hx)).congr_deriv ?_
  ring

private theorem intervalIntegrable_i10K2JoinLog {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => log (x * (1 - x)) / x) volume a 1 := by
  have hL := intervalIntegrable_and_integral_log_one_sub_div.1
  have hR : ContinuousOn (fun x : ℝ => log x / x) (Icc a 1) :=
    (continuousOn_log.mono fun x hx => (ha.1.trans_le hx.1).ne').div
      continuousOn_id fun x hx => (ha.1.trans_le hx.1).ne'
  have hSub : uIcc a 1 ⊆ uIcc 0 1 := by
    rw [uIcc_of_le ha.2.le, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc_left ha.1.le
  have h := (hR.mono (by rw [uIcc_of_le ha.2.le])).intervalIntegrable.add
    (hL.mono_set hSub)
  apply h.congr_uIoo
  intro x hx
  rw [uIoo_of_le ha.2.le] at hx
  dsimp only
  rw [log_mul (ha.1.trans hx.1).ne' (sub_pos.mpr hx.2).ne', add_div]

private theorem integral_i10K2JoinLog_right {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    (∫ x in a..1, log (x * (1 - x)) / x) = -(π ^ 2 / 6) - i10K2JoinLogPrim a := by
  have hL : Tendsto (fun x : ℝ => log x) (𝓝[<] 1) (𝓝 0) := by
    simpa only [log_one] using ((continuousAt_log one_ne_zero).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (1 : ℝ))))
  have h1 : Tendsto i10K2JoinLogPrim (𝓝[<] 1) (𝓝 (-(π ^ 2 / 6))) := by
    unfold i10K2JoinLogPrim
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_div, zero_sub] using
      ((hL.pow 2).div_const 2).sub tendsto_Li₂_one_left
  have h0 : Tendsto i10K2JoinLogPrim (𝓝[>] a) (𝓝 (i10K2JoinLogPrim a)) :=
    (hasDerivAt_i10K2JoinLogPrim ha).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ha.2
    (fun x hx => hasDerivAt_i10K2JoinLogPrim ⟨ha.1.trans hx.1, hx.2⟩)
    (intervalIntegrable_i10K2JoinLog ha) h0 h1

theorem integral_i10K2JoinLog {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (∫ z in x..1, log (z * (1 - z)) / z) -
      (∫ z in 0..x, log (z * (1 - z)) / (1 - z)) = i10K2JoinLog x := by
  have hc : 1 - x ∈ Ioo (0 : ℝ) 1 := ⟨sub_pos.mpr hx.2, sub_lt_self _ hx.1⟩
  have h := intervalIntegral.integral_comp_sub_left
    (f := fun z : ℝ => log (z * (1 - z)) / z) (a := 0) (b := x) 1
  simp only [sub_sub_cancel, sub_zero] at h
  conv at h => lhs; arg 1; intro z; rw [mul_comm (1 - z) z]
  rw [h, integral_i10K2JoinLog_right hx, integral_i10K2JoinLog_right hc]
  unfold i10K2JoinLog i10K2JoinLogPrim
  ring

/-- An antiderivative of the logarithmic kernel divided by the squared cut parameter. -/
noncomputable def i10K2JoinLogRadialPrim (x : ℝ) : ℝ :=
  (log x + log (1 - x) + 1 - i10K2JoinLog x) / x +
    log x - log (1 - x) + i10K2JoinLog x

private theorem hasDerivAt_i10K2JoinLog {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i10K2JoinLog (-(log x + log (1 - x)) / (x * (1 - x))) x := by
  have hc : 1 - x ∈ Ioo (0 : ℝ) 1 := ⟨sub_pos.mpr hx.2, sub_lt_self _ hx.1⟩
  have hs := (hasDerivAt_id' x).const_sub (1 : ℝ)
  have h := ((hasDerivAt_i10K2JoinLogPrim hc).comp x hs).sub
    (hasDerivAt_i10K2JoinLogPrim hx)
  have he : (fun y => i10K2JoinLogPrim (1 - y) - i10K2JoinLogPrim y) = i10K2JoinLog := by
    funext y
    unfold i10K2JoinLogPrim i10K2JoinLog
    ring
  rw [← he]
  refine h.congr_deriv ?_
  simp only [mul_comm (1 - x), sub_sub_cancel, log_mul hx.1.ne' hc.1.ne']
  field_simp [hx.1.ne', hc.1.ne']
  ring

theorem hasDerivAt_i10K2JoinLogRadialPrim {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i10K2JoinLogRadialPrim (i10K2JoinLog x / x ^ 2) x := by
  have hc : 1 - x ≠ 0 := (sub_pos.mpr hx.2).ne'
  have hxL := hasDerivAt_log hx.1.ne'
  have hcL := ((hasDerivAt_id' x).const_sub 1).log hc
  have hJ := hasDerivAt_i10K2JoinLog hx
  have h := ((((((hxL.add hcL).add_const 1).sub hJ).div (hasDerivAt_id' x)
    hx.1.ne').add hxL).sub hcL).add hJ
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, Pi.sub_apply]
  field_simp [hx.1.ne', hc]
  ring

private theorem tendsto_i10K2JoinLog_mul_one_sub :
    Tendsto (fun x => (1 - x) * i10K2JoinLog x) (𝓝[<] 1) (𝓝 0) := by
  have hx : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝 0) :=
    tendsto_one_sub_nhdsLT_one.mono_right nhdsWithin_le_nhds
  have hl : Tendsto (fun x : ℝ => log x) (𝓝[<] 1) (𝓝 0) := by
    simpa only [log_one] using ((continuousAt_log one_ne_zero).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (1 : ℝ))))
  have hLi0 : Tendsto Li₂ (𝓝[>] 0) (𝓝 0) := by
    simpa only [Li₂_zero] using (hasDerivAt_Li₂_zero.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  have h := ((((tendsto_mul_log_sq_zero.comp tendsto_one_sub_nhdsLT_one).sub
    (hx.mul (hl.pow 2))).div_const 2).add (hx.mul tendsto_Li₂_one_left)).sub
      (hx.mul (hLi0.comp tendsto_one_sub_nhdsLT_one))
  simp only [zero_mul, sub_zero, zero_div, add_zero] at h
  exact h.congr fun _ => by unfold i10K2JoinLog; simp only [Function.comp_apply]; ring

theorem tendsto_i10K2JoinLogRadialPrim_one :
    Tendsto i10K2JoinLogRadialPrim (𝓝[<] 1) (𝓝 1) := by
  have hx : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hl : Tendsto (fun x : ℝ => log x) (𝓝[<] 1) (𝓝 0) := by
    simpa only [log_one] using ((continuousAt_log one_ne_zero).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (1 : ℝ))))
  have h := (((((hx.const_add 1).mul hl).add
    (tendsto_mul_log_zero.comp tendsto_one_sub_nhdsLT_one)).add_const 1).sub
      tendsto_i10K2JoinLog_mul_one_sub).div hx one_ne_zero
  simp only [mul_zero, zero_add, sub_zero, div_one] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with x hx'
  unfold i10K2JoinLogRadialPrim
  change ((1 + x) * log x + (1 - x) * log (1 - x) + 1 -
    (1 - x) * i10K2JoinLog x) / x = _
  field_simp [hx'.1.ne']
  ring

theorem integral_i10K2JoinLog_radial {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => i10K2JoinLog x / x ^ 2) volume a 1 ∧
      ∫ x in a..1, i10K2JoinLog x / x ^ 2 = 1 - i10K2JoinLogRadialPrim a := by
  have hL : IntervalIntegrable (fun x : ℝ => log (1 - x) ^ 2) volume a 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.2.le).2
    exact QED.ThreeLoopD.integrableOn_log_one_sub_sq_i9Ku.mono_set
      (Ioo_subset_Ioo_left ha.1.le)
  have hu : uIcc a 1 = Icc a 1 := uIcc_of_le ha.2.le
  have ht {x : ℝ} (hx : x ∈ uIcc a 1) : 0 < x := by
    rw [hu] at hx
    exact ha.1.trans_le hx.1
  have hR : IntervalIntegrable (fun x : ℝ => log x ^ 2) volume a 1 :=
    ((continuousOn_log.mono fun x hx => (ht hx).ne').pow 2).intervalIntegrable
  have hX : uIcc a 1 ⊆ Icc (-1 : ℝ) 1 := by
    rw [hu]
    exact Icc_subset_Icc_left (by linarith [ha.1])
  have hY : MapsTo (fun x : ℝ => 1 - x) (uIcc a 1) (Icc (-1 : ℝ) 1) := by
    intro x hx
    rw [hu] at hx
    exact ⟨by linarith [hx.2], by linarith [ha.1, hx.1]⟩
  have hI : IntervalIntegrable (fun x => i10K2JoinLog x) volume a 1 :=
    (((hL.sub hR).div_const 2).add ((continuousOn_Li₂.mono hX).intervalIntegrable)).sub
      ((continuousOn_Li₂.comp (continuousOn_const.sub continuousOn_id) hY).intervalIntegrable)
  have hN : ContinuousOn (fun x : ℝ => (x ^ 2)⁻¹) (uIcc a 1) :=
    (continuousOn_id.pow 2).inv₀ fun x hx => pow_ne_zero _ (ht hx).ne'
  have hInt : IntervalIntegrable (fun x => i10K2JoinLog x / x ^ 2) volume a 1 := by
    simpa only [div_eq_mul_inv] using hI.mul_continuousOn hN
  exact ⟨hInt, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ha.2
    (fun x hx => hasDerivAt_i10K2JoinLogRadialPrim ⟨ha.1.trans hx.1, hx.2⟩) hInt
    ((hasDerivAt_i10K2JoinLogRadialPrim ha).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    tendsto_i10K2JoinLogRadialPrim_one⟩

/-- Integration over the two distances from the cut for the unweighted kernel. -/
theorem integral_i10K2Join_density {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    2 * (∫ a in (0 : ℝ)..t, ∫ b in (0 : ℝ)..(1 - t), log b - log a) =
      2 * t * (1 - t) * (log (1 - t) - log t) := by
  let c := 1 - t
  have hL (a : ℝ) : (∫ b in (0 : ℝ)..c, log b - log a) =
      c * (log c - 1) - c * log a := by
    rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_log'
      intervalIntegrable_const, integral_log_from_zero_of_pos (sub_pos.mpr ht.2),
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  change 2 * (∫ a in (0 : ℝ)..t, ∫ b in (0 : ℝ)..c, log b - log a) = _
  simp only [hL]
  have hR : IntervalIntegrable (fun a : ℝ => c * log a) volume 0 t :=
    intervalIntegral.intervalIntegrable_log'.const_mul _
  rw [intervalIntegral.integral_sub intervalIntegrable_const hR,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_log_from_zero_of_pos ht.1]
  simp only [sub_zero, smul_eq_mul]
  dsimp only [c]
  ring

/-- Transfer a derivative across the joining weight when the residual vanishes at both ends. -/
theorem integral_i10K2_transfer_derivative {N N' J W : ℝ → ℝ}
    (hN : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt N (N' x) x)
    (hN' : ContinuousOn N' (Icc 0 1)) (hN0 : N 0 = 0) (hN1 : N 1 = 0)
    (hJ : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt J (-W x / (x * (1 - x))) x)
    (hIJ : IntervalIntegrable J volume 0 1) (hIW : IntervalIntegrable W volume 0 1)
    (hJ0 : Tendsto (fun x => x * J x) (𝓝[>] 0) (𝓝 0))
    (hJ1 : Tendsto (fun x => (1 - x) * J x) (𝓝[<] 1) (𝓝 0)) :
    (∫ x in (0 : ℝ)..1, W x * (N x / (x * (1 - x)))) =
      ∫ x in (0 : ℝ)..1, N' x * J x := by
  let Q := fun x : ℝ => N x / (x * (1 - x))
  have nd0 := (hasDerivAt_iff_tendsto_slope_left_right.mp (hN 0 (by simp))).2
  have nd1 := (hasDerivAt_iff_tendsto_slope_left_right.mp (hN 1 (by simp))).1
  have hS0 : Tendsto (fun x => N x / x) (𝓝[>] 0) (𝓝 (N' 0)) := by
    refine nd0.congr ?_
    intro x
    simp only [slope, hN0, vsub_eq_sub, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hS1 : Tendsto (fun x => N x / (1 - x)) (𝓝[<] 1) (𝓝 (-N' 1)) := by
    refine nd1.neg.congr ?_
    intro x
    simp only [slope, hN1, vsub_eq_sub, sub_zero, smul_eq_mul, div_eq_mul_inv]
    rw [show (1 - x) = -(x - 1) by ring, inv_neg]
    ring
  have hq0 : Tendsto Q (𝓝[>] 0) (𝓝 (N' 0)) := by
    have hc : Tendsto (fun x : ℝ => 1 - x) (𝓝[>] 0) (𝓝 1) := by
      have h : Continuous (fun x : ℝ => 1 - x) := continuous_const.sub continuous_id
      simpa only [sub_zero] using (h.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have h := hS0.div hc one_ne_zero
    rw [div_one] at h
    exact h.congr fun _ => by simp only [Q, Pi.div_apply, div_div]
  have hq1 : Tendsto Q (𝓝[<] 1) (𝓝 (-N' 1)) := by
    have hx : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have h := hS1.div hx one_ne_zero
    rw [div_one] at h
    exact h.congr fun _ => by simp only [Q, Pi.div_apply, div_div, mul_comm]
  have hNCont : ContinuousOn N (Icc 0 1) :=
    fun x hx => (hN x hx).continuousAt.continuousWithinAt
  have hQ : ContinuousOn Q (Ioo 0 1) := by
    apply (hNCont.mono Ioo_subset_Icc_self).div
      (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
    exact fun x hx => mul_ne_zero hx.1.ne' (sub_pos.mpr hx.2).ne'
  have hQext : ContinuousOn (extendFrom (Ioo (0 : ℝ) 1) Q) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_Icc_extendFrom_Ioo hQ hq0 hq1
  have hIWQ : IntervalIntegrable (fun x => W x * Q x) volume 0 1 := by
    apply (hIW.mul_continuousOn hQext).congr_uIoo
    intro x hx
    rw [uIoo_of_le zero_le_one] at hx
    simp only [extendFrom_extends hQ x hx]
  have hINJ : IntervalIntegrable (fun x => N' x * J x) volume 0 1 :=
    hIJ.continuousOn_mul (by rwa [uIcc_of_le zero_le_one])
  have hl : Tendsto (fun x => N x * J x) (𝓝[>] 0) (𝓝 0) := by
    have h := hS0.mul hJ0
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    field_simp [hx.ne']
  have hr : Tendsto (fun x => N x * J x) (𝓝[<] 1) (𝓝 0) := by
    have h := hS1.mul hJ1
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x (hx : x < 1)
    field_simp [(sub_pos.mpr hx).ne']
  have hD {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun x => N x * J x) (N' x * J x - W x * Q x) x := by
    refine ((hN x (Ioo_subset_Icc_self hx)).mul (hJ x hx)).congr_deriv ?_
    simp only [Q]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun _ hx => hD hx) (hINJ.sub hIWQ) hl hr
  rw [intervalIntegral.integral_sub hINJ hIWQ, sub_zero] at h
  exact (sub_eq_zero.mp h).symm

private theorem integral_i10K2_interpolation_of_primitive {g g' J W : ℝ → ℝ}
    (hg : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt g (g' x) x)
    (hg' : ContinuousOn g' (Icc 0 1))
    (hJ : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt J (-W x / (x * (1 - x))) x)
    (hIJ : IntervalIntegrable J volume 0 1) (hIW : IntervalIntegrable W volume 0 1)
    (hJ0 : Tendsto (fun x => x * J x) (𝓝[>] 0) (𝓝 0))
    (hJ1 : Tendsto (fun x => (1 - x) * J x) (𝓝[<] 1) (𝓝 0))
    (hodd : ∀ x : ℝ, J (1 - x) = -J x) :
    (∫ x in (0 : ℝ)..1, W x * ((g x - (1 - x) * g 0 - x * g 1) / (x * (1 - x)))) =
      ∫ x in (0 : ℝ)..1, g' x * J x := by
  let N := fun x : ℝ => g x - (1 - x) * g 0 - x * g 1
  let N' := fun x : ℝ => g' x - (g 1 - g 0)
  have hN (x : ℝ) (hx : x ∈ Icc 0 1) : HasDerivAt N (N' x) x := by
    have h := ((hg x hx).sub (((hasDerivAt_id' x).const_sub 1).mul_const (g 0))).sub
      ((hasDerivAt_id' x).mul_const (g 1))
    refine h.congr_deriv ?_
    dsimp only [N']
    ring
  have hN' : ContinuousOn N' (Icc 0 1) := hg'.sub continuousOn_const
  have h := integral_i10K2_transfer_derivative hN hN' (by simp [N]) (by simp [N])
    hJ hIJ hIW hJ0 hJ1
  change (∫ x in (0 : ℝ)..1, W x * (N x / (x * (1 - x)))) = _
  rw [h]
  have hs := intervalIntegral.integral_comp_sub_left (f := J) (a := 0) (b := 1) 1
  simp only [hodd, sub_self, sub_zero, intervalIntegral.integral_neg] at hs
  have hJv : ∫ x in (0 : ℝ)..1, J x = 0 := by linarith only [hs]
  have hC : IntervalIntegrable (fun x => g' x * J x) volume 0 1 :=
    hIJ.continuousOn_mul (by rwa [uIcc_of_le zero_le_one])
  have he (x : ℝ) : N' x * J x = g' x * J x - (g 1 - g 0) * J x := by
    dsimp only [N']
    ring
  simp only [he]
  rw [intervalIntegral.integral_sub hC (hIJ.const_mul (g 1 - g 0)),
    intervalIntegral.integral_const_mul, hJv, mul_zero, sub_zero]

/-- The interpolation subtraction integrated against the logarithm of the joining weight. -/
theorem integral_i10K2_logWeighted_interpolation {g g' : ℝ → ℝ}
    (hg : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt g (g' x) x)
    (hg' : ContinuousOn g' (Icc 0 1)) :
    (∫ x in (0 : ℝ)..1,
      log (x * (1 - x)) * ((g x - (1 - x) * g 0 - x * g 1) / (x * (1 - x)))) =
      ∫ x in (0 : ℝ)..1, g' x * i10K2JoinLog x := by
  have hodd (x : ℝ) : i10K2JoinLog (1 - x) = -i10K2JoinLog x := by
    simp only [i10K2JoinLog, sub_sub_cancel]
    ring
  have h0 : Tendsto (fun x => x * i10K2JoinLog x) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_i10K2JoinLog_mul_one_sub.comp tendsto_one_sub_nhdsGT_zero).neg
    simpa only [Function.comp_def, sub_sub_cancel, hodd, mul_neg, neg_neg, neg_zero] using h
  have hL : IntervalIntegrable (fun x : ℝ => log x) volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'
  have hR := hL.symm.comp_sub_left 1
  simp only [sub_self, sub_zero] at hR
  have hW : IntervalIntegrable (fun x : ℝ => log (x * (1 - x))) volume 0 1 := by
    apply (hL.add hR).congr_uIoo
    intro x hx
    rw [uIoo_of_le zero_le_one] at hx
    exact (log_mul hx.1.ne' (sub_pos.mpr hx.2).ne').symm
  have h1 := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2
    QED.ThreeLoopD.integrableOn_log_sq_i9Ku
  have h2 := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2
    QED.ThreeLoopD.integrableOn_log_one_sub_sq_i9Ku
  have hC : ContinuousOn Li₂ (uIcc (0 : ℝ) 1) :=
    continuousOn_Li₂.mono (by rw [uIcc_of_le zero_le_one]; exact Icc_subset_Icc_left (by norm_num))
  have hCr : ContinuousOn (fun x => Li₂ (1 - x)) (uIcc (0 : ℝ) 1) := by
    apply hC.comp (continuousOn_const.sub continuousOn_id)
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx ⊢
    exact ⟨sub_nonneg.mpr hx.2, sub_le_self _ hx.1⟩
  have hI : IntervalIntegrable i10K2JoinLog volume 0 1 :=
    (((h2.sub h1).div_const 2).add hC.intervalIntegrable).sub hCr.intervalIntegrable
  apply integral_i10K2_interpolation_of_primitive hg hg' _ hI hW h0
    tendsto_i10K2JoinLog_mul_one_sub hodd
  intro x hx
  rw [log_mul hx.1.ne' (sub_pos.mpr hx.2).ne']
  exact hasDerivAt_i10K2JoinLog hx

/-- The interpolation subtraction integrated against the unweighted joining kernel. -/
theorem integral_i10K2_interpolation {g g' : ℝ → ℝ}
    (hg : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt g (g' x) x)
    (hg' : ContinuousOn g' (Icc 0 1)) :
    (∫ x in (0 : ℝ)..1, (g x - (1 - x) * g 0 - x * g 1) / (x * (1 - x))) =
      ∫ x in (0 : ℝ)..1, g' x * (log (1 - x) - log x) := by
  let J := fun x : ℝ => log (1 - x) - log x
  have hodd (x : ℝ) : J (1 - x) = -J x := by simp [J, neg_sub]
  have hL : IntervalIntegrable (fun x : ℝ => log x) volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'
  have hR := hL.symm.comp_sub_left 1
  simp only [sub_self, sub_zero] at hR
  have h0 : Tendsto (fun x => x * J x) (𝓝[>] 0) (𝓝 0) := by
    have hx : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have h := (hx.mul tendsto_log_one_sub_zero).sub tendsto_mul_log_zero
    simpa only [zero_mul, sub_zero] using h.congr fun _ => by simp only [J]; ring
  have h1 : Tendsto (fun x => (1 - x) * J x) (𝓝[<] 1) (𝓝 0) := by
    have h := (h0.comp tendsto_one_sub_nhdsLT_one).neg
    simpa only [Function.comp_def, hodd, mul_neg, neg_neg, neg_zero] using h
  have hD (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt J (-(1 : ℝ) / (x * (1 - x))) x := by
    have hc := (sub_pos.mpr hx.2).ne'
    refine ((((hasDerivAt_id' x).const_sub 1).log hc).sub
      (hasDerivAt_log hx.1.ne')).congr_deriv ?_
    field_simp [hx.1.ne', hc]
    ring
  simpa only [one_mul] using integral_i10K2_interpolation_of_primitive hg hg'
    (J := J) (W := fun _ => 1) hD (hR.sub hL) intervalIntegrable_const h0 h1 hodd

end QED.ThreeLoopE
