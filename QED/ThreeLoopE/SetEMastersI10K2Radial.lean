/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI10K2Join
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import QED.ThreeLoopD.SetDMastersI9RemKuIBP

/-!
# Integration of the logarithmic joining kernel over the cut rectangle

Use the fraction and the sum of the two distances as coordinates.
The shorter of the two rectangle bounds controls the radial interval.
-/

@[expose] public section

open Real Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopE

private def radialMap (q : ℝ × ℝ) : ℝ × ℝ := (q.1 * q.2, (1 - q.1) * q.2)

private noncomputable def radialMax (t x : ℝ) : ℝ :=
  min (t / x) ((1 - t) / (1 - x))

private def radialRegion (t : ℝ) : Set (ℝ × ℝ) :=
  {q | q.1 ∈ Ioo 0 1 ∧ q.2 ∈ Ioo 0 (radialMax t q.1)}

private theorem measurableSet_radialRegion (t : ℝ) : MeasurableSet (radialRegion t) := by
  have h : Measurable (fun q : ℝ × ℝ => radialMax t q.1) := by
    unfold radialMax
    fun_prop
  exact (measurable_fst measurableSet_Ioo).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd h))

private theorem radialMax_pos {t x : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < radialMax t x :=
  lt_min (div_pos ht.1 hx.1) (div_pos (sub_pos.mpr ht.2) (sub_pos.mpr hx.2))

private theorem radialMax_of_le {t x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (h : x ≤ t) :
    radialMax t x = (1 - t) / (1 - x) := by
  refine min_eq_right ((div_le_div_iff₀ (sub_pos.mpr hx.2) hx.1).2 ?_)
  linarith only [h, show (1 - t) * x = x - t * x by ring,
    show t * (1 - x) = t - t * x by ring]

private theorem radialMax_of_ge {t x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (h : t ≤ x) :
    radialMax t x = t / x := by
  refine min_eq_left ((div_le_div_iff₀ hx.1 (sub_pos.mpr hx.2)).2 ?_)
  linarith only [h, show (1 - t) * x = x - t * x by ring,
    show t * (1 - x) = t - t * x by ring]

private theorem radialMax_le_one {t x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    radialMax t x ≤ 1 := by
  rcases le_total x t with h | h
  · rw [radialMax_of_le hx h, div_le_one (sub_pos.mpr hx.2)]
    linarith only [h]
  · rw [radialMax_of_ge hx h, div_le_one hx.1]
    exact h

private theorem image_radialMap (t : ℝ) :
    radialMap '' radialRegion t = Ioo 0 t ×ˢ Ioo 0 (1 - t) := by
  ext p
  constructor
  · rintro ⟨⟨x, v⟩, ⟨hx, hv⟩, rfl⟩
    have h₁ := lt_of_lt_of_le hv.2 (min_le_left (t / x) ((1 - t) / (1 - x)))
    have h₂ := lt_of_lt_of_le hv.2 (min_le_right (t / x) ((1 - t) / (1 - x)))
    refine ⟨⟨mul_pos hx.1 hv.1, ?_⟩, ⟨mul_pos (sub_pos.mpr hx.2) hv.1, ?_⟩⟩
    · change x * v < t
      rw [mul_comm]
      exact (lt_div_iff₀ hx.1).1 h₁
    · change (1 - x) * v < 1 - t
      rw [mul_comm]
      exact (lt_div_iff₀ (sub_pos.mpr hx.2)).1 h₂
  · intro hp
    let v := p.1 + p.2
    let x := p.1 / v
    have hv : 0 < v := add_pos hp.1.1 hp.2.1
    have hx : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos hp.1.1 hv, (div_lt_one hv).2 (lt_add_of_pos_right _ hp.2.1)⟩
    have e₁ : x * v = p.1 := div_mul_cancel₀ _ hv.ne'
    have e₂ : (1 - x) * v = p.2 := by rw [sub_mul, one_mul, e₁]; exact add_sub_cancel_left _ _
    refine ⟨(x, v), ⟨hx, hv, lt_min ?_ ?_⟩, Prod.ext e₁ e₂⟩
    · apply (lt_div_iff₀ hx.1).2
      rw [mul_comm, e₁]
      exact hp.1.2
    · apply (lt_div_iff₀ (sub_pos.mpr hx.2)).2
      rw [mul_comm, e₂]
      exact hp.2.2

private theorem injOn_radialMap (t : ℝ) : InjOn radialMap (radialRegion t) := by
  intro p hp q _ h
  have hv : p.2 = q.2 := by
    have e₁ := congrArg Prod.fst h
    have e₂ := congrArg Prod.snd h
    change p.1 * p.2 = q.1 * q.2 at e₁
    change (1 - p.1) * p.2 = (1 - q.1) * q.2 at e₂
    linarith only [e₁, e₂, show (1 - p.1) * p.2 = p.2 - p.1 * p.2 by ring,
      show (1 - q.1) * q.2 = q.2 - q.1 * q.2 by ring]
  refine Prod.ext (mul_right_cancel₀ (ne_of_gt hp.2.1) ?_) hv
  have e := congrArg Prod.fst h
  change p.1 * p.2 = q.1 * q.2 at e
  rwa [← hv] at e

private noncomputable def radialDeriv (q : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (q.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + q.1 • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((-q.2) • ContinuousLinearMap.fst ℝ ℝ ℝ + (1 - q.1) • ContinuousLinearMap.snd ℝ ℝ ℝ)

private theorem hasFDerivAt_radialMap (q : ℝ × ℝ) :
    HasFDerivAt radialMap (radialDeriv q) q := by
  have hx := hasFDerivAt_fst (𝕜 := ℝ) (p := q) (E := ℝ) (F := ℝ)
  have hv := hasFDerivAt_snd (𝕜 := ℝ) (p := q) (E := ℝ) (F := ℝ)
  have h := (hx.mul hv).prodMk (((hasFDerivAt_const (1 : ℝ) q).sub hx).mul hv)
  have he : radialMap = fun p : ℝ × ℝ => (p.1 * p.2, (1 - p.1) * p.2) := rfl
  rw [he]
  refine h.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro p
  apply Prod.ext
  · simp [radialDeriv]
    ring
  · simp [radialDeriv]
    ring

private theorem det_radialDeriv (q : ℝ × ℝ) : (radialDeriv q).det = q.2 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ),
    Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, radialDeriv]
  ring

private theorem integrableOn_joinLog :
    IntegrableOn i10K2JoinLog (Ioo (0 : ℝ) 1) := by
  have h₁ := QED.ThreeLoopD.integrableOn_log_sq_i9Ku
  have h₂ := QED.ThreeLoopD.integrableOn_log_one_sub_sq_i9Ku
  have hC : ContinuousOn Li₂ (Icc (0 : ℝ) 1) :=
    continuousOn_Li₂.mono (Icc_subset_Icc_left (by norm_num))
  have hCr : ContinuousOn (fun x => Li₂ (1 - x)) (Icc (0 : ℝ) 1) :=
    hC.comp (continuousOn_const.sub continuousOn_id)
      (fun x hx => ⟨sub_nonneg.mpr hx.2, sub_le_self _ hx.1⟩)
  rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at h₁ h₂ ⊢
  rw [← uIcc_of_le zero_le_one] at hC hCr
  exact (((h₂.sub h₁).div_const 2).add hC.intervalIntegrable).sub hCr.intervalIntegrable

private theorem integrableOn_radial (t : ℝ) :
    IntegrableOn (fun q : ℝ × ℝ => q.2 * i10K2JoinLog q.1) (radialRegion t) := by
  have hi : IntegrableOn (fun v : ℝ => v) (Ioo 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1
      (continuous_id.intervalIntegrable 0 1)
  have h : IntegrableOn (fun q : ℝ × ℝ => i10K2JoinLog q.1 * q.2)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo 0 1) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact integrableOn_joinLog.mul_prod hi
  have hs : radialRegion t ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioo 0 1 := fun _ hq =>
    ⟨hq.1, hq.2.1, hq.2.2.trans_le (radialMax_le_one hq.1)⟩
  simpa only [mul_comm] using h.mono_set hs

/-- The weighted joining kernel has a finite absolute integral on the cut rectangle. -/
theorem integrableOn_i10K2JoinLog_rectangle (t : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => i10K2JoinLog (p.1 / (p.1 + p.2)))
      (Ioo 0 t ×ˢ Ioo 0 (1 - t)) := by
  let f := fun p : ℝ × ℝ => i10K2JoinLog (p.1 / (p.1 + p.2))
  have hD q (_ : q ∈ radialRegion t) :=
    (hasFDerivAt_radialMap q).hasFDerivWithinAt (s := radialRegion t)
  have hS := measurableSet_radialRegion t
  have : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  change IntegrableOn f _
  rw [← image_radialMap, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    volume hS hD (injOn_radialMap t)]
  apply (integrableOn_radial t).congr_fun _ hS
  intro p hp
  have hv : 0 < p.2 := hp.2.1
  have e : (radialMap p).1 / ((radialMap p).1 + (radialMap p).2) = p.1 := by
    simp only [radialMap]
    rw [show p.1 * p.2 + (1 - p.1) * p.2 = p.2 by ring, mul_div_cancel_right₀ _ hv.ne']
  simp only [f, det_radialDeriv, abs_of_pos hv, smul_eq_mul, e]

/-- Integration along the radial variable in the logarithmic cut density. -/
private theorem integral_joinLog_rectangle {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ p in Ioo 0 t ×ˢ Ioo 0 (1 - t), i10K2JoinLog (p.1 / (p.1 + p.2))) =
      ∫ x in Ioo (0 : ℝ) 1, radialMax t x ^ 2 / 2 * i10K2JoinLog x := by
  let f := fun p : ℝ × ℝ => i10K2JoinLog (p.1 / (p.1 + p.2))
  have hD q (_ : q ∈ radialRegion t) :=
    (hasFDerivAt_radialMap q).hasFDerivWithinAt (s := radialRegion t)
  have hS := measurableSet_radialRegion t
  have : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  change (∫ p in _, f p) = _
  rw [← image_radialMap, integral_image_eq_integral_abs_det_fderiv_smul
    volume hS hD (injOn_radialMap t)]
  have he p (hp : p ∈ radialRegion t) :
      |(radialDeriv p).det| • f (radialMap p) = p.2 * i10K2JoinLog p.1 := by
    have hv : 0 < p.2 := hp.2.1
    have e : (radialMap p).1 / ((radialMap p).1 + (radialMap p).2) = p.1 := by
      simp only [radialMap]
      rw [show p.1 * p.2 + (1 - p.1) * p.2 = p.2 by ring, mul_div_cancel_right₀ _ hv.ne']
    simp only [f, det_radialDeriv, abs_of_pos hv, smul_eq_mul, e]
  rw [setIntegral_congr_fun hS he, ← integral_indicator hS, Measure.volume_eq_prod]
  have hi : Integrable ((radialRegion t).indicator (fun q => q.2 * i10K2JoinLog q.1))
      ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod, integrable_indicator_iff hS]
    exact integrableOn_radial t
  rw [integral_prod _ hi, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · rw [indicator_of_mem hx]
    have he' (v : ℝ) :
        (radialRegion t).indicator (fun q => q.2 * i10K2JoinLog q.1) (x, v) =
          (Ioo 0 (radialMax t x)).indicator (fun v => v * i10K2JoinLog x) v := by
      simp only [indicator_apply, radialRegion, mem_ofPred_eq, hx, true_and]
    simp_rw [he']
    rw [integral_indicator measurableSet_Ioo]
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (radialMax_pos ht hx).le,
      intervalIntegral.integral_mul_const, integral_id]
    ring
  · rw [indicator_of_notMem hx]
    apply integral_eq_zero_of_ae
    filter_upwards [] with v
    exact indicator_of_notMem (fun h => hx h.1) _

/-- The logarithmic joining density from the two ordered bubble regions. -/
theorem integral_i10K2JoinLog_rectangle {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    2 * (∫ p in Ioo 0 t ×ˢ Ioo 0 (1 - t), i10K2JoinLog (p.1 / (p.1 + p.2))) =
      t ^ 2 * (1 - i10K2JoinLogRadialPrim t) -
        (1 - t) ^ 2 * (1 - i10K2JoinLogRadialPrim (1 - t)) := by
  let c := 1 - t
  let F := fun x => radialMax t x ^ 2 / 2 * i10K2JoinLog x
  let K := fun x => i10K2JoinLog x / x ^ 2
  have hc : c ∈ Ioo (0 : ℝ) 1 := ⟨sub_pos.mpr ht.2, sub_lt_self _ ht.1⟩
  obtain ⟨hK, hT⟩ := integral_i10K2JoinLog_radial ht
  obtain ⟨hKc, hC⟩ := integral_i10K2JoinLog_radial hc
  have hodd (x : ℝ) : i10K2JoinLog (1 - x) = -i10K2JoinLog x := by
    simp only [i10K2JoinLog, sub_sub_cancel]
    ring
  have hL : EqOn (fun x => -(c ^ 2 / 2) * K (1 - x)) F (uIoo 0 t) := by
    intro x hx
    rw [uIoo_of_le ht.1.le] at hx
    have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, hx.2.trans ht.2⟩
    dsimp only [K, F]
    rw [radialMax_of_le hx' hx.2.le, hodd, div_pow]
    ring
  have hR : EqOn (fun x => (t ^ 2 / 2) * K x) F (uIoo t 1) := by
    intro x hx
    rw [uIoo_of_le ht.2.le] at hx
    have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨ht.1.trans hx.1, hx.2⟩
    dsimp only [K, F]
    rw [radialMax_of_ge hx' hx.1.le, div_pow]
    ring
  have hIL : IntervalIntegrable (fun x => -(c ^ 2 / 2) * K (1 - x)) volume 0 t := by
    have h := (hKc.symm.const_mul (-(c ^ 2 / 2))).comp_sub_left 1
    simpa only [sub_self, sub_sub_cancel, show 1 - c = t by simp [c]] using h
  have hIR : IntervalIntegrable (fun x => (t ^ 2 / 2) * K x) volume t 1 :=
    hK.const_mul _
  rw [integral_joinLog_rectangle ht, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]
  change 2 * (∫ x in (0 : ℝ)..1, F x) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hIL.congr_uIoo hL)
    (hIR.congr_uIoo hR), ← intervalIntegral.integral_congr_uIoo hL,
    ← intervalIntegral.integral_congr_uIoo hR]
  have e : (∫ x in (0 : ℝ)..t, -(c ^ 2 / 2) * K (1 - x)) =
      -(c ^ 2 / 2) * (∫ x in c..1, K x) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left, sub_zero]
  rw [e, intervalIntegral.integral_const_mul, hT, hC]
  ring

end QED.ThreeLoopE
