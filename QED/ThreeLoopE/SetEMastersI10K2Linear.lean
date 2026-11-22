/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI10K2Inner
import QED.ThreeLoopE.SetEMastersI10K2Join
import QED.ThreeLoopE.SetEMastersI10LogMoment

/-!
# The linear coefficient of the second remainder

Order the bubble parameters and apply Fubini on the region between them.
The two distances from the cut give the unweighted joining density.
-/

@[expose] public section

open Real Set MeasureTheory

namespace QED.ThreeLoopE

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

private theorem cut_integrableOn {t : ℝ} (ht : t ∈ unitInterval) :
    IntegrableOn (fun r => log (r - t)) (Ioo t 1) ∧
      IntegrableOn (fun s => log (t - s)) (Ioo 0 t) := by
  have hr := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1 - t)).comp_sub_right t
  have hs := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := t)).symm.comp_sub_left t
  simp only [zero_add, sub_add_cancel, sub_self, sub_zero] at hr hs
  exact ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le ht.2.le).1 hr,
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1.le).1 hs⟩

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

private noncomputable def cutLinear (q : ℝ × (ℝ × ℝ)) : ℝ :=
  deriv i10K2PsiOne q.1 * (log (q.2.1 - q.1) - log (q.1 - q.2.2))

private noncomputable def cutBound (q : ℝ × (ℝ × ℝ)) : ℝ :=
  (2 / q.1) * (-log (q.2.1 - q.1) - log (q.1 - q.2.2))

private theorem cut_section {t : ℝ} (ht : t ∈ unitInterval) :
    IntegrableOn (fun p => cutLinear (t, p)) (cutRectangle t) ∧
      IntegrableOn (fun p => cutBound (t, p)) (cutRectangle t) := by
  obtain ⟨hr, hs⟩ := cut_integrableOn ht
  have hr₀ : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo t 1) :=
    integrableOn_const (measure_Ioo_lt_top.ne)
  have hs₀ : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 t) :=
    integrableOn_const (measure_Ioo_lt_top.ne)
  unfold cutRectangle
  simp only [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have h₁ := hr.mul_prod hs₀
  have h₂ := hr₀.mul_prod hs
  have h₁' : Integrable (fun p : ℝ × ℝ => log (p.1 - t))
      ((volume.restrict (Ioo t 1)).prod (volume.restrict (Ioo 0 t))) := by
    simpa only [mul_one] using h₁
  have h₂' : Integrable (fun p : ℝ × ℝ => log (t - p.2))
      ((volume.restrict (Ioo t 1)).prod (volume.restrict (Ioo 0 t))) := by
    simpa only [one_mul] using h₂
  constructor
  · simpa only [cutLinear, Pi.sub_apply] using
      (h₁'.sub h₂').const_mul (deriv i10K2PsiOne t)
  · simpa only [cutBound, Pi.sub_apply, Pi.neg_apply] using
      (h₁'.neg.sub h₂').const_mul (2 / t)

private theorem cut_bound {t : ℝ} (ht : t ∈ unitInterval) {p : ℝ × ℝ}
    (hp : p ∈ cutRectangle t) : ‖cutLinear (t, p)‖ ≤ cutBound (t, p) := by
  have ha := log_nonpos (sub_pos.mpr hp.2.2).le (by linarith [ht.2, hp.2.1])
  have hb := log_nonpos (sub_pos.mpr hp.1.1).le (by linarith [hp.1.2, ht.1])
  have h := abs_sub (log (p.1 - t)) (log (t - p.2))
  rw [abs_of_nonpos ha, abs_of_nonpos hb] at h
  simp only [cutLinear, cutBound, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (abs_deriv_i10K2PsiOne_le ht) (by linarith)
    (abs_nonneg _) (div_nonneg (by norm_num) ht.1.le)

private theorem integral_cut_bound {t : ℝ} (ht : t ∈ unitInterval) :
    (∫ p in cutRectangle t, cutBound (t, p)) =
      2 * (1 - t) * (2 - log t - log (1 - t)) := by
  rw [cut_rectangle_integral ht (cut_section ht).2]
  let c := 1 - t
  have hc : 0 < c := sub_pos.mpr ht.2
  have h (a : ℝ) : (∫ b in (0 : ℝ)..c, (2 / t) * (-log b - log a)) =
      (2 / t) * (- (c * (log c - 1)) - c * log a) := by
    have hlog : IntervalIntegrable (fun b : ℝ => -log b) volume 0 c :=
      intervalIntegral.intervalIntegrable_log'.neg
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      hlog intervalIntegrable_const, intervalIntegral.integral_neg,
      integral_log_from_zero_of_pos hc, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  simp only [cutBound, add_sub_cancel_right, sub_sub_cancel]
  change (∫ a in (0 : ℝ)..t, ∫ b in (0 : ℝ)..c, (2 / t) * (-log b - log a)) = _
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    intervalIntegrable_const (intervalIntegral.intervalIntegrable_log'.const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_log_from_zero_of_pos ht.1]
  simp only [sub_zero, smul_eq_mul]
  dsimp only [c]
  field_simp [ht.1.ne']
  ring

private theorem integrable_cut_bound :
    Integrable (cutRegion.indicator cutBound) ((volume.restrict unitInterval).prod volume) := by
  have hm : Measurable cutBound := by
    unfold cutBound
    fun_prop
  apply (integrable_prod_iff
    (hm.indicator measurableSet_cutRegion).aestronglyMeasurable).2
  constructor
  · apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    change Integrable ((cutRectangle t).indicator (fun p => cutBound (t, p))) _
    have hs : MeasurableSet (cutRectangle t) := measurableSet_Ioo.prod measurableSet_Ioo
    exact (integrable_indicator_iff hs).2 (cut_section ht).2
  · have hl : IntervalIntegrable log volume (0 : ℝ) 1 :=
      intervalIntegral.intervalIntegrable_log'
    have hr := hl.symm.comp_sub_left 1
    simp only [sub_zero, sub_self] at hr
    have hC : ContinuousOn (fun t : ℝ => 2 * (1 - t)) (uIcc (0 : ℝ) 1) := by fun_prop
    have h₂ : IntervalIntegrable (fun _ => (2 : ℝ)) volume 0 1 := intervalIntegrable_const
    have hi := ((h₂.sub hl).sub hr).continuousOn_mul hC
    apply ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 hi).congr
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    change 2 * (1 - t) * (2 - log t - log (1 - t)) =
      ∫ p, ‖(cutRectangle t).indicator (fun p => cutBound (t, p)) p‖
    have hs : MeasurableSet (cutRectangle t) := measurableSet_Ioo.prod measurableSet_Ioo
    rw [← integral_cut_bound ht, ← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [] with p
    by_cases hp : p ∈ cutRectangle t
    · simp only [indicator_of_mem hp, Real.norm_eq_abs]
      exact (abs_of_nonneg ((norm_nonneg _).trans (cut_bound ht hp))).symm
    · simp only [indicator_of_notMem hp, norm_zero]

private theorem integrable_cut_linear :
    Integrable (cutRegion.indicator cutLinear) ((volume.restrict unitInterval).prod volume) := by
  have hm : Measurable cutLinear := by
    unfold cutLinear
    have hd := measurable_deriv (f := i10K2PsiOne)
    fun_prop
  have hb : Measurable cutBound := by
    unfold cutBound
    fun_prop
  refine integrable_cut_bound.mono' (hm.indicator measurableSet_cutRegion).aestronglyMeasurable ?_
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le
    (hm.indicator measurableSet_cutRegion).norm
    (hb.indicator measurableSet_cutRegion))).2
  apply ae_restrict_of_forall_mem measurableSet_Ioo
  intro t ht
  filter_upwards [] with p
  by_cases hp : (t, p) ∈ cutRegion
  · simpa only [indicator_of_mem hp] using cut_bound ht hp
  · simp only [indicator_of_notMem hp, norm_zero, le_refl]

private noncomputable def orientedLinear (p : ℝ × ℝ) : ℝ :=
  ∫ t in p.2..p.1, cutLinear (t, p)

private theorem orientedLinear_swap (p : ℝ × ℝ) :
    orientedLinear p.swap = orientedLinear p := by
  rcases p with ⟨r, s⟩
  unfold orientedLinear
  rw [intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro t _
  change -(deriv i10K2PsiOne t * (log (s - t) - log (t - r))) = _
  rw [show s - t = -(t - s) by ring, show t - r = -(r - t) by ring,
    log_neg_eq_log, log_neg_eq_log]
  simp only [cutLinear]
  ring

private theorem integral_cut_linear_bubbles :
    (∫ q, cutRegion.indicator cutLinear q ∂(volume.restrict unitInterval).prod volume) =
      ∫ p in unitInterval ×ˢ unitInterval,
        {p : ℝ × ℝ | p.2 < p.1}.indicator orientedLinear p := by
  rw [integral_prod_symm _ integrable_cut_linear, ← integral_indicator
    (measurableSet_Ioo.prod measurableSet_Ioo)]
  apply integral_congr_ae
  filter_upwards [] with p
  by_cases hp : p ∈ unitInterval ×ˢ unitInterval
  · rw [indicator_of_mem hp]
    by_cases h : p.2 < p.1
    · rw [indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.2 < p.1} from h)]
      unfold orientedLinear
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

/-- The first coefficient of the subtracted second remainder. -/
theorem integral_i10K2CoeffOne :
    ∫ p in i10K2Domain, i10K2CoeffOne p = -5 - π ^ 2 + 12 * QED.Polylog.zeta3 := by
  obtain ⟨hi, he⟩ := integral_i10K2CoeffOne_joined
  change IntegrableOn orientedLinear _ at hi
  rw [he]
  change (∫ p in unitInterval ×ˢ unitInterval, orientedLinear p) = _
  let T := {p : ℝ × ℝ | p.2 < p.1}
  let U := {p : ℝ × ℝ | p.1 < p.2}
  have hT : MeasurableSet T := measurableSet_lt measurable_snd measurable_fst
  have hU : MeasurableSet U := measurableSet_lt measurable_fst measurable_snd
  have hsum (p : ℝ × ℝ) :
      orientedLinear p = T.indicator orientedLinear p + U.indicator orientedLinear p := by
    rcases lt_trichotomy p.2 p.1 with h | h | h
    · have h₁ : p ∈ T := h
      have h₂ : p ∉ U := h.asymm
      simp only [indicator_of_mem h₁, indicator_of_notMem h₂, add_zero]
    · have h₁ : p ∉ T := by simp [T, h]
      have h₂ : p ∉ U := by simp [U, h]
      simp only [indicator_of_notMem h₁, indicator_of_notMem h₂, add_zero,
        orientedLinear, h, intervalIntegral.integral_same]
    · have h₁ : p ∉ T := h.asymm
      have h₂ : p ∈ U := h
      simp only [indicator_of_mem h₂, indicator_of_notMem h₁, zero_add]
  have hswap : (∫ p in unitInterval ×ˢ unitInterval, U.indicator orientedLinear p) =
      ∫ p in unitInterval ×ˢ unitInterval, T.indicator orientedLinear p := by
    simp only [Measure.volume_eq_prod]
    rw [← setIntegral_prod_swap]
    apply integral_congr_ae
    filter_upwards [] with p
    by_cases hp : p ∈ T
    · rw [indicator_of_mem hp, indicator_of_mem (show p.swap ∈ U from hp), orientedLinear_swap]
    · rw [indicator_of_notMem hp, indicator_of_notMem (show p.swap ∉ U from hp)]
  calc
    _ = 2 * (∫ p in unitInterval ×ˢ unitInterval, T.indicator orientedLinear p) := by
      simp_rw [hsum]
      rw [integral_add (hi.indicator hT) (hi.indicator hU), hswap, two_mul]
    _ = 2 * (∫ q, cutRegion.indicator cutLinear q ∂(volume.restrict unitInterval).prod volume) :=
      congrArg (2 * ·) integral_cut_linear_bubbles.symm
    _ = _ := by
      rw [integral_prod _ integrable_cut_linear, ← integral_const_mul]
      refine (setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_).trans
        integral_i10K2_linear_density
      change 2 * (∫ p, (cutRectangle t).indicator (fun p => cutLinear (t, p)) p) = _
      have hs : MeasurableSet (cutRectangle t) := measurableSet_Ioo.prod measurableSet_Ioo
      rw [integral_indicator hs, cut_rectangle_integral ht (cut_section ht).1]
      simp only [cutLinear, add_sub_cancel_right, sub_sub_cancel,
        intervalIntegral.integral_const_mul]
      change 2 * (deriv i10K2PsiOne t *
        (∫ a in (0 : ℝ)..t, ∫ b in (0 : ℝ)..(1 - t), log b - log a)) =
        2 * t * (1 - t) * (log (1 - t) - log t) * deriv i10K2PsiOne t
      rw [mul_left_comm, integral_i10K2Join_density ht]
      ring

end QED.ThreeLoopE
