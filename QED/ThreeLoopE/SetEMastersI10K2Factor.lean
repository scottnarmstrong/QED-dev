/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI10KabAn
public import QED.ThreeLoopD.SetDMastersLaurent
import QED.ThreeLoopD.SetDMastersI9KTaylor
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Difference quotient for the second subtracted remainder of the master `I₁₀`

At zero, the integrand of `ψ(t)` is `u - 1` and is independent of `t`.
Consequently the linear interpolation subtraction vanishes pointwise,
before either the inner or the outer integral. The continued difference
quotient implements the exact factorization by `ε`.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology QED.DimReg QED.ThreeLoopD

namespace QED.ThreeLoopE

theorem i10Tau_mem_Ioo {z r s : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) : i10Tau z r s ∈ Ioo (0 : ℝ) 1 := by
  have hzc : 0 < 1 - z := sub_pos.mpr hz.2
  exact ⟨add_pos (mul_pos hz.1 hr.1) (mul_pos hzc hs.1), by
    unfold i10Tau
    linarith only [mul_lt_mul_of_pos_left hr.2 hz.1, mul_lt_mul_of_pos_left hs.2 hzc]⟩

theorem i10PsiF_zero {t : ℝ} (ht : t ≠ 0) (u : ℝ) :
    i10PsiF 0 t u = (u : ℂ) - 1 := by
  simp only [i10PsiF, neg_zero, cpow_zero, one_mul, zero_sub, cpow_neg_one, mul_zero,
    sub_zero, cpow_one, ofReal_sub, ofReal_one, ofReal_mul]
  field_simp [ofReal_ne_zero.mpr ht]
  ring

/-- The pointwise interpolation subtraction in the integrand of `K₂`. -/
noncomputable def i10K2B (ε : ℂ) (q : ℝ × ℝ × ℝ) (u : ℝ) : ℂ :=
  i10PsiF ε (i10Tau q.1 q.2.1 q.2.2) u -
    (1 - (q.1 : ℂ)) * i10PsiF ε q.2.2 u - (q.1 : ℂ) * i10PsiF ε q.2.1 u

/-- The continued divided integrand of `K₂ / ε`. -/
noncomputable def i10K2H (ε : ℂ) (q : ℝ × ℝ × ℝ) (u : ℝ) : ℂ :=
  i10A ε q.2.1 * i10A ε q.2.2 * i10W ε q.1 *
    dslope (fun w => i10K2B w q u) 0 ε

theorem i10K2B_zero {q : ℝ × ℝ × ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) (u : ℝ) :
    i10K2B 0 q u = 0 := by
  obtain ⟨hz, hr, hs⟩ := hq
  rw [i10K2B, i10PsiF_zero (i10Tau_mem_Ioo hz hr hs).1.ne',
    i10PsiF_zero hs.1.ne', i10PsiF_zero hr.1.ne']
  ring

theorem integrableOn_i10PsiF {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : IntegrableOn (i10PsiF ε t) (Ioo (0 : ℝ) 1) := by
  have hI := (integrableOn_rpow_Ioo (by norm_num : -(1 / 20 : ℝ) > -1)).const_mul
    (8 * t ^ (-(11 / 20) : ℝ))
  refine hI.mono' (Measurable.aestronglyMeasurable ?_) ?_
  · unfold i10PsiF
    fun_prop
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun u hu => ?_
    exact (norm_i10PsiF_le hε ht hu).trans_eq (by ring)

theorem integral_i10K2B_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {q : ℝ × ℝ × ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :
    (∫ u in Ioo (0 : ℝ) 1, i10K2B ε q u) =
      i10Psi ε (i10Tau q.1 q.2.1 q.2.2) -
        (1 - (q.1 : ℂ)) * i10Psi ε q.2.2 - (q.1 : ℂ) * i10Psi ε q.2.1 := by
  obtain ⟨hz, hr, hs⟩ := hq
  have ht := integrableOn_i10PsiF hε (i10Tau_mem_Ioo hz hr hs)
  have hr' := (integrableOn_i10PsiF hε hr).const_mul (q.1 : ℂ)
  have hs' := (integrableOn_i10PsiF hε hs).const_mul (1 - (q.1 : ℂ))
  simp only [i10K2B, i10Psi_eq]
  calc
    _ = (∫ u in Ioo (0 : ℝ) 1,
        i10PsiF ε (i10Tau q.1 q.2.1 q.2.2) u - (1 - (q.1 : ℂ)) * i10PsiF ε q.2.2 u) -
          ∫ u in Ioo (0 : ℝ) 1, (q.1 : ℂ) * i10PsiF ε q.2.1 u :=
      integral_sub (ht.sub hs') hr'
    _ = _ := by rw [integral_sub ht hs', integral_const_mul, integral_const_mul]

theorem i10K2_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 20) :
    i10K2 ε = ε * ∫ q in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1),
      ∫ u in Ioo (0 : ℝ) 1, i10K2H ε q u := by
  rw [i10K2, ← integral_const_mul]
  apply setIntegral_congr_fun (measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo))
  intro q hq
  dsimp only
  rw [← integral_i10K2B_eq hε hq, ← integral_const_mul, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u _
  dsimp only
  have h := sub_smul_dslope (fun w => i10K2B w q u) 0 ε
  simp only [sub_zero, smul_eq_mul, i10K2B_zero hq] at h
  rw [i10K2H, ← h]
  ring

theorem i10K2_zero : i10K2 0 = 0 := by
  rw [i10K2_eq (by simp : ‖(0 : ℂ)‖ < 1 / 20), zero_mul]

theorem differentiable_i10PsiF {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) : Differentiable ℂ fun ε => i10PsiF ε t u := by
  have hp : 0 < 1 - (1 - u) * t := by
    nlinarith only [ht.2, mul_pos ht.1 hu.1]
  have hc {x : ℝ} (hx : 0 < x) {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
      Differentiable ℂ fun ε => (x : ℂ) ^ (f ε) :=
    fun ε => (hf ε).const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))
  unfold i10PsiF
  exact (hc hu.1 differentiable_neg).mul
    ((hc ht.1 (differentiable_id.sub_const 1)).mul
      ((hc hp ((differentiable_const (1 : ℂ)).sub (differentiable_id.const_mul 3))).sub_const 1))

theorem differentiable_i10K2H {q : ℝ × ℝ × ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) : Differentiable ℂ fun ε => i10K2H ε q u := by
  obtain ⟨hz, hr, hs⟩ := hq
  have hb : Differentiable ℂ fun ε => i10K2B ε q u := by
    unfold i10K2B
    exact (((differentiable_i10PsiF (i10Tau_mem_Ioo hz hr hs) hu).sub
      ((differentiable_i10PsiF hs hu).const_mul _)).sub
      ((differentiable_i10PsiF hr hu).const_mul _))
  have hd : Differentiable ℂ (dslope (fun ε => i10K2B ε q u) 0) := by
    have h := (differentiableOn_dslope (c := (0 : ℂ)) (s := univ) univ_mem).mpr
      hb.differentiableOn
    exact fun ε => (h ε (mem_univ _)).differentiableAt univ_mem
  have ha {x : ℝ} (hx : x < 1) : Differentiable ℂ fun ε => i10A ε x := by
    have hp : 0 < 1 - x := sub_pos.mpr hx
    exact fun ε => differentiableAt_id.neg.const_cpow (Or.inl (ofReal_ne_zero.mpr hp.ne'))
  have hw : Differentiable ℂ fun ε => i10W ε q.1 := fun ε =>
    (differentiableAt_id.sub_const _).const_cpow (Or.inl (ofReal_ne_zero.mpr (i9_c_pos hz).ne'))
  unfold i10K2H
  exact (((ha hr.2).mul (ha hs.2)).mul hw).mul hd

/-- The quotient in `ψ` is a normalized integral of a power with exponent `-3 ε`. -/
theorem i10PsiF_eq_average {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {t u : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    i10PsiF ε t u =
      -((1 - u : ℝ) : ℂ) * (1 - 3 * ε) * (u : ℂ) ^ (-ε) * (t : ℂ) ^ ε *
        ∫ v in (0 : ℝ)..1, ((1 - v * ((1 - u) * t) : ℝ) : ℂ) ^ (-3 * ε) := by
  set a := (1 - u) * t with ha
  have hupos := sub_pos.mpr hu.2
  have ha₀ : 0 < a := mul_pos hupos ht.1
  have ha₁ : a < 1 := by nlinarith only [ht.2, mul_pos hu.1 ht.1]
  have hα : (1 : ℂ) - 3 * ε ≠ 0 := by
    intro h
    have hr := i10_re_le hε
    have hp := congrArg Complex.re h
    simp at hp
    linarith
  have hc : ContinuousOn (fun v : ℝ => ((1 - v * a : ℝ) : ℂ) ^ (-3 * ε))
      (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    intro v hv
    have hp : 0 < 1 - v * a := by nlinarith only [ha₀, ha₁, hv.2]
    have hcont : ContinuousAt (fun v : ℝ => 1 - v * a) v := by fun_prop
    have H := continuousAt_ofReal_cpow_const (1 - v * a) (-3 * ε) (Or.inr hp.ne')
    exact (H.comp (f := fun x : ℝ => 1 - x * a) hcont).continuousWithinAt
  have hd : ∀ v ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => ((1 - v * a : ℝ) : ℂ) ^ (1 - 3 * ε))
        (-(a : ℂ) * (1 - 3 * ε) * ((1 - v * a : ℝ) : ℂ) ^ (-3 * ε)) v := by
    rw [uIcc_of_le zero_le_one]
    intro v hv
    have hp : 0 < 1 - v * a := by nlinarith only [ha₀, ha₁, hv.2]
    have hinner : HasDerivAt (fun v : ℝ => 1 - v * a) (-a) v := by
      simpa only [one_mul, id_eq] using ((hasDerivAt_id v).mul_const a).const_sub (1 : ℝ)
    have hh := (hasDerivAt_ofReal_cpow_const hp.ne' hα).scomp v hinner
    change HasDerivAt (fun v : ℝ => ((1 - v * a : ℝ) : ℂ) ^ (1 - 3 * ε)) _ v at hh
    refine hh.congr_deriv ?_
    rw [show 1 - 3 * ε - 1 = -3 * ε by ring, Complex.real_smul, ofReal_neg, mul_assoc]
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hc.const_mul _).intervalIntegrable
  rw [intervalIntegral.integral_const_mul] at hint
  simp only [one_mul, zero_mul, sub_zero, ofReal_one, one_cpow] at hint
  have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
  have htp : (t : ℂ) ^ (ε - 1) * (t : ℂ) = (t : ℂ) ^ ε := by
    calc
      _ = (t : ℂ) ^ (ε - 1) * (t : ℂ) ^ (1 : ℂ) := by rw [cpow_one]
      _ = _ := by rw [← cpow_add _ _ htC, sub_add_cancel]
  rw [i10PsiF, ← ha, ← hint, ha, ofReal_mul, ← htp]
  ring

/-- The normalized bound reduces the singularity at `t = 0` to the power `t^(-1/20)`. -/
theorem norm_i10PsiF_le_normalized {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {t u : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    ‖i10PsiF ε t u‖ ≤ 2 * (u ^ (-(1 / 5) : ℝ) * t ^ (-(1 / 20) : ℝ)) := by
  have hr := i10_re_le hε
  have hr' := (i9_eps_facts hε).2.2.1
  have hnonneg := (sub_pos.mpr hu.2).le
  have h₁ : ‖-((1 - u : ℝ) : ℂ)‖ ≤ 1 := by
    rw [norm_neg, norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    linarith [hu.1]
  have h₂ : ‖1 - 3 * ε‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_one, show ‖(3 : ℂ)‖ = 3 by norm_num]
    linarith
  have h₃ : ‖(u : ℂ) ^ (-ε)‖ ≤ u ^ (-(1 / 20) : ℝ) :=
    norm_cpow_le_rpow_of_le hu.1 hu.2.le (by simp; linarith)
  have h₄ : ‖(t : ℂ) ^ ε‖ ≤ t ^ (-(1 / 20) : ℝ) :=
    norm_cpow_le_rpow_of_le ht.1 ht.2.le hr'
  have h₅ : ‖∫ v in (0 : ℝ)..1, ((1 - v * ((1 - u) * t) : ℝ) : ℂ) ^ (-3 * ε)‖ ≤
      u ^ (-(3 / 20) : ℝ) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := u ^ (-(3 / 20) : ℝ))
      (f := fun v => ((1 - v * ((1 - u) * t) : ℝ) : ℂ) ^ (-3 * ε)) (by
        rw [uIoc_of_le zero_le_one]
        intro v hv
        have ha : 0 ≤ (1 - u) * t := mul_nonneg hnonneg ht.1.le
        have hv' := mul_le_of_le_one_left ha hv.2
        have ht' := mul_le_of_le_one_right hnonneg ht.2.le
        have hp : u ≤ 1 - v * ((1 - u) * t) := by linarith
        have hp₁ : 1 - v * ((1 - u) * t) ≤ 1 := by
          linarith only [mul_nonneg hv.1.le ha]
        exact (norm_cpow_le_rpow_of_le (hu.1.trans_le hp) hp₁ (by simp; linarith)).trans
          (Real.rpow_le_rpow_of_nonpos hu.1 hp (by norm_num)))
    simpa only [sub_zero, abs_one, mul_one] using h
  have hu₀ := hu.1.le
  have ht₀ := ht.1.le
  rw [i10PsiF_eq_average hε ht hu, norm_mul, norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ 1 * 2 * u ^ (-(1 / 20) : ℝ) * t ^ (-(1 / 20) : ℝ) * u ^ (-(3 / 20) : ℝ) :=
      mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _) zero_le_one)
        h₃ (norm_nonneg _) (by norm_num)) h₄ (norm_nonneg _) (by positivity)) h₅ (norm_nonneg _)
        (by positivity)
    _ = 2 * ((u ^ (-(1 / 20) : ℝ) * u ^ (-(3 / 20) : ℝ)) * t ^ (-(1 / 20) : ℝ)) := by ring
    _ = _ := by rw [rpow_mul_rpow_eq (c := -(1 / 5)) hu.1 (by norm_num)]

private theorem norm_i10_cpow_sub_le {β : ℂ} {p l x y : ℝ} (hβ : ‖β‖ ≤ 1)
    (hre : -p ≤ β.re) (hp : 0 ≤ p) (hl : 0 < l)
    (hx : x ∈ Icc l 1) (hy : y ∈ Icc l 1) :
    ‖(x : ℂ) ^ β - (y : ℂ) ^ β‖ ≤ l ^ (-p - 1) * |x - y| := by
  by_cases hβ0 : β = 0
  · simp only [hβ0, cpow_zero, sub_self, norm_zero]
    exact mul_nonneg (Real.rpow_nonneg hl.le _) (abs_nonneg _)
  have hd : ∀ t ∈ Icc l 1, HasDerivWithinAt (fun s : ℝ => (s : ℂ) ^ β)
      (β * (t : ℂ) ^ (β - 1)) (Icc l 1) t := fun t ht =>
    (hasDerivAt_ofReal_cpow_const (hl.trans_le ht.1).ne' hβ0).hasDerivWithinAt
  have hb : ∀ t ∈ Icc l 1, ‖β * (t : ℂ) ^ (β - 1)‖ ≤ l ^ (-p - 1) := by
    intro t ht
    rw [norm_mul, ← one_mul (l ^ (-p - 1))]
    apply mul_le_mul hβ _ (norm_nonneg _) zero_le_one
    exact (norm_cpow_le_rpow_of_le (hl.trans_le ht.1) ht.2 (by simp; linarith)).trans
      (Real.rpow_le_rpow_of_nonpos hl ht.1 (by linarith))
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc _ _) hy hx

private theorem i10Psi_average_mem {v u t : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - v * ((1 - u) * t) ∈ Icc u 1 := by
  have h := (sub_pos.mpr hu.2).le
  have h₁ := mul_le_of_le_one_left (mul_nonneg h ht.1.le) hv.2
  have h₂ := mul_le_of_le_one_right h ht.2.le
  exact ⟨by linarith, by linarith only [mul_nonneg hv.1 (mul_nonneg h ht.1.le)]⟩

/-- The spatial difference of the normalized integrand has a linear bound. -/
theorem norm_i10PsiF_sub_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {m x y u : ℝ}
    (hm : 0 < m) (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1)
    (hmx : m ≤ x) (hmy : m ≤ y) (hu : u ∈ Ioo (0 : ℝ) 1) :
    ‖i10PsiF ε x u - i10PsiF ε y u‖ ≤
      4 * (u ^ (-(6 / 5) : ℝ) * m ^ (-(21 / 20) : ℝ) * |x - y|) := by
  let p (t v : ℝ) := (1 - v * ((1 - u) * t))
  let f (t v : ℝ) := (t : ℂ) ^ ε * (p t v : ℂ) ^ (-3 * ε)
  let c : ℂ := -((1 - u : ℝ) : ℂ) * (1 - 3 * ε) * (u : ℂ) ^ (-ε)
  have hc₀ : ‖-((1 - u : ℝ) : ℂ)‖ ≤ 1 := by
    rw [norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hu.2)]
    linarith [hu.1]
  have hc₁ : ‖(3 : ℂ) * ε‖ ≤ 1 := by
    rw [norm_mul, show ‖(3 : ℂ)‖ = 3 by norm_num]
    linarith
  have hc₂ : ‖(1 : ℂ) - 3 * ε‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have hre := i10_re_le hε
  have hre' := (i9_eps_facts hε).2.2.1
  have hneg : -(3 / 20 : ℝ) ≤ (-3 * ε).re := by simp; linarith
  have hc : ‖c‖ ≤ 2 * u ^ (-(1 / 20) : ℝ) := by
    dsimp [c]
    rw [norm_mul, norm_mul, show (2 : ℝ) = 1 * 2 by norm_num]
    exact mul_le_mul (mul_le_mul hc₀ hc₂ (norm_nonneg _) zero_le_one)
      (norm_cpow_le_rpow_of_le hu.1 hu.2.le (by simp; linarith)) (norm_nonneg _) (by norm_num)
  have hcont {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
      ContinuousOn (f t) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    intro v hv
    have hp := hu.1.trans_le (i10Psi_average_mem hv hu ht).1
    have hcon : ContinuousAt (p t) v := by dsimp [p]; fun_prop
    exact ((continuousAt_ofReal_cpow_const (p t v) _ (Or.inr hp.ne')).comp
      (f := p t) hcon).const_mul _ |>.continuousWithinAt
  have he {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
      i10PsiF ε t u = c * ∫ v in (0 : ℝ)..1, f t v := by
    rw [i10PsiF_eq_average hε ht hu]
    simp only [f, p, c, intervalIntegral.integral_const_mul]
    ring
  have ht_change : ‖(x : ℂ) ^ ε - (y : ℂ) ^ ε‖ ≤ m ^ (-(21 / 20) : ℝ) * |x - y| := by
    convert norm_i10_cpow_sub_le (by linarith : ‖ε‖ ≤ 1) hre' (by norm_num) hm
      ⟨hmx, hx.2.le⟩ ⟨hmy, hy.2.le⟩ using 2
    norm_num
  have hy₀ : ‖(y : ℂ) ^ ε‖ ≤ m ^ (-(1 / 20) : ℝ) :=
    (norm_cpow_le_rpow_of_le hy.1 hy.2.le hre').trans
      (Real.rpow_le_rpow_of_nonpos hm hmy (by norm_num))
  have hu₀ := hu.1.le
  have hm₀ := hm.le
  have hu_exp : u ^ (-(3 / 20) : ℝ) ≤ u ^ (-(23 / 20) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hu.1 hu.2.le (by norm_num)
  have hm_exp : m ^ (-(1 / 20) : ℝ) ≤ m ^ (-(21 / 20) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hm (hmx.trans hx.2.le) (by norm_num)
  set M := u ^ (-(23 / 20) : ℝ) * m ^ (-(21 / 20) : ℝ) * |x - y|
  have hb : ∀ v ∈ uIoc (0 : ℝ) 1, ‖f x v - f y v‖ ≤ 2 * M := by
    rw [uIoc_of_le zero_le_one]
    intro v hv
    have hv' : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2⟩
    have hpx : p x v ∈ Icc u 1 := i10Psi_average_mem hv' hu hx
    have hpy : p y v ∈ Icc u 1 := i10Psi_average_mem hv' hu hy
    have hpx₀ : ‖(p x v : ℂ) ^ (-3 * ε)‖ ≤ u ^ (-(3 / 20) : ℝ) :=
      (norm_cpow_le_rpow_of_le (hu.1.trans_le hpx.1) hpx.2 hneg).trans
        (Real.rpow_le_rpow_of_nonpos hu.1 hpx.1 (by norm_num))
    have hpdist : |p x v - p y v| ≤ |x - y| := by
      have hu' : 0 ≤ 1 - u := by linarith [hu.2]
      have hvu : v * (1 - u) ≤ 1 := by nlinarith only [hu.1, hv.2, mul_nonneg hv.1.le hu.1.le]
      rw [show p x v - p y v = -(v * (1 - u) * (x - y)) by dsimp [p]; ring,
        abs_neg, abs_mul, abs_of_nonneg (mul_nonneg hv.1.le hu')]
      exact mul_le_of_le_one_left (abs_nonneg _) hvu
    have hpd : ‖(p x v : ℂ) ^ (-3 * ε) - (p y v : ℂ) ^ (-3 * ε)‖ ≤
        u ^ (-(23 / 20) : ℝ) * |x - y| := by
      have hn : ‖-3 * ε‖ ≤ 1 := by simpa only [neg_mul, norm_neg] using hc₁
      have h := norm_i10_cpow_sub_le hn hneg (by norm_num) hu.1 hpx hpy
      have he : -(3 / 20 : ℝ) - 1 = -(23 / 20) := by norm_num
      rw [he] at h
      exact h.trans (mul_le_mul_of_nonneg_left hpdist (Real.rpow_nonneg hu₀ _))
    have hf : f x v - f y v =
        ((x : ℂ) ^ ε - (y : ℂ) ^ ε) * (p x v : ℂ) ^ (-3 * ε) +
          (y : ℂ) ^ ε * ((p x v : ℂ) ^ (-3 * ε) - (p y v : ℂ) ^ (-3 * ε)) := by
      dsimp [f]
      ring
    rw [hf]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, show 2 * M = M + M by ring]
    apply add_le_add
    · calc
        _ ≤ (m ^ (-(21 / 20) : ℝ) * |x - y|) * u ^ (-(23 / 20) : ℝ) :=
          mul_le_mul ht_change (hpx₀.trans hu_exp) (norm_nonneg _) (by positivity)
        _ = M := by dsimp [M]; ring
    · calc
        _ ≤ m ^ (-(21 / 20) : ℝ) * (u ^ (-(23 / 20) : ℝ) * |x - y|) :=
          mul_le_mul (hy₀.trans hm_exp) hpd (norm_nonneg _) (by positivity)
        _ = M := by dsimp [M]; ring
  have hi : ‖∫ v in (0 : ℝ)..1, f x v - f y v‖ ≤ 2 * M := by
    simpa only [sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [he hx, he hy, ← mul_sub, ← intervalIntegral.integral_sub (hcont hx).intervalIntegrable
    (hcont hy).intervalIntegrable, norm_mul]
  calc
    _ ≤ (2 * u ^ (-(1 / 20) : ℝ)) * (2 * M) :=
      mul_le_mul hc hi (norm_nonneg _) (by positivity)
    _ = 4 * ((u ^ (-(1 / 20) : ℝ) * u ^ (-(23 / 20) : ℝ)) *
        m ^ (-(21 / 20) : ℝ) * |x - y|) := by dsimp [M]; ring
    _ = _ := by rw [rpow_mul_rpow_eq (c := -(6 / 5)) hu.1 (by norm_num)]

private theorem norm_i10PsiF_sub_le_sqrt {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {m x y u : ℝ}
    (hm : 0 < m) (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1)
    (hmx : m ≤ x) (hmy : m ≤ y) (hu : u ∈ Ioo (0 : ℝ) 1) :
    ‖i10PsiF ε x u - i10PsiF ε y u‖ ≤
      4 * (u ^ (-(7 / 10) : ℝ) * m ^ (-(11 / 20) : ℝ) * √|x - y|) := by
  set X := ‖i10PsiF ε x u - i10PsiF ε y u‖
  have hx' := (norm_i10PsiF_le_normalized hε hx hu).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hm hmx (by norm_num))
        (Real.rpow_nonneg hu.1.le (-(1 / 5)))) (by norm_num))
  have hy' := (norm_i10PsiF_le_normalized hε hy hu).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hm hmy (by norm_num))
        (Real.rpow_nonneg hu.1.le (-(1 / 5)))) (by norm_num))
  have h₁ : X ≤ 4 * (u ^ (-(1 / 5) : ℝ) * m ^ (-(1 / 20) : ℝ)) :=
    (norm_sub_le _ _).trans (by linarith only [hx', hy'])
  have h₂ := norm_i10PsiF_sub_le hε hm hx hy hmx hmy hu
  have h₃ : X ^ 2 ≤ (4 * (u ^ (-(1 / 5) : ℝ) * m ^ (-(1 / 20) : ℝ))) *
      (4 * (u ^ (-(6 / 5) : ℝ) * m ^ (-(21 / 20) : ℝ) * |x - y|)) := by
    rw [sq]
    exact mul_le_mul h₁ h₂ (norm_nonneg _) ((norm_nonneg _).trans h₁)
  have hU : (u ^ (-(7 / 10) : ℝ)) ^ 2 =
      u ^ (-(1 / 5) : ℝ) * u ^ (-(6 / 5) : ℝ) := by
    rw [sq, rpow_mul_rpow_eq (c := -(7 / 5)) hu.1 (by norm_num),
      rpow_mul_rpow_eq (c := -(7 / 5)) hu.1 (by norm_num)]
  have hM : (m ^ (-(11 / 20) : ℝ)) ^ 2 =
      m ^ (-(1 / 20) : ℝ) * m ^ (-(21 / 20) : ℝ) := by
    rw [sq, rpow_mul_rpow_eq (c := -(11 / 10)) hm (by norm_num),
      rpow_mul_rpow_eq (c := -(11 / 10)) hm (by norm_num)]
  have hnonneg : 0 ≤ 4 * (u ^ (-(7 / 10) : ℝ) * m ^ (-(11 / 20) : ℝ) * √|x - y|) :=
    mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (Real.rpow_nonneg hu.1.le _)
      (Real.rpow_nonneg hm.le _)) (Real.sqrt_nonneg _))
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) hnonneg two_ne_zero).mp (h₃.trans_eq ?_)
  rw [mul_pow, mul_pow, mul_pow, hU, hM, Real.sq_sqrt (abs_nonneg _)]
  ring

/-- The interpolation bracket gains a square root at both joining faces. -/
theorem norm_i10K2B_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {q : ℝ × ℝ × ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    ‖i10K2B ε q u‖ ≤ 8 * (u ^ (-(7 / 10) : ℝ) *
      (q.2.1 * q.2.2) ^ (-(11 / 20) : ℝ) * √(q.1 * (1 - q.1))) := by
  obtain ⟨hz, hr, hs⟩ := hq
  set z := q.1
  set r := q.2.1
  set s := q.2.2
  have hz' := sub_pos.mpr hz.2
  have hz₀ := hz.1
  have hz₁ := hz.2
  have hr₀ := hr.1
  have hr₁ := hr.2
  have hs₀ := hs.1
  have hs₁ := hs.2
  have hm := mul_pos hr₀ hs₀
  have hmr : r * s ≤ r := mul_le_of_le_one_right hr₀.le hs₁.le
  have hms : r * s ≤ s := mul_le_of_le_one_left hs₀.le hr₁.le
  have ht := i10Tau_mem_Ioo (z := z) hz hr hs
  have hmt : r * s ≤ i10Tau z r s := by
    unfold i10Tau
    nlinarith only [mul_le_mul_of_nonneg_left hmr hz₀.le, mul_le_mul_of_nonneg_left hms hz'.le]
  have hrs : |r - s| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hts : |i10Tau z r s - s| ≤ z := by
    rw [show i10Tau z r s - s = z * (r - s) by unfold i10Tau; ring, abs_mul, abs_of_pos hz₀]
    exact mul_le_of_le_one_right hz₀.le hrs
  have htr : |i10Tau z r s - r| ≤ 1 - z := by
    rw [show i10Tau z r s - r = -(1 - z) * (r - s) by unfold i10Tau; ring,
      abs_mul, abs_neg, abs_of_pos hz']
    exact mul_le_of_le_one_right hz'.le hrs
  have hs' := norm_i10PsiF_sub_le_sqrt hε hm ht hs hmt hms hu
  have hr' := norm_i10PsiF_sub_le_sqrt hε hm ht hr hmt hmr hu
  set M := u ^ (-(7 / 10) : ℝ) * (r * s) ^ (-(11 / 20) : ℝ)
  have hM : 0 ≤ M := mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.rpow_nonneg hm.le _)
  have hzn : ‖(z : ℂ)‖ = z := by rw [norm_real, Real.norm_eq_abs, abs_of_pos hz₀]
  have hcn : ‖(1 - z : ℂ)‖ = 1 - z := by
    rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_of_pos hz']
  have e : i10K2B ε q u =
      (1 - z : ℂ) * (i10PsiF ε (i10Tau z r s) u - i10PsiF ε s u) +
        (z : ℂ) * (i10PsiF ε (i10Tau z r s) u - i10PsiF ε r u) := by
    unfold i10K2B
    change i10PsiF ε (i10Tau z r s) u - _ * i10PsiF ε s u - _ * i10PsiF ε r u = _
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, hcn, hzn]
  calc
    _ ≤ (1 - z) * (4 * (M * √z)) + z * (4 * (M * √(1 - z))) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hs'.trans (by gcongr)) hz'.le)
        (mul_le_mul_of_nonneg_left (hr'.trans (by gcongr)) hz₀.le)
    _ = 4 * (M * ((1 - z) * √z + z * √(1 - z))) := by ring
    _ ≤ 4 * (M * (√(z * (1 - z)) + √(z * (1 - z)))) := by
      rw [Real.sqrt_mul hz₀.le]
      have hs₁' : 1 - z ≤ √(1 - z) := Real.le_sqrt_self_iff.mpr (by linarith)
      have hz₁' : z ≤ √z := Real.le_sqrt_self_iff.mpr hz₁.le
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add
        ((mul_le_mul_of_nonneg_right hs₁' (Real.sqrt_nonneg z)).trans_eq (mul_comm _ _))
        (mul_le_mul_of_nonneg_right hz₁' (Real.sqrt_nonneg (1 - z)))) hM) (by norm_num)
    _ = _ := by ring

/-- The subtracted integrand of `K₂`, on a product of the outer and inner domains. -/
noncomputable def i10K2F (ε : ℂ) (p : (ℝ × ℝ × ℝ) × ℝ) : ℂ :=
  i10A ε p.1.2.1 * i10A ε p.1.2.2 * i10W ε p.1.1 * i10K2B ε p.1 p.2

/-- The product of the joining cube and the innermost integration interval. -/
def i10K2Domain : Set ((ℝ × ℝ × ℝ) × ℝ) :=
  (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) ×ˢ Ioo (0 : ℝ) 1

private noncomputable def i10K2Bound (p : (ℝ × ℝ × ℝ) × ℝ) : ℝ :=
  8 * (((p.1.1 * (1 - p.1.1)) ^ (-(11 / 20) : ℝ) *
    ((p.1.2.1 * (1 - p.1.2.1)) ^ (-(11 / 20) : ℝ) *
      (p.1.2.2 * (1 - p.1.2.2)) ^ (-(11 / 20) : ℝ))) * p.2 ^ (-(7 / 10) : ℝ))

private theorem measurableSet_i10K2Domain : MeasurableSet i10K2Domain :=
  (measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)).prod measurableSet_Ioo

private theorem norm_i10K2F_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {p : (ℝ × ℝ × ℝ) × ℝ}
    (hp : p ∈ i10K2Domain) : ‖i10K2F ε p‖ ≤ i10K2Bound p := by
  have hz := hp.1.1
  have hr := hp.1.2.1
  have hs := hp.1.2.2
  have hu := hp.2
  set z := p.1.1
  set r := p.1.2.1
  set s := p.1.2.2
  set u := p.2
  have hc := i9_c_pos hz
  have hr' := sub_pos.mpr hr.2
  have hs' := sub_pos.mpr hs.2
  rw [i10K2F, norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ (1 - r) ^ (-(11 / 20) : ℝ) * (1 - s) ^ (-(11 / 20) : ℝ) *
        (z * (1 - z)) ^ (-(21 / 20) : ℝ) *
        (8 * (u ^ (-(7 / 10) : ℝ) * (r * s) ^ (-(11 / 20) : ℝ) * √(z * (1 - z)))) := by
      have hr₀ := Real.rpow_nonneg hr'.le (-(11 / 20) : ℝ)
      have hs₀ := Real.rpow_nonneg hs'.le (-(11 / 20) : ℝ)
      have hc₀ := Real.rpow_nonneg hc.le (-(21 / 20) : ℝ)
      exact mul_le_mul
        (mul_le_mul (mul_le_mul (norm_i10A_le hε hr) (norm_i10A_le hε hs) (norm_nonneg _) hr₀)
          (norm_i10W_le hε hz) (norm_nonneg _) (mul_nonneg hr₀ hs₀))
        (norm_i10K2B_le hε hp.1 hu) (norm_nonneg _) (mul_nonneg (mul_nonneg hr₀ hs₀) hc₀)
    _ = i10K2Bound p := by
      rw [i10K2Bound, Real.sqrt_eq_rpow]
      rw [Real.mul_rpow hr.1.le hs.1.le,
        Real.mul_rpow hr.1.le hr'.le, Real.mul_rpow hs.1.le hs'.le]
      have e := rpow_mul_rpow_eq (t := z * (1 - z)) (a := -(21 / 20 : ℝ)) (c := -(11 / 20))
        hc (by norm_num : -(21 / 20 : ℝ) + 1 / 2 = -(11 / 20))
      rw [← e]
      ring

private theorem integrable_i10K2Bound : IntegrableOn i10K2Bound i10K2Domain := by
  simp only [IntegrableOn, i10K2Domain, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact ((integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
    ((integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
      (integrableOn_mul_one_sub_rpow_Ioo (by norm_num))) |>.mul_prod
    (integrableOn_rpow_Ioo (by norm_num))).const_mul 8

private theorem measurable_i10K2F (ε : ℂ) : Measurable (i10K2F ε) := by
  unfold i10K2F i10A i10W i10K2B i10PsiF i10Tau
  fun_prop

private theorem differentiable_i10K2F {p : (ℝ × ℝ × ℝ) × ℝ} (hp : p ∈ i10K2Domain) :
    Differentiable ℂ fun ε => i10K2F ε p := by
  have hz := hp.1.1
  have hr := hp.1.2.1
  have hs := hp.1.2.2
  have hu := hp.2
  have ha {x : ℝ} (hx : x < 1) : Differentiable ℂ fun ε => i10A ε x :=
    fun ε => differentiableAt_id.neg.const_cpow
      (Or.inl (ofReal_ne_zero.mpr (sub_pos.mpr hx).ne'))
  have hw : Differentiable ℂ fun ε => i10W ε p.1.1 := fun ε =>
    (differentiableAt_id.sub_const _).const_cpow (Or.inl (ofReal_ne_zero.mpr (i9_c_pos hz).ne'))
  have hb : Differentiable ℂ fun ε => i10K2B ε p.1 p.2 := by
    unfold i10K2B
    exact (((differentiable_i10PsiF (i10Tau_mem_Ioo hz hr hs) hu).sub
      ((differentiable_i10PsiF hs hu).const_mul _)).sub
      ((differentiable_i10PsiF hr hu).const_mul _))
  exact (((ha hr.2).mul (ha hs.2)).mul hw).mul hb

private theorem i10K2_eq_integral {ε : ℂ} (hε : ‖ε‖ < 1 / 20) :
    i10K2 ε = ∫ p in i10K2Domain, i10K2F ε p := by
  have hi : IntegrableOn (i10K2F ε) i10K2Domain :=
    integrable_i10K2Bound.mono' (measurable_i10K2F ε).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_i10K2Domain fun p hp => norm_i10K2F_le hε hp)
  rw [i10K2Domain, Measure.volume_eq_prod] at hi ⊢
  rw [setIntegral_prod _ hi, i10K2]
  apply setIntegral_congr_fun (measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo))
  intro q hq
  dsimp only
  rw [← integral_i10K2B_eq hε hq, ← integral_const_mul]
  rfl

theorem analyticOnNhd_i10K2 : AnalyticOnNhd ℂ i10K2 (Metric.ball 0 (1 / 40)) := by
  have hd : DifferentiableOn ℂ i10K2 (Metric.ball 0 (1 / 40)) := by
    intro ε hε
    apply DifferentiableAt.differentiableWithinAt
    have hε' : ‖ε‖ < 1 / 40 := by simpa only [Metric.mem_ball, dist_zero_right] using hε
    have hball : ∀ w ∈ Metric.ball ε (1 / 40), ‖w‖ < 1 / 20 := fun w hw => by
      have hh := norm_sub_norm_le w ε
      rw [Metric.mem_ball, dist_eq_norm] at hw
      linarith
    have h := differentiableAt_integral_of_holomorphic (by norm_num : (0 : ℝ) < 1 / 40)
      integrable_i10K2Bound (fun w _ => (measurable_i10K2F w).aestronglyMeasurable)
      (ae_restrict_of_forall_mem measurableSet_i10K2Domain fun p hp w hw =>
        norm_i10K2F_le (hball w hw) hp)
      (ae_restrict_of_forall_mem measurableSet_i10K2Domain fun p hp =>
        (differentiable_i10K2F hp).differentiableOn)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds ε (by norm_num : (0 : ℝ) < 1 / 40)] with w hw
    exact i10K2_eq_integral (hball w hw)
  exact fun ε hε => hd.analyticAt (Metric.isOpen_ball.mem_nhds hε)

theorem hasTruncLaurent_i10K2_derivs :
    HasTruncLaurent i10K2
      (fun ε => deriv i10K2 0 * ε + iteratedDeriv 2 i10K2 0 / 2 * ε ^ 2) 3 := by
  have h : AnalyticAt ℂ i10K2 0 := analyticOnNhd_i10K2 _ (Metric.mem_ball_self (by norm_num))
  obtain ⟨F, hF, he⟩ := h.exists_eventuallyEq_sum_add_pow_mul 3
  refine ⟨F, hF, ?_⟩
  filter_upwards [nhdsWithin_le_nhds he] with ε hε
  rw [hε]
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, i10K2_zero, smul_eq_mul]
  ring

private theorem hasDerivAt_i10K2F_iterated {p : (ℝ × ℝ × ℝ) × ℝ} (hp : p ∈ i10K2Domain)
    (n : ℕ) (ε : ℂ) :
    HasDerivAt (iteratedDeriv n (fun w => i10K2F w p))
      (iteratedDeriv (n + 1) (fun w => i10K2F w p) ε) ε := by
  rw [iteratedDeriv_succ]
  exact ((differentiable_i10K2F hp).contDiff.differentiable_iteratedDeriv' n ε).hasDerivAt

private theorem aestronglyMeasurable_i10K2F_iterated (n : ℕ) (ε : ℂ) :
    AEStronglyMeasurable (fun p => iteratedDeriv n (fun w => i10K2F w p) ε)
      (volume.restrict i10K2Domain) := by
  induction n generalizing ε with
  | zero => simpa only [iteratedDeriv_zero] using (measurable_i10K2F ε).aestronglyMeasurable
  | succ n ih =>
    let δ : ℕ → ℂ := fun j => ((1 / ((j : ℝ) + 1) : ℝ) : ℂ)
    let D (w : ℂ) (p : (ℝ × ℝ × ℝ) × ℝ) := iteratedDeriv n (fun t => i10K2F t p) w
    have hδ : Tendsto δ atTop (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun j => ?_⟩
      · simpa only [δ, Function.comp_def, ofReal_zero] using (continuous_ofReal.tendsto 0).comp
          tendsto_one_div_add_atTop_nhds_zero_nat
      · exact ofReal_ne_zero.mpr (by positivity)
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun j p => (δ j)⁻¹ • (D (ε + δ j) p - D ε p)) (fun j => ?_) ?_
    · change AEStronglyMeasurable ((δ j)⁻¹ • (D (ε + δ j) - D ε))
        (volume.restrict i10K2Domain)
      exact ((ih (ε + δ j)).sub (ih ε)).const_smul _
    · filter_upwards [ae_restrict_mem measurableSet_i10K2Domain] with p hp
      have h := hasDerivAt_i10K2F_iterated hp n ε
      rw [hasDerivAt_iff_tendsto_slope_zero] at h
      exact h.comp hδ

/-- The first two nonconstant Taylor coefficients of `K₂) as convergent integrals. -/
theorem hasTruncLaurent_i10K2_integrals :
    HasTruncLaurent i10K2 (fun ε =>
      (∫ p in i10K2Domain, deriv (fun w => i10K2F w p) 0) * ε +
        (∫ p in i10K2Domain, iteratedDeriv 2 (fun w => i10K2F w p) 0) / 2 * ε ^ 2) 3 := by
  let H : ℂ → ℂ := fun ε => ∫ p in i10K2Domain, i10K2F ε p
  have he : i10K2 =ᶠ[𝓝 0] H := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 20)] with ε hε
    exact i10K2_eq_integral (by simpa only [Metric.mem_ball, dist_zero_right] using hε)
  have hd (n : ℕ) (hn : n ≤ 2) :
      iteratedDeriv n i10K2 0 = ∫ p in i10K2Domain, iteratedDeriv n (fun w => i10K2F w p) 0 := by
    rw [he.iteratedDeriv_eq n]
    let D (k : ℕ) (w : ℂ) (p : (ℝ × ℝ × ℝ) × ℝ) := iteratedDeriv k (fun t => i10K2F t p) w
    have hn' : ‖(0 : ℂ)‖ < 1 / 20 - (n : ℝ) * (1 / 100) := by
      have h : (n : ℝ) ≤ 2 := by exact_mod_cast hn
      rw [norm_zero]
      linarith
    have hb : ∀ᵐ p ∂volume.restrict i10K2Domain,
        ∀ w : ℂ, ‖w‖ < 1 / 20 → ‖D 0 w p‖ ≤ i10K2Bound p :=
      ae_restrict_of_forall_mem measurableSet_i10K2Domain fun p hp w hw =>
        norm_i10K2F_le hw hp
    have h := iteratedDeriv_integral_of_chain (D := D) (by norm_num : (0 : ℝ) < 1 / 100)
      (ae_restrict_of_forall_mem measurableSet_i10K2Domain fun p hp =>
        hasDerivAt_i10K2F_iterated hp)
      hb integrable_i10K2Bound aestronglyMeasurable_i10K2F_iterated n 0 hn'
    exact h
  have h₁ := hd 1 (by norm_num)
  simp only [iteratedDeriv_one] at h₁
  rw [← h₁, ← hd 2 (by norm_num)]
  exact hasTruncLaurent_i10K2_derivs

end QED.ThreeLoopE
