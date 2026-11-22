/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegBndLadderRadial
public import QED.ChainProof.SetCRegBndTail
public import QED.TwoLoop.UnitLLinkLimit
import QED.TwoLoop.UnitLLinkDominated
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Integrated inner ladder remainder

Integrate the shell-centered radial estimate of
`QED/ChainProof/SetCRegBndLadderRadial.lean` in the two remaining parameters.
The endpoint is the dressed Pauli integral times the ordinary soft weight.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.TwoLoop.UnitLLink

/-- The pointwise radial integral with its shell endpoint added. -/
noncomputable def ladderInnerCenteredRemainder (mγ Λ T la Y x : ℝ) : ℝ :=
  (∫ z in Ioi (0 : ℝ), ladderInnerRadialRemainder mγ Λ T la Y x z) +
    Y ^ 2 * (1 - x) ^ 3 / (ladderInnerMass 1 la x / x) *
      vpPhotonT 1 mγ Λ T (shellArg 1 Y)

private theorem measurable_ladderInnerCenteredRemainder (mγ Λ T la : ℝ) :
    Measurable (Function.uncurry (ladderInnerCenteredRemainder mγ Λ T la)) := by
  have hR : Measurable (vpPhotonT 1 mγ Λ T) := by
    unfold vpPhotonT QED.TwoLoop.UnitVPLink.photonD
    fun_prop
  have hD := measurable_deriv (vpPhotonT 1 mγ Λ T)
  have hRad : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      ladderInnerRadialRemainder mγ Λ T la p.1.1 p.1.2 p.2) := by
    unfold ladderInnerRadialRemainder ladderInnerMass
    dsimp only
    fun_prop
  have hInt := hRad.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi 0))
  unfold Function.uncurry ladderInnerCenteredRemainder shellArg
    QED.TwoLoop.UnitVPLink.photonVar ladderInnerMass
  exact hInt.measurable.add (by fun_prop)

private theorem integrableOn_of_abs_le_on_unit {F G : ℝ → ℝ} (hG : IntegrableOn G (Ioo 0 1))
    (hF : Measurable F) (h : ∀ x ∈ Ioo (0 : ℝ) 1, |F x| ≤ G x) :
    IntegrableOn F (Ioo 0 1) ∧ |∫ x in Ioo (0 : ℝ) 1, F x| ≤ ∫ x in Ioo (0 : ℝ) 1, G x := by
  have h' : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1), ‖F x‖ ≤ G x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Real.norm_eq_abs] using h x hx
  exact ⟨hG.mono' hF.aestronglyMeasurable h',
    by simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le hG h'⟩

private theorem log_unit_integrals :
    IntegrableOn (fun x : ℝ => -Real.log x) (Ioo 0 1) ∧
    IntegrableOn (fun x : ℝ => -Real.log (1 - x)) (Ioo 0 1) ∧
    (∫ x in Ioo (0 : ℝ) 1, -Real.log x) = 1 ∧
    (∫ x in Ioo (0 : ℝ) 1, -Real.log (1 - x)) = 1 := by
  have h : IntervalIntegrable (fun x : ℝ => -Real.log x) volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'.neg
  have hs := h.symm.comp_sub_left (1 : ℝ)
  rw [sub_self, sub_zero] at hs
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 h,
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 hs, ?_, ?_⟩
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_neg, integral_log]
    simp
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_comp_sub_left (fun x : ℝ => -Real.log x),
      sub_self, sub_zero, intervalIntegral.integral_neg, integral_log]
    simp

private theorem rpow_unit_integrals :
    IntegrableOn (fun y : ℝ => (1 - y) ^ (-(1 / 2) : ℝ)) (Ioo 0 1) ∧
    (∫ y in Ioo (0 : ℝ) 1, (1 - y) ^ (-(1 / 2) : ℝ)) = 2 := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 1) (b := 0)
    (r := -(1 / 2 : ℝ)) (by norm_num)).comp_sub_left 1
  rw [sub_self, sub_zero] at h
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 h, ?_⟩
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-(1 / 2) : ℝ))]
  norm_num [integral_rpow (Or.inl (by norm_num : -1 < -(1 / 2 : ℝ)))]

/-- After centering at the shell endpoint, the fully integrated inner
radial remainder admits a regulator-independent bound. -/
theorem abs_integral_ladderInnerCenteredRemainder_le {mγ Λ T : ℝ} (la : ℝ)
    (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 1 ≤ T) :
    let f := ladderInnerCenteredRemainder mγ Λ T la
    IntegrableOn (fun Y => ∫ x in Ioo (0 : ℝ) 1, f Y x) (Ioo 0 1) ∧
      |∫ Y in Ioo (0 : ℝ) 1, ∫ x in Ioo (0 : ℝ) 1, f Y x| ≤ (59 / 2) / √T := by
  intro f
  have hT₀ := zero_lt_one.trans_le hT
  have hS := Real.sqrt_pos.2 hT₀
  have hST : √T ≤ T := by
    have h := Real.sqrt_le_sqrt hT
    rw [Real.sqrt_one] at h
    calc √T ≤ √T * √T := le_mul_of_one_le_right hS.le h
         _ = T := Real.mul_self_sqrt hT₀.le
  let G := fun Y : ℝ => (17 / 2 + 6 * (1 - Y) ^ (-(1 / 2) : ℝ) +
    3 * (2 + -Real.log (1 - Y))) / √T
  have hF := measurable_ladderInnerCenteredRemainder mγ Λ T la
  have ⟨hlog, hlog', elog, elog'⟩ := log_unit_integrals
  have ⟨hpow, epow⟩ := rpow_unit_integrals
  have hinner (Y : ℝ) (hY : Y ∈ Ioo (0 : ℝ) 1) :
      |∫ x in Ioo (0 : ℝ) 1, f Y x| ≤ G Y := by
    let C := 17 / 2 + 6 * (1 - Y) ^ (-(1 / 2) : ℝ) + 3 * (1 + -Real.log (1 - Y))
    let B := fun x : ℝ => (C + 3 * (-Real.log x)) / √T
    have hC : IntegrableOn (fun _ : ℝ => C) (Ioo 0 1) := integrableOn_const (by simp)
    have hB : IntegrableOn B (Ioo 0 1) := (hC.add (hlog.const_mul 3)).div_const _
    have eB : (∫ x in Ioo (0 : ℝ) 1, B x) = G Y := by
      dsimp only [B, G, C]
      rw [integral_div, integral_add hC (hlog.const_mul 3), integral_const_mul, elog]
      simp
      dsimp only [C]
      ring_nf
    rw [← eB]
    refine (integrableOn_of_abs_le_on_unit hB (hF.comp measurable_prodMk_left) ?_).2
    intro x hx
    have h := (abs_integral_ladderInnerRadialRemainder_add_shell_le la hmγ hreg hT₀ hY hx).2
    have hd : 0 < 1 - Y := sub_pos.mpr hY.2
    have hc : Y * (1 - Y) ≤ 1 :=
      (mul_le_mul_of_nonneg_right hY.2.le hd.le).trans (by linarith only [hY.1])
    have hlogx : 0 ≤ -Real.log x := neg_nonneg.mpr (Real.log_nonpos hx.1.le hx.2.le)
    have hlogd : 0 ≤ -Real.log (1 - Y) :=
      neg_nonneg.mpr (Real.log_nonpos hd.le (by linarith only [hY.1]))
    let L := -Real.log x - Real.log (1 - Y)
    have hL : 0 ≤ L := add_nonneg hlogx hlogd
    have hCL : 1 + Y * (1 - Y) * L ≤ 1 + L := by
      linarith only [mul_le_mul_of_nonneg_right hc hL]
    refine h.trans ?_
    dsimp only [B, C]
    rw [Real.rpow_neg hd.le, ← Real.sqrt_eq_rpow]
    rw [show 6 / (√(1 - Y) * √T) = 6 * (√(1 - Y))⁻¹ / √T by ring]
    have hterm : 3 / T * (1 + Y * (1 - Y) * L) ≤ 3 / √T * (1 + L) :=
      (mul_le_mul_of_nonneg_left hCL (by positivity)).trans
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num) hS hST)
          (by linarith only [hL]))
    dsimp only [L] at hterm
    calc
      _ ≤ 17 / (2 * √T) + 6 * (√(1 - Y))⁻¹ / √T + 3 / √T * (1 + L) :=
        add_le_add le_rfl hterm
      _ = _ := by dsimp only [L]; ring
  have hG₁ : IntegrableOn (fun Y : ℝ => 6 * (1 - Y) ^ (-(1 / 2) : ℝ)) (Ioo 0 1) :=
    hpow.const_mul 6
  have hG₂ : IntegrableOn (fun Y : ℝ => 2 + -Real.log (1 - Y)) (Ioo 0 1) :=
    (integrableOn_const (by simp)).add hlog'
  have hG₃ : IntegrableOn (fun Y : ℝ => 17 / 2 + 6 * (1 - Y) ^ (-(1 / 2) : ℝ)) (Ioo 0 1) :=
    (integrableOn_const (by simp)).add hG₁
  have hG : IntegrableOn G (Ioo 0 1) :=
    (hG₃.add (hG₂.const_mul 3)).div_const _
  have eG : (∫ Y in Ioo (0 : ℝ) 1, G Y) = (59 / 2) / √T := by
    dsimp only [G]
    rw [integral_div, integral_add hG₃ (hG₂.const_mul 3),
      integral_add (integrableOn_const (by simp)) hG₁,
      integral_const_mul, epow, integral_const_mul,
      integral_add (integrableOn_const (by simp)) hlog', elog']
    norm_num
  have hMeas := (hF.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioo 0 1))).measurable
  obtain ⟨hJ, hJ'⟩ := integrableOn_of_abs_le_on_unit hG hMeas hinner
  exact ⟨hJ, hJ'.trans_eq eG⟩

/-- The inner radial shell endpoint factors into the ordinary soft integral
and the dressed one-loop Pauli integral. -/
theorem integral_integral_ladderInnerShell (mγ Λ T la : ℝ) :
    (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
      Y ^ 2 * (1 - x) ^ 3 / (ladderInnerMass 1 la x / x) *
        vpPhotonT 1 mγ Λ T (shellArg 1 Y)) =
      outerSoftJ la * ∫ Y in (0 : ℝ)..1, QED.TwoLoop.VPUnit.regKernel T (mγ ^ 2) (Λ ^ 2) Y := by
  have e (Y x : ℝ) :
      Y ^ 2 * (1 - x) ^ 3 / (ladderInnerMass 1 la x / x) *
          vpPhotonT 1 mγ Λ T (shellArg 1 Y) =
        (Y ^ 2 * vpPhotonT 1 mγ Λ T (shellArg 1 Y)) *
          (x * (1 - x) ^ 3 / ladderInnerMass 1 la x) := by
    rw [div_div_eq_mul_div]
    ring
  simp_rw [e, intervalIntegral.integral_const_mul]
  rw [← outerSoftJ, intervalIntegral.integral_mul_const, mul_comm,
    integral_ladderSoft_coefficient_eq]

/-- The ordinary on-shell charge coefficient cancels the light soft weight.
The heavy logarithm is isolated explicitly for the outer placement. -/
theorem abs_ladderDeltaOne_sub_outerSoftJ_add_log_le {p q : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hq1 : 1 ≤ q) :
    |ladderDeltaOne 1 p q - (outerSoftJ p - outerSoftJ q) + Real.log q / 2| ≤ 7 / 2 := by
  have hq := zero_lt_one.trans_le hq1
  let M := ladderInnerMass 1
  let J := fun m y => y * (1 - y) ^ 3 / M m y
  let f := fun y => -(ladderCtBracket p y - ladderCtBracket q y) - (J p y - J q y) +
    y * Real.log q
  have hJ {m : ℝ} (hm : 0 < m) : IntervalIntegrable (J m) volume 0 1 := by
    exact (ContinuousOn.div (by fun_prop) (continuousOn_ladderInnerMass m)
      (fun y hy => (ladderInnerMass_pos one_pos hm hy).ne')).intervalIntegrable_of_Icc zero_le_one
  have e : ladderDeltaOne 1 p q - (outerSoftJ p - outerSoftJ q) + Real.log q / 2 =
      ∫ y in Ioo (0 : ℝ) 1, f y := by
    rw [ladderDeltaOne_eq hp hq, outerSoftJ, outerSoftJ, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one]
    have hCt : IntervalIntegrable (fun y => -(ladderCtBracket p y - ladderCtBracket q y))
        volume 0 1 :=
      ((intervalIntegrable_ladderCtBracket hp).sub (intervalIntegrable_ladderCtBracket hq)).neg
    have hJ' : IntervalIntegrable (fun y => J p y - J q y) volume 0 1 := (hJ hp).sub (hJ hq)
    have hF : IntervalIntegrable
        (fun y => -(ladderCtBracket p y - ladderCtBracket q y) - (J p y - J q y))
        volume 0 1 := hCt.sub hJ'
    have hLog : IntervalIntegrable (fun y => y * Real.log q) volume 0 1 :=
      (continuous_id.mul continuous_const).intervalIntegrable _ _
    dsimp only [f]
    rw [intervalIntegral.integral_add hF hLog, intervalIntegral.integral_sub hCt hJ',
      intervalIntegral.integral_neg,
      intervalIntegral.integral_sub (intervalIntegrable_ladderCtBracket hp)
        (intervalIntegrable_ladderCtBracket hq),
      intervalIntegral.integral_sub (hJ hp) (hJ hq), intervalIntegral.integral_mul_const,
      integral_id]
    ring
  let G := fun y => 2 + -Real.log y + (-Real.log (1 - y)) / 2
  have ⟨hl, hr, el, er⟩ := log_unit_integrals
  have h2 : IntegrableOn (fun _ : ℝ => (2 : ℝ)) (Ioo 0 1) := integrableOn_const (by simp)
  have hGl : IntegrableOn (fun y : ℝ => 2 + -Real.log y) (Ioo 0 1) := h2.add hl
  have hG : IntegrableOn G (Ioo 0 1) := hGl.add (hr.div_const 2)
  have eG : (∫ y in Ioo (0 : ℝ) 1, G y) = 7 / 2 := by
    dsimp only [G]
    rw [integral_add hGl (hr.div_const 2), integral_add h2 hl, integral_div, el, er]
    norm_num
  have hf : Measurable f := by
    unfold f ladderCtBracket J M ladderInnerMass
    fun_prop
  rw [e, ← eG]
  refine (integrableOn_of_abs_le_on_unit hG hf ?_).2
  intro y hy
  have hy₀ : 0 < y := hy.1
  have hy₁ : y < 1 := hy.2
  have hd : 0 < 1 - y := sub_pos.mpr hy₁
  have hy2 : y ^ 2 ≤ y := by nlinarith only [mul_nonneg hy₀.le hd.le]
  have hmp : 0 < M p y := ladderInnerMass_pos one_pos hp (Ioo_subset_Icc_self hy)
  have hmq : 0 < M q y := ladderInnerMass_pos one_pos hq (Ioo_subset_Icc_self hy)
  have hpq2 : p ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hp.le (hp1.trans hq1) 2
  have hp2 : p ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hp.le hp1 2
  have hq2 : 1 ≤ q ^ 2 := by simpa using pow_le_pow_left₀ zero_le_one hq1 2
  have eM (m : ℝ) : M m y = y ^ 2 + (1 - y) * m ^ 2 := by simp [M, ladderInnerMass]
  have hmpMin : y ^ 2 ≤ M p y := by rw [eM]; exact le_add_of_nonneg_right (by positivity)
  have hmpMax : M p y ≤ 1 := by
    rw [eM]
    linarith only [hy2, mul_le_mul_of_nonneg_left hp2 hd.le]
  have hmqMin : 1 - y ≤ M q y / q ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hq), eM]
    exact le_add_of_nonneg_left (sq_nonneg y)
  have hmqMax : M q y / q ^ 2 ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos hq), eM]
    nlinarith only [hy2, mul_le_mul_of_nonneg_right hq2 hy₀.le]
  have hinv : 0 ≤ (M p y)⁻¹ - (M q y)⁻¹ := by
    apply sub_nonneg.mpr
    apply inv_le_inv₀ hmq hmp |>.2
    rw [eM, eM]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpq2 hd.le)
  have hfrac : y ^ 2 * ((M p y)⁻¹ - (M q y)⁻¹) ≤ 1 := by
    calc
      _ ≤ y ^ 2 * (M p y)⁻¹ := mul_le_mul_of_nonneg_left
        (sub_le_self _ (inv_nonneg.mpr hmq.le)) (sq_nonneg y)
      _ ≤ 1 := by rwa [← div_eq_mul_inv, div_le_one hmp]
  let A := -2 + 7 * y / 2 - y ^ 2
  have hA : |A| ≤ 2 := by
    apply abs_le.mpr
    dsimp only [A]
    constructor
    · linarith only [hy₀, hy2]
    · linarith only [hy₁, sq_nonneg y]
  have hRp : |Real.log (M p y)| ≤ -(2 * Real.log y) := by
    have hlogsq : Real.log (y ^ 2) = 2 * Real.log y := by
      rw [Real.log_pow]
      norm_num
    rw [abs_of_nonpos (Real.log_nonpos hmp.le hmpMax), neg_le_neg_iff, ← hlogsq]
    exact Real.log_le_log (sq_pos_of_pos hy₀) hmpMin
  have hRq : |Real.log (M q y / q ^ 2)| ≤ -Real.log (1 - y) := by
    rw [abs_of_nonpos (Real.log_nonpos (by positivity) hmqMax), neg_le_neg_iff]
    exact Real.log_le_log hd hmqMin
  have eLog : Real.log (M p y / M q y) + 2 * Real.log q =
      Real.log (M p y) - Real.log (M q y / q ^ 2) := by
    rw [Real.log_div hmp.ne' hmq.ne', Real.log_div hmq.ne' (pow_ne_zero _ hq.ne'), Real.log_pow]
    push_cast
    ring
  have ef : f y = -(A * (y ^ 2 * ((M p y)⁻¹ - (M q y)⁻¹))) +
      y / 2 * (Real.log (M p y) - Real.log (M q y / q ^ 2)) := by
    rw [← eLog]
    unfold f J A ladderCtBracket
    have hLog := Real.log_div hmp.ne' hmq.ne'
    dsimp only [M] at hLog
    rw [hLog]
    simp only [M, div_eq_mul_inv]
    ring
  have hLog : |y / 2 * (Real.log (M p y) - Real.log (M q y / q ^ 2))| ≤
      -Real.log y + (-Real.log (1 - y)) / 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ y / 2)]
    calc
      _ ≤ y / 2 * (|Real.log (M p y)| + |Real.log (M q y / q ^ 2)|) :=
        mul_le_mul_of_nonneg_left (by
          rw [sub_eq_add_neg, ← abs_neg (Real.log (M q y / q ^ 2))]
          exact abs_add_le _ _) (by positivity)
      _ ≤ (1 / 2) * (-(2 * Real.log y) + -Real.log (1 - y)) :=
        mul_le_mul (by linarith only [hy₁]) (add_le_add hRp hRq) (by positivity) (by norm_num)
      _ = _ := by ring
  rw [ef]
  dsimp only [G]
  rw [add_assoc]
  refine (abs_add_le _ _).trans (add_le_add ?_ hLog)
  rw [abs_neg, abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg y) hinv)]
  calc
    _ ≤ 2 * 1 := mul_le_mul hA hfrac (mul_nonneg (sq_nonneg y) hinv) zero_le_two
    _ = 2 := mul_one _

/-- The combined inner ladder estimate after the on-shell charge coefficient
is added and the explicit tail and heavy logarithm are centered. -/
theorem abs_ladderInner_centered_onShell_le {p q T : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hq1 : 1 ≤ q) (hT : 1 ≤ T) :
    let R := vpPhotonT 1 p q T
    let E := fun la =>
      ∫ Y in Ioo (0 : ℝ) 1, ∫ x in Ioo (0 : ℝ) 1, ladderInnerCenteredRemainder p q T la Y x
    let F := ∫ x in (0 : ℝ)..1, QED.TwoLoop.VPUnit.regKernel T (p ^ 2) (q ^ 2) x
    |ladderInnerLeading R p - ladderInnerLeading R q -
        (oneLoopF2 1 p - oneLoopF2 1 q) / 4 * photonTail R 0 +
      (E p - E q) +
      (ladderDeltaOne 1 p q - (outerSoftJ p - outerSoftJ q) + Real.log q / 2) * F| ≤
      67 / √T := by
  intro R E F
  have hpq := hp1.trans hq1
  have hT₀ := zero_lt_one.trans_le hT
  have hLead := abs_ladderInnerLeading_pv_sub_tail_le hp hpq hT₀
  have hRem : |E p - E q| ≤ 59 / √T := by
    calc
      _ ≤ |E p| + |E q| := abs_sub _ _
      _ ≤ (59 / 2) / √T + (59 / 2) / √T :=
        add_le_add (abs_integral_ladderInnerCenteredRemainder_le p hp hpq hT).2
          (abs_integral_ladderInnerCenteredRemainder_le q hp hpq hT).2
      _ = _ := by ring
  have ⟨hF₀, hF₁⟩ := QED.TwoLoop.VPUnit.integral_regKernel_le hT₀ (sq_nonneg p)
    (pow_le_pow_left₀ hp.le hpq 2)
  have hSq := Real.sqrt_pos.2 hT₀
  have hST : √T ≤ T := by
    have h := Real.sqrt_le_sqrt hT
    rw [Real.sqrt_one] at h
    calc √T ≤ √T * √T := le_mul_of_one_le_right hSq.le h
         _ = T := Real.mul_self_sqrt hT₀.le
  have hSoft : |(ladderDeltaOne 1 p q - (outerSoftJ p - outerSoftJ q) + Real.log q / 2) * F| ≤
      2 / √T := by
    rw [abs_mul, abs_of_nonneg (show 0 ≤ F from hF₀)]
    refine (mul_le_mul (abs_ladderDeltaOne_sub_outerSoftJ_add_log_le hp hp1 hq1)
      hF₁ (show 0 ≤ F from hF₀) (by norm_num)).trans ?_
    calc
      (7 / 2 : ℝ) * (1 / (3 * T)) = (7 / 6) / T := by ring
      _ ≤ (7 / 6) / √T := div_le_div_of_nonneg_left (by norm_num) hSq hST
      _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) hSq.le
  apply (abs_add_le _ _).trans
  refine (add_le_add ((abs_add_le _ _).trans (add_le_add hLead hRem)) hSoft).trans_eq ?_
  ring

end QED.ChainProof.SetCRegDisp

end
