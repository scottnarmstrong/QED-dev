/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSlope
public import QED.ChainProof.SetCRegLongShare
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Uniform estimates for the dressed photon and centered Feynman shell integrals

The pointwise comparison with a single spectral propagator works over the whole
spectral range, including coincident spectral and regulator masses. Subtracting the
common tail at zero gives shell integrals that decay uniformly in both regulators.
-/

@[expose] public section

open Set MeasureTheory Filter

namespace QED.ChainProof.SetCRegDisp

/-- The positive Pauli–Villars dressed photon is bounded by the single spectral propagator. -/
theorem vpPhotonT_le_single {m mγ Λ T s : ℝ}
    (hm : 0 < m) (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T) (hs : 0 ≤ s) :
    vpPhotonT m mγ Λ T s ≤ 1 / (s + T * m ^ 2) := by
  have hΛ := hmγ.trans_le hreg
  have hab := pow_le_pow_left₀ hmγ.le hreg 2
  have hratio : s / (s + mγ ^ 2) ≤ 1 :=
    (div_le_one (by positivity)).2 (le_add_of_nonneg_right (sq_nonneg _))
  have hdiff : (Λ ^ 2 - mγ ^ 2) / (s + Λ ^ 2) ≤ 1 :=
    (div_le_one (by positivity)).2 (by linarith only [hs, sq_nonneg mγ])
  have h1 : (s / (s + mγ ^ 2)) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hratio
  have h2 : ((Λ ^ 2 - mγ ^ 2) / (s + Λ ^ 2)) ^ 2 ≤ 1 :=
    pow_le_one₀ (div_nonneg (sub_nonneg.mpr hab) (by positivity)) hdiff
  have he : vpPhotonT m mγ Λ T s =
      ((s / (s + mγ ^ 2)) ^ 2 * ((Λ ^ 2 - mγ ^ 2) / (s + Λ ^ 2)) ^ 2) /
        (s + T * m ^ 2) := by
    rw [vpPhotonT_eq hmγ hΛ hT hm hs, div_pow,
      mul_comm (s + T * m ^ 2), ← div_div, mul_div_assoc]
    rw [div_pow]
  rw [he]
  exact div_le_div_of_nonneg_right
    (by simpa only [one_mul] using mul_le_mul h1 h2 (sq_nonneg _) zero_le_one)
    (by positivity)

/-- Subtracting the tail at zero leaves a finite interval with a regulator-independent bound. -/
theorem photonTail_sub_le_log {m mγ Λ T a : ℝ}
    (hm : 0 < m) (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T) (ha : 0 ≤ a) :
    0 ≤ photonTail (vpPhotonT m mγ Λ T) 0 - photonTail (vpPhotonT m mγ Λ T) a ∧
    photonTail (vpPhotonT m mγ Λ T) 0 - photonTail (vpPhotonT m mγ Λ T) a ≤
      Real.log (1 + a / (T * m ^ 2)) := by
  have hΛ := hmγ.trans_le hreg
  have hi : IntegrableOn (vpPhotonT m mγ Λ T) (Ioi 0) := by
    simpa only [zero_add] using integrableOn_vpPhotonT_shift hmγ hΛ hT hm le_rfl
  have hc : 0 < T * m ^ 2 := by positivity
  simp only [photonTail_eq_Ioi]
  rw [intervalIntegral.integral_Ioi_sub_Ioi hi ha]
  refine ⟨intervalIntegral.integral_nonneg ha (fun s hs =>
    vpPhotonT_nonneg hmγ hΛ hT hm hs.1), ?_⟩
  calc
    (∫ s in 0..a, vpPhotonT m mγ Λ T s) ≤ ∫ s in 0..a, 1 / (s + T * m ^ 2) := by
      refine intervalIntegral.integral_mono_on ha ?_ ?_ (fun s hs =>
        vpPhotonT_le_single hm hmγ hreg hT hs.1)
      · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ha).2
          (hi.mono_set Ioc_subset_Ioi_self)
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le ha]
        exact continuousOn_const.div (continuous_id.add continuous_const).continuousOn
          fun s hs => (add_pos_of_nonneg_of_pos hs.1 hc).ne'
    _ = Real.log (1 + a / (T * m ^ 2)) := by
      rw [intervalIntegral.integral_comp_add_right (fun s : ℝ => 1 / s), zero_add,
        integral_one_div_of_pos hc (add_pos_of_nonneg_of_pos ha hc)]
      congr 1
      field_simp
      ring

private theorem log_one_add_le_two_sqrt {y : ℝ} (hy : 0 ≤ y) :
    Real.log (1 + y) ≤ 2 * Real.sqrt y := by
  have hs := Real.sqrt_nonneg y
  have hp : 0 < 1 + Real.sqrt y := by positivity
  have hsq : 1 + y ≤ (1 + Real.sqrt y) ^ 2 := by
    nlinarith only [hs, Real.sq_sqrt hy]
  calc
    Real.log (1 + y) ≤ Real.log ((1 + Real.sqrt y) ^ 2) :=
      Real.log_le_log (by positivity) hsq
    _ = 2 * Real.log (1 + Real.sqrt y) := by rw [Real.log_pow]; norm_cast
    _ ≤ 2 * Real.sqrt y := by linarith only [Real.log_le_sub_one_of_pos hp]

private theorem centeredTail_shell_le {m mγ Λ T x : ℝ}
    (hm : 0 < m) (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T) (hx : x ∈ Icc 0 1) :
    ‖photonTail (vpPhotonT m mγ Λ T) 0 -
      photonTail (vpPhotonT m mγ Λ T) (shellArg m x)‖ ≤
      (2 / Real.sqrt T) * (1 - x) ^ (-(1 / 2) : ℝ) := by
  by_cases hx1 : x = 1
  · subst x
    simp [shellArg, QED.TwoLoop.UnitVPLink.photonVar]
  have hx' : 0 < 1 - x := sub_pos.mpr (lt_of_le_of_ne hx.2 hx1)
  have hden : 0 < T * (1 - x) := mul_pos hT hx'
  have he : shellArg m x / (T * m ^ 2) = x ^ 2 / (T * (1 - x)) := by
    unfold shellArg QED.TwoLoop.UnitVPLink.photonVar
    field_simp
  obtain ⟨h0, hlog⟩ := photonTail_sub_le_log hm hmγ hreg hT (shellArg_nonneg m hx)
  rw [Real.norm_of_nonneg h0]
  refine hlog.trans ?_
  rw [he]
  refine (log_one_add_le_two_sqrt (by positivity)).trans ?_
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hx.1, Real.sqrt_mul hT.le,
    Real.rpow_neg hx'.le, ← Real.sqrt_eq_rpow]
  have hsT := Real.sqrt_pos.2 hT
  have hsx := Real.sqrt_pos.2 hx'
  calc
    2 * (x / (Real.sqrt T * Real.sqrt (1 - x))) ≤
        2 * (1 / (Real.sqrt T * Real.sqrt (1 - x))) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hx.2 (by positivity)) zero_le_two
    _ = _ := by field_simp

private theorem intervalIntegrable_shellMajorant :
    IntervalIntegrable (fun x : ℝ => (1 - x) ^ (-(1 / 2) : ℝ)) volume 0 1 := by
  have hi := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
    (r := -(1 / 2 : ℝ)) (by norm_num)
  simpa only [sub_self, sub_zero] using hi.symm.comp_sub_left (1 : ℝ)

private theorem integral_shellMajorant :
    (∫ x in (0 : ℝ)..1, (1 - x) ^ (-(1 / 2) : ℝ)) = 2 := by
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-(1 / 2) : ℝ))]
  norm_num [integral_rpow (Or.inl (by norm_num : -1 < -(1 / 2 : ℝ)))]

private theorem intervalIntegrable_tail_shell {m mγ Λ T : ℝ}
    (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) :
    IntervalIntegrable (fun x => photonTail (vpPhotonT m mγ Λ T) (shellArg m x)) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Measure.integrableOn_of_bounded (M := photonK mγ Λ / (T * m ^ 2) * Real.pi)
    (by simp) ?_ ?_
  · exact ((measurable_photonTail_vp m mγ Λ).comp
      (measurable_const.prodMk (measurable_shellArg m))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => ?_)
    have ha := shellArg_nonneg m (Ioc_subset_Icc_self hx)
    rw [Real.norm_of_nonneg (photonTail_nonneg hmγ hΛ hT hm ha)]
    exact photonTail_le hmγ hΛ hT hm ha

/-- The centered shell value obeys the dispersion majorant uniformly in both regulators. -/
theorem norm_seShellVal_sub_tail_le {m mγ Λ T : ℝ}
    (hm : 0 < m) (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T) :
    ‖seShellVal (vpPhotonT m mγ Λ T) m -
      (3 / 2) * photonTail (vpPhotonT m mγ Λ T) 0‖ ≤ 8 / Real.sqrt T := by
  let R := vpPhotonT m mγ Λ T
  let q := photonTail R 0
  let f : ℝ → ℝ := fun x => photonTail R (shellArg m x)
  have hf : IntervalIntegrable f volume 0 1 :=
    intervalIntegrable_tail_shell hm hmγ (hmγ.trans_le hreg) hT
  have hw : Continuous fun x : ℝ => 1 + x := continuous_const.add continuous_id
  have hi : IntervalIntegrable (fun x : ℝ => x) volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have hq : (∫ x in (0 : ℝ)..1, (1 + x) * q) = (3 / 2) * q := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_add
      intervalIntegrable_const hi, intervalIntegral.integral_const,
      integral_id]
    norm_num
  change ‖(∫ x in (0 : ℝ)..1, (1 + x) * f x) - (3 / 2) * q‖ ≤ _
  have hfw : IntervalIntegrable (fun x => (1 + x) * f x) volume 0 1 :=
    hf.continuousOn_mul hw.continuousOn
  have hqw : IntervalIntegrable (fun x => (1 + x) * q) volume 0 1 :=
    (hw.mul continuous_const).intervalIntegrable 0 1
  rw [← hq, ← intervalIntegral.integral_sub hfw hqw]
  calc
    _ ≤ ∫ x in (0 : ℝ)..1, (4 / Real.sqrt T) * (1 - x) ^ (-(1 / 2) : ℝ) := by
      refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
        (Eventually.of_forall fun x hx => ?_) (intervalIntegrable_shellMajorant.const_mul _)
      have hx' : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hx
      rw [← mul_sub, norm_mul, norm_sub_rev, Real.norm_of_nonneg (by linarith only [hx'.1])]
      refine (mul_le_mul (show 1 + x ≤ 2 by linarith only [hx'.2])
        (centeredTail_shell_le hm hmγ hreg hT hx') (norm_nonneg _) zero_le_two).trans ?_
      exact le_of_eq (by ring)
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_shellMajorant]; ring

/-- The centered shell slope obeys the dispersion majorant uniformly in both regulators. -/
theorem norm_seShellSlope_add_tail_le {m mγ Λ T : ℝ}
    (hm : 0 < m) (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 1 ≤ T) :
    ‖seShellSlope (vpPhotonT m mγ Λ T) m +
      (1 / 2) * photonTail (vpPhotonT m mγ Λ T) 0‖ ≤ 8 / Real.sqrt T := by
  have ht : 0 < T := zero_lt_one.trans_le hT
  have hΛ := hmγ.trans_le hreg
  let R := vpPhotonT m mγ Λ T
  let q := photonTail R 0
  let f : ℝ → ℝ := fun x => photonTail R (shellArg m x)
  let g : ℝ → ℝ := fun x => 2 * m ^ 2 * x * (1 + x) * R (shellArg m x)
  have pointwise {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ g x ∧ g x ≤ 4 / T := by
    have ha := shellArg_nonneg m hx
    have hr := vpPhotonT_nonneg hmγ hΛ ht hm ha
    have hr' : R (shellArg m x) ≤ 1 / (T * m ^ 2) :=
      (vpPhotonT_le_single hm hmγ hreg ht ha).trans
        (one_div_le_one_div_of_le (by positivity) (le_add_of_nonneg_left ha))
    have hx2 : x * (1 + x) ≤ 1 * 2 :=
      mul_le_mul hx.2 (by linarith only [hx.2]) (by linarith only [hx.1]) zero_le_one
    have hx0 := hx.1
    have hfactor := mul_le_mul_of_nonneg_left hx2 (show 0 ≤ 2 * m ^ 2 by positivity)
    refine ⟨mul_nonneg (by positivity) hr, ?_⟩
    calc
      g x ≤ (4 * m ^ 2) * (1 / (T * m ^ 2)) :=
        mul_le_mul (by nlinarith only [hfactor]) hr' hr (by positivity)
      _ = _ := by field_simp
  have hg : IntervalIntegrable g volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine Measure.integrableOn_of_bounded (M := 4 / T) (by simp) ?_ ?_
    · have hR : Measurable fun x => R (shellArg m x) :=
        (measurable_vpPhotonT m mγ Λ).comp
        (measurable_const.prodMk (measurable_shellArg m))
      have hg₁ : Measurable fun x : ℝ => 2 * m ^ 2 * x * (1 + x) := by fun_prop
      exact (hg₁.mul hR).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => ?_)
      obtain ⟨h0, h1⟩ := pointwise (Ioc_subset_Icc_self hx)
      rwa [Real.norm_of_nonneg h0]
  have hf : IntervalIntegrable f volume 0 1 := intervalIntegrable_tail_shell hm hmγ hΛ ht
  have hw : Continuous fun x : ℝ => 1 - x := continuous_const.sub continuous_id
  have hi : IntervalIntegrable (fun x : ℝ => x) volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have hq : (∫ x in (0 : ℝ)..1, (1 - x) * q) = (1 / 2) * q := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub
      intervalIntegrable_const hi, intervalIntegral.integral_const,
      integral_id]
    norm_num
  change ‖(∫ x in (0 : ℝ)..1, g x - (1 - x) * f x) + (1 / 2) * q‖ ≤ _
  have hfw : IntervalIntegrable (fun x => (1 - x) * f x) volume 0 1 :=
    hf.continuousOn_mul hw.continuousOn
  have hqw : IntervalIntegrable (fun x => (1 - x) * q) volume 0 1 :=
    (hw.mul continuous_const).intervalIntegrable 0 1
  rw [← hq, ← intervalIntegral.integral_add (hg.sub hfw) hqw]
  calc
    _ ≤ ∫ x in (0 : ℝ)..1, 4 / T + (2 / Real.sqrt T) * (1 - x) ^ (-(1 / 2) : ℝ) := by
      refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
        (Eventually.of_forall fun x hx => ?_)
        (intervalIntegrable_const.add (intervalIntegrable_shellMajorant.const_mul _))
      have hx' : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hx
      have he : g x - (1 - x) * f x + (1 - x) * q = g x + (1 - x) * (q - f x) := by ring
      rw [he]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · obtain ⟨h0, h1⟩ := pointwise hx'
        rwa [Real.norm_of_nonneg h0]
      · rw [norm_mul, Real.norm_of_nonneg (sub_nonneg.mpr hx'.2)]
        exact mul_le_of_le_one_left (norm_nonneg _) (by linarith only [hx'.1]) |>.trans
          (centeredTail_shell_le hm hmγ hreg ht hx')
    _ = 4 / T + 4 / Real.sqrt T := by
      rw [intervalIntegral.integral_add intervalIntegrable_const
        (intervalIntegrable_shellMajorant.const_mul _), intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul, integral_shellMajorant]
      simp only [sub_zero, one_smul]
      ring
    _ ≤ _ := by
      have hs := Real.sqrt_pos.2 ht
      have hs1 : 1 ≤ Real.sqrt T := by simpa using Real.sqrt_le_sqrt hT
      have hsT : Real.sqrt T ≤ T := by nlinarith only [Real.sq_sqrt ht.le, hs1]
      calc
        _ ≤ 4 / Real.sqrt T + 4 / Real.sqrt T :=
          add_le_add (div_le_div_of_nonneg_left (by norm_num) hs hsT) le_rfl
        _ = _ := by ring

open QED.WickModel (Params)
open QED.TwoLoop.UnitLLink (oneLoopF2 ladderInnerMass)
open QED.TwoLoop.UnitSCClose (selfVm vmIntegrand abs_vmIntegrand_le)

private theorem norm_oneLoopF2_le_one (m μ : ℝ) : ‖oneLoopF2 m μ‖ ≤ 1 := by
  unfold oneLoopF2
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := 1) (f := fun x => x ^ 2 * (1 - x) * m ^ 2 / ladderInnerMass m μ x) ?_
  · simpa using h
  intro x hx
  rw [uIoc_of_le zero_le_one] at hx
  have hx1 := sub_nonneg.mpr hx.2
  have hden : 0 ≤ ladderInnerMass m μ x := by unfold ladderInnerMass; positivity
  rw [Real.norm_of_nonneg (div_nonneg (by positivity) hden)]
  by_cases h0 : ladderInnerMass m μ x = 0
  · simp [h0]
  apply (div_le_one (lt_of_le_of_ne hden (Ne.symm h0))).2
  calc
    _ ≤ x ^ 2 * 1 * m ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith only [hx.1]) (sq_nonneg _)) (sq_nonneg _)
    _ ≤ _ := by simpa only [mul_one, ladderInnerMass] using
      le_add_of_nonneg_right (mul_nonneg hx1 (sq_nonneg μ))

private theorem norm_selfVm_le_three (μ : ℝ) : ‖selfVm μ‖ ≤ 3 := by
  unfold selfVm
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := 3) (f := vmIntegrand μ) ?_
  · simpa using h
  intro x hx
  rw [uIoc_of_le zero_le_one] at hx
  rw [Real.norm_eq_abs]
  exact (abs_vmIntegrand_le hx).trans (by linarith only [hx.1])

/-- The full Feynman share sum after adding its explicit photon-tail term. -/
theorem norm_sum_uSF_add_tail_le (P₀ : Params) {mγ Λ T : ℝ}
    (hm : 0 < P₀.m) (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 1 ≤ T) :
    ‖(∑ k, uSF P₀ k mγ Λ T) +
      sCoefLine P₀ * (P₀.e ^ 4 / (32 * Real.pi ^ 4) : ℝ) *
        (((oneLoopF2 P₀.m mγ - oneLoopF2 P₀.m Λ) / 2 + 3 * dVm P₀.m mγ Λ) *
          photonTail (vpPhotonT P₀.m mγ Λ T) 0 : ℝ)‖ ≤
      ‖sCoefLine P₀ * (P₀.e ^ 4 / (32 * Real.pi ^ 4) : ℝ)‖ * (112 / Real.sqrt T) := by
  have hΛ := hmγ.trans_le hreg
  let F := oneLoopF2 P₀.m mγ - oneLoopF2 P₀.m Λ
  let V := dVm P₀.m mγ Λ
  let R := vpPhotonT P₀.m mγ Λ T
  let q := photonTail R 0
  let val := seShellVal R P₀.m
  let slope := seShellSlope R P₀.m
  let scale := sCoefLine P₀ * (P₀.e ^ 4 / (32 * Real.pi ^ 4) : ℝ)
  have hF : ‖F‖ ≤ 2 := by
    exact (norm_sub_le _ _).trans (by
      simpa only [one_add_one_eq_two] using
        add_le_add (norm_oneLoopF2_le_one P₀.m mγ) (norm_oneLoopF2_le_one P₀.m Λ))
  have hV : ‖V‖ ≤ 6 := by
    exact (norm_sub_le _ _).trans (by
      exact (add_le_add (norm_selfVm_le_three _) (norm_selfVm_le_three _)).trans (by norm_num))
  have hsum : (∑ k, uSF P₀ k mγ Λ T) = scale * (↑(F * slope - 2 * V * val) : ℂ) := by
    have hk : dVk P₀.m mγ Λ = -F - V := by
      exact eq_sub_of_add_eq (dVk_add_dVm hm hmγ hΛ)
    have hmC : (P₀.m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm.ne'
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    rw [sum_uShare]
    simp only [massKer, shellKer₀, shellKer₁, sCoefVtx, sPauliB0_eq_two_mul hm hmγ hΛ, hk]
    dsimp only [scale, sCoefLine, F, V, slope, val, R]
    push_cast
    field_simp
    ring
  change ‖(∑ k, uSF P₀ k mγ Λ T) + scale * (↑((F / 2 + 3 * V) * q) : ℂ)‖ ≤ _
  rw [hsum, ← mul_add, ← Complex.ofReal_add, norm_mul, Complex.norm_real]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [show F * slope - 2 * V * val + (F / 2 + 3 * V) * q =
    F * (slope + q / 2) - 2 * V * (val - 3 / 2 * q) by ring]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, show ‖(2 : ℝ)‖ = 2 by norm_num]
  have hs : ‖slope + q / 2‖ ≤ 8 / Real.sqrt T := by
    rw [div_eq_inv_mul]
    simpa only [one_div] using norm_seShellSlope_add_tail_le hm hmγ hreg hT
  have hv := norm_seShellVal_sub_tail_le hm hmγ hreg (zero_lt_one.trans_le hT)
  calc
    _ ≤ 2 * (8 / Real.sqrt T) + (2 * 6) * (8 / Real.sqrt T) :=
      add_le_add (mul_le_mul hF hs (norm_nonneg _) zero_le_two)
        (mul_le_mul (mul_le_mul_of_nonneg_left hV zero_le_two) hv (norm_nonneg _) (by norm_num))
    _ = _ := by ring

end QED.ChainProof.SetCRegDisp

end
