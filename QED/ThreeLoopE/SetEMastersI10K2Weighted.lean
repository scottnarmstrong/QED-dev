/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI10K2Inner
public import QED.ThreeLoopE.SetEMastersI10K2Join
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.LHopital
public import QED.ThreeLoopE.SetEMastersI10KaMoments
public import QED.Polylog.HPLLowWeight
import QED.Polylog.HPLValues
import QED.Polylog.HPLValues4
import QED.Polylog.Deriv
import QED.Polylog.ExtraIntegralsC

/-!
# The quadratic coefficient after integrating the joining parameter

At fixed bubbles the affine argument stays in the open unit interval.
The interpolation formulas transfer a derivative to each coefficient of
the inner moment. The bubble logarithms are constant during this transfer.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog
open QED.Polylog.HPL Letter

namespace QED.ThreeLoopE

/-- The derivative of the quadratic inner moment. -/
noncomputable def i10K2PsiTwoDeriv (t : ℝ) : ℝ :=
  let c := 1 - t
  let a := log t
  let b := log c
  (-a) / (2 * t) + 3 * (c - a) / (2 * t ^ 2) - 6 / t ^ 2 -
    3 * c * (-Li₂ t + a * b - 2 * b ^ 2 + 3 * b) / t ^ 3 +
    3 * c ^ 2 / (2 * t ^ 2) * (2 * b / t + (-a + 4 * b - 3) / c)

/-- Differentiation of the quadratic inner moment on the integration interval. -/
theorem hasDerivAt_i10K2PsiTwo {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i10K2PsiTwo (i10K2PsiTwoDeriv t) t := by
  have ht₀ := ht.1.ne'
  have hc := (sub_pos.mpr ht.2).ne'
  have dt := hasDerivAt_id' t
  have dc := dt.const_sub (1 : ℝ)
  have da := hasDerivAt_log ht₀
  have db := dc.log hc
  have dL := hasDerivAt_Li₂' ht
  have dQ := ((dL.neg.add (da.mul db)).sub ((db.pow 2).const_mul 2)).add (db.const_mul 3)
  have dF := (((da.pow 2).neg.div_const 4).add
    (((dc.mul da).const_mul 3).div (dt.const_mul 2) (mul_ne_zero two_ne_zero ht₀))).sub_const 5
  have dG := dF.add ((hasDerivAt_const t (6 : ℝ)).div dt ht₀)
  have dM := ((dc.pow 2).const_mul 3).div ((dt.pow 2).const_mul 2)
    (mul_ne_zero two_ne_zero (pow_ne_zero 2 ht₀))
  have h := dG.add (dM.mul dQ)
  convert h using 1
  · ext x
    simp only [i10K2PsiTwo, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply,
      Pi.neg_apply, Pi.pow_apply]
    ring
  · simp only [i10K2PsiTwoDeriv, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply,
      Pi.neg_apply, Pi.pow_apply]
    field_simp [ht₀, hc]
    ring

/-- The derivative of the quadratic moment is continuous away from the endpoints. -/
theorem continuousOn_i10K2PsiTwoDeriv : ContinuousOn i10K2PsiTwoDeriv (Ioo 0 1) := by
  unfold i10K2PsiTwoDeriv
  intro t ht
  have ht₀ := ht.1.ne'
  have ht₂ := pow_ne_zero 2 ht₀
  have hden₁ := mul_ne_zero two_ne_zero ht₀
  have hden₂ := mul_ne_zero two_ne_zero ht₂
  have ht₃ := pow_ne_zero 3 ht₀
  have hc := (sub_pos.mpr ht.2).ne'
  have hL := (hasDerivAt_Li₂' ht).continuousAt
  apply ContinuousAt.continuousWithinAt
  dsimp only
  fun_prop

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

private theorem tau_interior {r s z : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    i10Tau z r s ∈ Ioo (0 : ℝ) 1 := by
  have h : 0 ≤ 1 - z := sub_nonneg.mpr hz.2
  have h₀ := add_nonneg (mul_nonneg hz.1 (sub_nonneg.mpr (min_le_left r s)))
    (mul_nonneg h (sub_nonneg.mpr (min_le_right r s)))
  have h₁ := add_nonneg (mul_nonneg hz.1 (sub_nonneg.mpr (le_max_left r s)))
    (mul_nonneg h (sub_nonneg.mpr (le_max_right r s)))
  unfold i10Tau
  exact ⟨by nlinarith only [h₀, lt_min hr.1 hs.1],
    by nlinarith only [h₁, max_lt hr.2 hs.2]⟩

private theorem hasDerivAt_tau (z r s : ℝ) :
    HasDerivAt (fun x => i10Tau x r s) (r - s) z := by
  have h := ((hasDerivAt_id' z).mul_const r).add
    (((hasDerivAt_id' z).const_sub 1).mul_const s)
  exact h.congr_deriv (by ring)

private theorem interpolation_integrable {g g' W : ℝ → ℝ}
    (hg : ∀ z ∈ Icc (0 : ℝ) 1, HasDerivAt g (g' z) z)
    (hW : IntervalIntegrable W volume 0 1) :
    IntervalIntegrable
      (fun z => W z * ((g z - (1 - z) * g 0 - z * g 1) / (z * (1 - z)))) volume 0 1 := by
  let N := fun z : ℝ => g z - (1 - z) * g 0 - z * g 1
  have hN z (hz : z ∈ Icc (0 : ℝ) 1) : DifferentiableAt ℝ N z :=
    (((hg z hz).sub (((hasDerivAt_id' z).const_sub 1).mul_const (g 0))).sub
      ((hasDerivAt_id' z).mul_const (g 1))).differentiableAt
  have hC (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
      ContinuousOn (dslope N a) (Icc 0 1) := by
    intro z hz
    by_cases e : z = a
    · subst z
      exact (continuousAt_dslope_same.2 (hN a ha)).continuousWithinAt
    · exact (continuousWithinAt_dslope_of_ne e).2 (hN z hz).continuousAt.continuousWithinAt
  have hD : ContinuousOn (fun z => dslope N 0 z - dslope N 1 z) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact (hC 0 (by simp)).sub (hC 1 (by simp))
  apply (hW.mul_continuousOn hD).congr_uIoo
  intro z hz
  rw [uIoo_of_le zero_le_one] at hz
  have h₁ : z - 1 ≠ 0 := sub_ne_zero.mpr hz.2.ne
  simp only [dslope_of_ne N hz.1.ne', dslope_of_ne N hz.2.ne, slope, vsub_eq_sub,
    smul_eq_mul, show N 0 = 0 by simp [N], show N 1 = 0 by simp [N], sub_zero]
  change W z * (z⁻¹ * N z - (z - 1)⁻¹ * N z) = W z * (N z / (z * (1 - z)))
  field_simp [hz.1.ne', h₁, (sub_pos.mpr hz.2).ne']
  ring

private theorem intervalIntegrable_log_joining :
    IntervalIntegrable (fun z : ℝ => log (z * (1 - z))) volume 0 1 := by
  have h : IntervalIntegrable log volume (0 : ℝ) 1 := intervalIntegral.intervalIntegrable_log'
  have hr := h.symm.comp_sub_left 1
  simp only [sub_self, sub_zero] at hr
  apply (h.add hr).congr_uIoo
  intro z hz
  rw [uIoo_of_le zero_le_one] at hz
  exact (log_mul hz.1.ne' (sub_pos.mpr hz.2).ne').symm

private theorem integral_quadratic_joining_parameter {r s : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    (∫ z in Ioo (0 : ℝ) 1, i10K2OuterTwo (z, r, s)) =
      (∫ z in (0 : ℝ)..1, ((r - s) * i10K2PsiTwoDeriv (i10Tau z r s)) *
        (log (1 - z) - log z)) +
      (log (1 - r) + log (1 - s)) *
        (-(∫ z in (0 : ℝ)..1, i10K2OuterOne (z, r, s))) +
      ∫ z in (0 : ℝ)..1,
        ((r - s) * deriv i10K2PsiOne (i10Tau z r s)) * i10K2JoinLog z := by
  let g := fun z => i10K2PsiOne (i10Tau z r s)
  let g' := fun z => (r - s) * deriv i10K2PsiOne (i10Tau z r s)
  let f := fun z => i10K2PsiTwo (i10Tau z r s)
  let f' := fun z => (r - s) * i10K2PsiTwoDeriv (i10Tau z r s)
  let C := log (1 - r) + log (1 - s)
  have hτ (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) := tau_interior hr hs hz
  have hτc : ContinuousOn (fun z => i10Tau z r s) (Icc 0 1) :=
    fun z _ => (hasDerivAt_tau z r s).continuousAt.continuousWithinAt
  have hg z (hz : z ∈ Icc (0 : ℝ) 1) : HasDerivAt g (g' z) z := by
    have h := hasDerivAt_i10K2PsiOne (hτ z hz)
    exact (h.differentiableAt.hasDerivAt.comp z (hasDerivAt_tau z r s)).congr_deriv
      (mul_comm _ _)
  have hf z (hz : z ∈ Icc (0 : ℝ) 1) : HasDerivAt f (f' z) z := by
    have h := (hasDerivAt_i10K2PsiTwo (hτ z hz)).comp z (hasDerivAt_tau z r s)
    exact h.congr_deriv (mul_comm _ _)
  have hgc : ContinuousOn g' (Icc 0 1) :=
    (continuousOn_i10K2PsiOne_deriv.comp hτc hτ).const_mul _
  have hfc : ContinuousOn f' (Icc 0 1) :=
    (continuousOn_i10K2PsiTwoDeriv.comp hτc hτ).const_mul _
  have e₀ (k : ℝ → ℝ) : k (i10Tau 0 r s) = k s := by simp [i10Tau]
  have e₁ (k : ℝ → ℝ) : k (i10Tau 1 r s) = k r := by simp [i10Tau]
  let P := fun k z => i10K2Interpolation k z r s / (z * (1 - z))
  have hgI : IntervalIntegrable (P i10K2PsiOne) volume 0 1 := by
    simpa only [g, P, i10K2Interpolation, one_mul, e₀, e₁] using
      interpolation_integrable hg (W := fun _ => 1) intervalIntegrable_const
  have hfI : IntervalIntegrable (P i10K2PsiTwo) volume 0 1 := by
    simpa only [f, P, i10K2Interpolation, one_mul, e₀, e₁] using
      interpolation_integrable hf (W := fun _ => 1) intervalIntegrable_const
  have hWI : IntervalIntegrable (fun z => log (z * (1 - z)) * P i10K2PsiOne z)
      volume 0 1 := by
    simpa only [g, P, i10K2Interpolation, e₀, e₁] using
      interpolation_integrable hg intervalIntegrable_log_joining
  have hF : (∫ z in (0 : ℝ)..1, P i10K2PsiTwo z) =
      ∫ z in (0 : ℝ)..1, f' z * (log (1 - z) - log z) := by
    simpa only [f, P, i10K2Interpolation, e₀, e₁] using integral_i10K2_interpolation hf hfc
  have hW : (∫ z in (0 : ℝ)..1, log (z * (1 - z)) * P i10K2PsiOne z) =
      ∫ z in (0 : ℝ)..1, g' z * i10K2JoinLog z := by
    simpa only [g, P, i10K2Interpolation, e₀, e₁] using
      integral_i10K2_logWeighted_interpolation hg hgc
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  calc
    _ = ∫ z in (0 : ℝ)..1, (P i10K2PsiTwo z - C * P i10K2PsiOne z) +
        log (z * (1 - z)) * P i10K2PsiOne z := by
      apply intervalIntegral.integral_congr
      intro z _
      simp only [i10K2OuterTwo, i10K2LogWeight, P, C]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hfI.sub (hgI.const_mul C)) hWI,
        intervalIntegral.integral_sub hfI (hgI.const_mul C),
        intervalIntegral.integral_const_mul, hF, hW]
      change _ - C * (∫ z in (0 : ℝ)..1, P i10K2PsiOne z) + _ =
        _ + C * (-(∫ z in (0 : ℝ)..1, P i10K2PsiOne z)) + _
      ring

private theorem integral_tau_comp {F : ℝ → ℝ} {r s : ℝ} :
    (∫ z in (0 : ℝ)..1, (r - s) * F (i10Tau z r s)) = ∫ t in s..r, F t := by
  simp_rw [show ∀ z, i10Tau z r s = (r - s) * z + s by intro z; unfold i10Tau; ring]
  rw [intervalIntegral.integral_const_mul]
  simpa only [smul_eq_mul, mul_zero, zero_add, mul_one, sub_add_cancel] using
    intervalIntegral.smul_integral_comp_mul_add F (a := (0 : ℝ)) (b := 1) (r - s) s

/-- The quadratic coefficient at fixed bubbles, with the affine cut as integration variable. -/
theorem integral_i10K2OuterTwo_interval {r s : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    (∫ z in Ioo (0 : ℝ) 1, i10K2OuterTwo (z, r, s)) =
      (∫ t in s..r, i10K2PsiTwoDeriv t * (log (r - t) - log (t - s))) -
      (log (1 - r) + log (1 - s)) *
        (∫ t in s..r, deriv i10K2PsiOne t * (log (r - t) - log (t - s))) +
      ∫ t in s..r, deriv i10K2PsiOne t * i10K2JoinLog ((t - s) / (r - s)) := by
  have h := integral_i10K2OuterOne_interval hr hs
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one] at h
  rw [integral_quadratic_joining_parameter hr hs, h, mul_neg, ← sub_eq_add_neg]
  rcases eq_or_ne r s with rfl | hne
  · simp
  · have h₁ :
        (∫ z in (0 : ℝ)..1, ((r - s) * i10K2PsiTwoDeriv (i10Tau z r s)) *
          (log (1 - z) - log z)) =
        ∫ t in s..r, i10K2PsiTwoDeriv t * (log (r - t) - log (t - s)) := by
      rw [← integral_tau_comp (r := r) (s := s)]
      apply intervalIntegral.integral_congr_uIoo
      intro z hz
      rw [uIoo_of_le zero_le_one] at hz
      have e₁ : r - i10Tau z r s = (r - s) * (1 - z) := by unfold i10Tau; ring
      have e₂ : i10Tau z r s - s = (r - s) * z := by unfold i10Tau; ring
      dsimp only
      rw [e₁, e₂, log_mul (sub_ne_zero.mpr hne) (sub_pos.mpr hz.2).ne',
        log_mul (sub_ne_zero.mpr hne) hz.1.ne']
      ring
    have h₂ :
        (∫ z in (0 : ℝ)..1, ((r - s) * deriv i10K2PsiOne (i10Tau z r s)) *
          i10K2JoinLog z) =
        ∫ t in s..r, deriv i10K2PsiOne t * i10K2JoinLog ((t - s) / (r - s)) := by
      rw [← integral_tau_comp (r := r) (s := s)]
      apply intervalIntegral.integral_congr
      intro z _
      have e : (i10Tau z r s - s) / (r - s) = z := by
        unfold i10Tau
        field_simp [sub_ne_zero.mpr hne]
        ring
      dsimp only
      rw [e, mul_assoc]
    rw [h₁, h₂]

/-- The quadratic coefficient as a bubble-pair integral of the transferred derivatives. -/
theorem integral_i10K2CoeffTwo_joined :
    let T := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1
    let F := fun p : ℝ × ℝ =>
      (∫ t in p.2..p.1, i10K2PsiTwoDeriv t * (log (p.1 - t) - log (t - p.2))) -
      (log (1 - p.1) + log (1 - p.2)) *
        (∫ t in p.2..p.1, deriv i10K2PsiOne t * (log (p.1 - t) - log (t - p.2))) +
      ∫ t in p.2..p.1, deriv i10K2PsiOne t * i10K2JoinLog ((t - p.2) / (p.1 - p.2))
    IntegrableOn F T ∧
      (∫ p in i10K2Domain, i10K2CoeffTwo p) = ∫ p in T, F p := by
  dsimp only
  let S := Ioo (0 : ℝ) 1
  let T := S ×ˢ S
  have hT : MeasurableSet T := measurableSet_Ioo.prod measurableSet_Ioo
  obtain ⟨hi, hv⟩ := integral_i10K2_coefficients_outer.2
  have hi' : Integrable i10K2OuterTwo ((volume.restrict S).prod (volume.restrict T)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hi
  refine ⟨hi'.integral_prod_right.congr (ae_restrict_of_forall_mem hT
    fun _ hp => integral_i10K2OuterTwo_interval hp.1 hp.2), ?_⟩
  rw [hv]
  change (∫ q in S ×ˢ T, i10K2OuterTwo q) = _
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ hi']
  exact setIntegral_congr_fun hT fun _ hp => integral_i10K2OuterTwo_interval hp.1 hp.2

/-- The unweighted density after integrating both bubbles at a fixed cut. -/
noncomputable def i10K2DensityOne (t : ℝ) : ℝ :=
  2 * t * (1 - t) * (log (1 - t) - log t)

/-- The candidate density of the logarithmic joining and bubble weights. -/
noncomputable def i10K2DensityTwo (t : ℝ) : ℝ :=
  let c := 1 - t
  let a := log t
  let b := log c
  2 * c * (3 * t - 1) * (Li₂ t + a * b) - t * c * a ^ 2 - 2 * t * (2 - t) * a +
    c * (1 - 2 * t) * b ^ 2 + 2 * c * (1 + t) * b

/-- The one-dimensional expression obtained by combining the two cut densities. -/
noncomputable def i10K2QuadraticReduced (t : ℝ) : ℝ :=
  i10K2DensityOne t * i10K2PsiTwoDeriv t + i10K2DensityTwo t * deriv i10K2PsiOne t

private noncomputable def hplSumDeriv (x : ℝ) : List (ℝ × List Letter) → ℝ
  | [] => 0
  | (_, []) :: terms => hplSumDeriv x terms
  | (a, b :: w) :: terms => a * b.kernel x * hpl w x + hplSumDeriv x terms

private theorem hasDerivAt_hplSum {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (terms : List (ℝ × List Letter)) :
    HasDerivAt (kaHplSum · terms) (hplSumDeriv x terms) x := by
  induction terms with
  | nil => exact hasDerivAt_const x 0
  | cons head tail ih =>
    obtain ⟨a, w⟩ := head
    cases w with
    | nil =>
      have e : hpl [] = fun _ => (1 : ℝ) := by funext y; rw [hpl]
      unfold kaHplSum hplSumDeriv
      simp only [e, mul_one]
      exact ih.const_add a
    | cons b v =>
      unfold kaHplSum hplSumDeriv
      exact (((hasDerivAt_hpl_cons b v hx).const_mul a).add ih).congr_deriv (by ring)

/-- Coefficients grouped by the power of the cut in the quadratic primitive. -/
noncomputable def i10K2QuadraticPrimitiveTerms (n : ℤ) : List (ℝ × List Letter) :=
  match n with
  | -2 => [(-3, [one, zero, one]), (6, [one, one]), (-6, [one, one, zero]),
      (-9, [one, one, one])]
  | -1 => [(30, [zero, zero, one]), (51, [zero, one]), (24, [zero, one, zero]),
      (48, [zero, one, one]), (51, [one]), (48, [one, zero]), (18, [one, zero, zero]),
      (72, [one, zero, one]), (57, [one, one]), (96, [one, one, zero]),
      (144, [one, one, one])]
  | 0 => [(-51, [zero]), (-18, [zero, zero]), (60, [zero, zero, zero, one]),
      (-15, [zero, zero, one]), (48, [zero, zero, one, zero]), (96, [zero, zero, one, one]),
      (-47, [zero, one]), (-10, [zero, one, zero]), (36, [zero, one, zero, zero]),
      (126, [zero, one, zero, one]), (-43, [zero, one, one]), (156, [zero, one, one, zero]),
      (234, [zero, one, one, one]), (35, [one]), (57, [one, zero]), (-9, [one, zero, one]),
      (67, [one, one]), (-18, [one, one, zero]), (-27, [one, one, one])]
  | 1 => [(11, []), (-97, [zero]), (-42, [zero, zero]), (-30, [zero, zero, one]),
      (-68, [zero, one]), (-24, [zero, one, zero]), (-48, [zero, one, one]), (-92, [one]),
      (-112, [one, zero]), (-18, [one, zero, zero]), (-60, [one, zero, one]),
      (-138, [one, one]), (-72, [one, one, zero]), (-108, [one, one, one])]
  | 2 => [(6, [zero]), (3, [zero, zero]), (4, [zero, one]), (6, [one]), (7, [one, zero]),
      (8, [one, one])]
  | _ => []

/-- A primitive for the reduced quadratic integrand, grouped by powers of the cut. -/
noncomputable def i10K2QuadraticPrimitive (t : ℝ) : ℝ :=
  kaHplSum t (i10K2QuadraticPrimitiveTerms (-2)) / t ^ 2 +
  kaHplSum t (i10K2QuadraticPrimitiveTerms (-1)) / t +
  kaHplSum t (i10K2QuadraticPrimitiveTerms 0) +
  t * kaHplSum t (i10K2QuadraticPrimitiveTerms 1) +
  t ^ 2 * kaHplSum t (i10K2QuadraticPrimitiveTerms 2)

/-- The finite HPL primitive differentiates to the reduced expression. -/
theorem hasDerivAt_i10K2QuadraticPrimitive {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i10K2QuadraticPrimitive (i10K2QuadraticReduced x) x := by
  have h₀ := hx.1.ne'
  have hc := (sub_pos.mpr hx.2).ne'
  have dx := hasDerivAt_id' x
  have d₁ := (hasDerivAt_hplSum hx (i10K2QuadraticPrimitiveTerms (-2))).div
    (dx.pow 2) (pow_ne_zero 2 h₀)
  have d₂ := (hasDerivAt_hplSum hx (i10K2QuadraticPrimitiveTerms (-1))).div dx h₀
  have d₃ := hasDerivAt_hplSum hx (i10K2QuadraticPrimitiveTerms 0)
  have d₄ := dx.mul (hasDerivAt_hplSum hx (i10K2QuadraticPrimitiveTerms 1))
  have d₅ := (dx.pow 2).mul (hasDerivAt_hplSum hx (i10K2QuadraticPrimitiveTerms 2))
  refine ((((d₁.add d₂).add d₃).add d₄).add d₅).congr_deriv ?_
  simp only [i10K2QuadraticPrimitiveTerms, kaHplSum, hplSumDeriv, hpl_nil, Letter.kernel,
    Pi.pow_apply]
  unfold i10K2QuadraticReduced i10K2DensityOne i10K2DensityTwo i10K2PsiTwoDeriv
  rw [(hasDerivAt_i10K2PsiOne hx).deriv, hpl_one_zero_zero hx, hpl_zero_one_zero hx,
    hpl_one_one_zero hx, hpl_one_zero_one hx, hpl_one_one_one hx,
    hpl_zero_zero_one hx, hpl_one_zero hx,
    hpl_one_one hx, hpl_zero_zero x, hpl_zero_one hx, hpl_one hx, hpl_zero x]
  rw [show Li 2 x = Li₂ x from rfl]
  field_simp [h₀, hc]
  ring

private theorem tendsto_one_sub_mul_hpl (w : List Letter) :
    Tendsto (fun x => (1 - x) * hpl w x) (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨C, _, h⟩ := abs_hpl_le_one_sub_rpow w (ε := 1 / 2) (by norm_num)
  have hL : Tendsto (fun y => y * hpl w (1 - y)) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_zero_of_abs_le_rpow (C := C) (r := 1 / 2) (b := 1 / 2)
      (by norm_num) (by norm_num) fun y hy => ?_
    have h' := h (1 - y) ⟨by linarith only [hy.2], sub_lt_self 1 hy.1⟩
    rw [sub_sub_cancel] at h'
    rw [abs_mul, abs_of_pos hy.1]
    calc
      _ ≤ y * (C * y ^ (-(1 / 2) : ℝ)) := mul_le_mul_of_nonneg_left h' hy.1.le
      _ = C * (y ^ (1 : ℝ) * y ^ (-(1 / 2) : ℝ)) := by rw [rpow_one, mul_left_comm]
      _ = C * y ^ (1 / 2 : ℝ) := by rw [← rpow_add hy.1]; norm_num
  simpa only [Function.comp_def, sub_sub_cancel] using hL.comp tendsto_one_sub_nhdsLT_one

private theorem tendsto_scaled_hpl_one {f : ℝ → ℝ} (hf : ContinuousAt f 1) (w : List Letter) :
    Tendsto (fun x => f x * ((1 - x) * hpl w x)) (𝓝[<] 1) (𝓝 0) := by
  simpa only [mul_zero] using
    (hf.tendsto.mono_left nhdsWithin_le_nhds).mul (tendsto_one_sub_mul_hpl w)

private theorem tendsto_regular_hpl_one {f : ℝ → ℝ} (hf : ContinuousAt f 1) (w : List Letter) :
    Tendsto (fun x => f x * hpl (zero :: w) x) (𝓝[<] 1)
      (𝓝 (f 1 * hpl (zero :: w) 1)) :=
  (hf.tendsto.mono_left nhdsWithin_le_nhds).mul (tendsto_hpl_one (by decide) w)

/-- The right endpoint value of the quadratic primitive. -/
theorem tendsto_i10K2QuadraticPrimitive_one :
    Tendsto i10K2QuadraticPrimitive (𝓝[<] 1)
      (𝓝 (11 - 60 * (π ^ 2 / 6) - 38 * zeta3 + 363 * (π ^ 4 / 90) / 2)) := by
  have ht : Tendsto (fun x : ℝ => 11 * x) (𝓝[<] 1) (𝓝 (11 * 1)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).const_mul 11
  have h₀ := tendsto_regular_hpl_one (f := fun x => 6*x^2 - 97*x - 51)
    (by fun_prop) []
  have h₀₀ := tendsto_regular_hpl_one (f := fun x => 3*x^2 - 42*x - 18)
    (by fun_prop) [zero]
  have h₀₀₀₁ := tendsto_regular_hpl_one (f := fun _ => 60) continuousAt_const [zero, zero, one]
  have h₀₀₁ := tendsto_regular_hpl_one (f := fun x => -30*x - 15 + 30/x)
    (by fun_prop (disch := norm_num)) [zero, one]
  have h₀₀₁₀ := tendsto_regular_hpl_one (f := fun _ => 48) continuousAt_const [zero, one, zero]
  have h₀₀₁₁ := tendsto_regular_hpl_one (f := fun _ => 96) continuousAt_const [zero, one, one]
  have h₀₁ := tendsto_regular_hpl_one (f := fun x => 4*x^2 - 68*x - 47 + 51/x)
    (by fun_prop (disch := norm_num)) [one]
  have h₀₁₀ := tendsto_regular_hpl_one (f := fun x => -24*x - 10 + 24/x)
    (by fun_prop (disch := norm_num)) [one, zero]
  have h₀₁₀₀ := tendsto_regular_hpl_one (f := fun _ => 36) continuousAt_const [one, zero, zero]
  have h₀₁₀₁ := tendsto_regular_hpl_one (f := fun _ => 126) continuousAt_const [one, zero, one]
  have h₀₁₁ := tendsto_regular_hpl_one (f := fun x => -48*x - 43 + 48/x)
    (by fun_prop (disch := norm_num)) [one, one]
  have h₀₁₁₀ := tendsto_regular_hpl_one (f := fun _ => 156) continuousAt_const [one, one, zero]
  have h₀₁₁₁ := tendsto_regular_hpl_one (f := fun _ => 234) continuousAt_const [one, one, one]
  have h₁ := tendsto_scaled_hpl_one (f := fun x => (-6*x^3 + 86*x^2 + 51*x) / x^2)
    (by fun_prop (disch := norm_num)) [one]
  have h₁₀ := tendsto_scaled_hpl_one (f := fun x => (-7*x^3 + 105*x^2 + 48*x) / x^2)
    (by fun_prop (disch := norm_num)) [one, zero]
  have h₁₀₀ := tendsto_scaled_hpl_one (f := fun x => (18*x^2 + 18*x) / x^2)
    (by fun_prop (disch := norm_num)) [one, zero, zero]
  have h₁₀₁ := tendsto_scaled_hpl_one (f := fun x => (60*x^2 + 69*x - 3) / x^2)
    (by fun_prop (disch := norm_num)) [one, zero, one]
  have h₁₁ := tendsto_scaled_hpl_one (f := fun x => (-8*x^3 + 130*x^2 + 63*x + 6) / x^2)
    (by fun_prop (disch := norm_num)) [one, one]
  have h₁₁₀ := tendsto_scaled_hpl_one (f := fun x => (72*x^2 + 90*x - 6) / x^2)
    (by fun_prop (disch := norm_num)) [one, one, zero]
  have h₁₁₁ := tendsto_scaled_hpl_one (f := fun x => (108*x^2 + 135*x - 9) / x^2)
    (by fun_prop (disch := norm_num)) [one, one, one]
  have h := (((((((((ht.add h₀).add h₀₀).add h₀₀₀₁).add h₀₀₁).add h₀₀₁₀).add h₀₀₁₁).add
    h₀₁).add h₀₁₀).add h₀₁₀₀).add h₀₁₀₁
  have h := (((((((((h.add h₀₁₁).add h₀₁₁₀).add h₀₁₁₁).add
    h₁).add h₁₀).add h₁₀₀).add h₁₀₁).add h₁₁).add h₁₁₀).add h₁₁₁
  simp only [hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_one_at_one,
    hpl_zero_zero_one_at_one, hpl_zero_zero_one_zero_at_one, hpl_zero_zero_one_one_at_one,
    hpl_zero_one_at_one, hpl_zero_one_zero_at_one, hpl_zero_one_zero_zero_at_one,
    hpl_zero_one_zero_one_at_one, hpl_zero_one_one_at_one, hpl_zero_one_one_zero_at_one,
    hpl_zero_one_one_one_at_one, mul_zero, add_zero] at h
  convert h.congr' ?_ using 2
  · ring
  · filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with x hx
    simp only [i10K2QuadraticPrimitive, i10K2QuadraticPrimitiveTerms,
      kaHplSum, hpl_nil]
    field_simp [hx.1.ne']
    ring

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

private theorem tendsto_trilog_div_zero :
    Tendsto (fun x => Li₃ x / x) (𝓝[>] 0) (𝓝 1) := by
  have hV : Tendsto (fun x => (Li₂ x / x) / 1) (𝓝[>] 0) (𝓝 1) := by
    simpa only [div_one] using tendsto_Li₂_div_zero
  exact HasDerivAt.lhopital_zero_right_on_Ioo zero_lt_one
    (fun _ hx => hasDerivAt_Li₃' hx) (fun x _ => hasDerivAt_id' x) (fun _ _ => one_ne_zero)
    tendsto_Li₃_zero_right tendsto_cut_zero hV

private theorem tendsto_hpl_zero_one_one_div_zero :
    Tendsto (fun x => hpl [zero, one, one] x / x) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_log_one_sub_div_zero'.pow 2).mul tendsto_cut_zero
  have hV : Tendsto (fun x => (x⁻¹ * hpl [one, one] x) / 1) (𝓝[>] 0) (𝓝 0) := by
    have he := h.div_const 2
    simp only [mul_zero, zero_div] at he
    refine he.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with x hx
    rw [hpl_one_one hx]
    field_simp [hx.1.ne']
  exact HasDerivAt.lhopital_zero_right_on_Ioo zero_lt_one
    (fun _ hx => hasDerivAt_hpl_cons zero [one, one] hx) (fun x _ => hasDerivAt_id' x)
    (fun _ _ => one_ne_zero) (tendsto_hpl_zero (by simp [AllZero])) tendsto_cut_zero hV

private noncomputable def leftLogSqCoeff (p : ℝ × ℝ × ℝ) : ℝ :=
  let (x, e, _) := p
  9 * e * x ^ 2 - 9 * e - 15 * x / 2 - 21

private noncomputable def leftLogCoeff (p : ℝ × ℝ × ℝ) : ℝ :=
  let (x, e, f) := p
  (-36) * e ^ 2 * x ^ 4 - 42 * e + 6 * f - 2 +
    x ^ 3 * (-9 * e ^ 2 + 65 * e) +
    x ^ 2 * (48 * e ^ 2 + 130 * e - 6 * f - 29) +
    x * (-3 * e ^ 2 - 153 * e - 10 * f - 121)

private noncomputable def leftRegularCoeff (p : ℝ × ℝ × ℝ) : ℝ :=
  let (x, e, f) := p
  18 * e ^ 3 * x ^ 6 - 60 * e + 6 * f - 50 +
    x ^ 5 * (9 * e ^ 3 / 2 - 50 * e ^ 2) +
    x ^ 4 * (-24 * e ^ 3 - 165 * e ^ 2 / 2 - 12 * e * f + 46 * e) +
    x ^ 3 * (3 * e ^ 3 / 2 + 211 * e ^ 2 / 2 - 9 * e * f + 267 * e / 2 + 9 * f - 14) +
    x ^ 2 * (24 * e ^ 2 + 24 * e * f - 56 * e + 53 * f - 117 / 2) +
    x * (3 * e ^ 2 - 3 * e * f - 127 * e / 2 - 128 * f + 37 / 2)

private noncomputable def leftData (x : ℝ) : ℝ × ℝ × ℝ :=
  (x, logRemainder x, dilogRemainder x)

private noncomputable def quarticTerms : List (ℝ × List Letter) :=
  [(60, [zero, zero, zero, one]), (48, [zero, zero, one, zero]),
   (96, [zero, zero, one, one]), (36, [zero, one, zero, zero]),
   (126, [zero, one, zero, one]), (156, [zero, one, one, zero]),
   (234, [zero, one, one, one])]

private theorem quadraticPrimitive_eq_left {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i10K2QuadraticPrimitive x =
      60 + (x * log x ^ 2) * leftLogSqCoeff (leftData x) +
      (x * log x) * leftLogCoeff (leftData x) +
      x * (leftRegularCoeff (leftData x) + 5 * (Li₃ x / x - 1) -
        43 * (hpl [zero, one, one] x / x)) + kaHplSum x quarticTerms := by
  simp only [i10K2QuadraticPrimitive, i10K2QuadraticPrimitiveTerms, kaHplSum, hpl_nil]
  rw [hpl_one_zero_zero hx, hpl_zero_one_zero hx, hpl_one_one_zero hx,
    hpl_one_zero_one hx, hpl_one_one_one hx, hpl_zero_zero_one hx, hpl_one_zero hx,
    hpl_one_one hx, hpl_zero_zero x, hpl_zero_one hx, hpl_one hx, hpl_zero x,
    show Li 2 x = Li₂ x from rfl, show Li 3 x = Li₃ x from rfl]
  simp only [leftLogSqCoeff, leftLogCoeff, leftRegularCoeff, leftData, logRemainder,
    dilogRemainder, quarticTerms, kaHplSum]
  field_simp [hx.1.ne']
  ring

private theorem tendsto_quarticTerms_zero (terms : List (ℝ × List Letter))
    (hterms : ∀ e ∈ terms, ¬AllZero e.2) :
    Tendsto (kaHplSum · terms) (𝓝[>] 0) (𝓝 0) := by
  induction terms with
  | nil => exact tendsto_const_nhds
  | cons e terms ih =>
    obtain ⟨a, w⟩ := e
    have hw := tendsto_hpl_zero (hterms (a, w) List.mem_cons_self)
    simpa only [kaHplSum, mul_zero, zero_add] using
      (hw.const_mul a).add (ih fun e he => hterms e (List.mem_cons_of_mem _ he))

/-- The cancellation of the power and logarithmic terms at the left endpoint. -/
theorem tendsto_i10K2QuadraticPrimitive_zero :
    Tendsto i10K2QuadraticPrimitive (𝓝[>] 0) (𝓝 60) := by
  have hP : Tendsto leftData (𝓝[>] 0) (𝓝 (0, -(1 / 2), 1 / 4)) :=
    tendsto_cut_zero.prodMk_nhds (tendsto_logRemainder_zero.prodMk_nhds
      tendsto_dilogRemainder_zero)
  have hA : Continuous leftLogSqCoeff := by unfold leftLogSqCoeff; fun_prop
  have hB : Continuous leftLogCoeff := by unfold leftLogCoeff; fun_prop
  have hC : Continuous leftRegularCoeff := by unfold leftRegularCoeff; fun_prop
  have h₁ := tendsto_mul_log_sq_zero.mul (hA.continuousAt.tendsto.comp hP)
  have h₂ := tendsto_mul_log_zero.mul (hB.continuousAt.tendsto.comp hP)
  have h₃ := tendsto_cut_zero.mul
    (((hC.continuousAt.tendsto.comp hP).add
      ((tendsto_trilog_div_zero.sub_const 1).const_mul 5)).sub
      (tendsto_hpl_zero_one_one_div_zero.const_mul 43))
  have h₄ := tendsto_quarticTerms_zero quarticTerms (by simp [quarticTerms, AllZero])
  have h := (((h₁.const_add (60 : ℝ)).add h₂).add h₃).add h₄
  simp only [zero_mul, add_zero] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with x hx
  exact (quadraticPrimitive_eq_left hx).symm

/-- The definite reduced quadratic integral, given its absolute integrability. -/
theorem integral_i10K2QuadraticReduced
    (hi : IntegrableOn i10K2QuadraticReduced (Ioo (0 : ℝ) 1)) :
    ∫ x in Ioo (0 : ℝ) 1, i10K2QuadraticReduced x =
      121 * π ^ 4 / 60 - 10 * π ^ 2 - 38 * zeta3 - 49 := by
  have hi' := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hi
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
      (fun _ hx => hasDerivAt_i10K2QuadraticPrimitive hx) hi'
      tendsto_i10K2QuadraticPrimitive_zero tendsto_i10K2QuadraticPrimitive_one]
  ring

/-- Group the cancellation at the left endpoint before estimating the quadratic derivative. -/
theorem i10K2PsiTwoDeriv_scaled {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    let e := (log (1 - t) + t) / t ^ 2
    let f := (Li₂ t - t) / t ^ 2
    t * i10K2PsiTwoDeriv t =
      (-2 - 3 * ((1 - t) * e)) * log t +
      (6 * ((1 - t) * t ^ 2 * e ^ 2) - 3 * (3 * t + 2) * ((1 - t) * e) +
        3 * ((1 - t) * f) - 3 * (t + 1)) := by
  simp only [i10K2PsiTwoDeriv]
  field_simp [ht.1.ne', (sub_pos.mpr ht.2).ne']
  ring

end QED.ThreeLoopE
