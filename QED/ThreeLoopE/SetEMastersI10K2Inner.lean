/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI10K2Psi
public import QED.ThreeLoopE.SetEMastersI10K2UMoments
import QED.ThreeLoopE.SetEMastersI10K2Join
import QED.ThreeLoopD.SetDMastersI9Analytic
import QED.ThreeLoopE.SetEMastersI10KabVal
import Mathlib.Analysis.Complex.Liouville

/-!
# Integrating the innermost parameter of the two `K₂` coefficients

A Cauchy estimate for the subtracted integrand gives absolute integrability
before applying Fubini. The affine logarithmic moments give the two functions
that enter the remaining interpolation subtraction.
-/

@[expose] public section

open Real Set MeasureTheory QED.Polylog QED.ThreeLoopD

namespace QED.ThreeLoopE

/-- The first integrated coefficient of the inner function. -/
noncomputable def i10K2PsiOne (t : ℝ) : ℝ :=
  -log t / 2 - 3 / 2 + 3 / (2 * t) + 3 / 2 * ((1 - t) ^ 2 * log (1 - t)) / t ^ 2

/-- The second integrated coefficient of the inner function. -/
noncomputable def i10K2PsiTwo (t : ℝ) : ℝ :=
  let c := 1 - t
  let a := log t
  let b := log c
  (-(a ^ 2)) / 4 + 3 * c * a / (2 * t) - 5 + 6 / t +
    3 * c ^ 2 / (2 * t ^ 2) * (-Li₂ t + a * b - 2 * b ^ 2 + 3 * b)

private theorem k2Inner_base_power {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
    IntervalIntegrable (fun u => i10PsiBase t u * log (i10PsiBase t u) ^ n) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le zero_le_one]
  have hq : Continuous (i10PsiBase t) := by unfold i10PsiBase; fun_prop
  exact hq.continuousOn.mul ((continuousOn_log.comp hq.continuousOn
    (fun u hu => (i10PsiBase_pos ht hu).ne')).pow n)

/-- The two inner coefficient integrals as functions of the affine joining argument. -/
theorem integral_i10K2PsiCoeff {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (IntegrableOn (i10PsiCoeffOne t) (Ioo 0 1) ∧
      ∫ u in Ioo (0 : ℝ) 1, i10PsiCoeffOne t u = i10K2PsiOne t) ∧
    (IntegrableOn (i10PsiCoeffTwo t) (Ioo 0 1) ∧
      ∫ u in Ioo (0 : ℝ) 1, i10PsiCoeffTwo t u = i10K2PsiTwo t) := by
  have hq₁ := k2Inner_base_power ht 1
  have hq₂ := k2Inner_base_power ht 2
  simp only [pow_one] at hq₁
  have hm := (integral_i10K2U_log_mul_log ht).1
  have he (u : ℝ) : 1 - t + t * u = i10PsiBase t u := by unfold i10PsiBase; ring
  simp only [he] at hm
  have hw₁ := (integral_i10K2U_weight_log_sub (log t)).1
  have hw₂ := (integral_i10K2U_weight_log_sub_sq (log t)).1
  have hi₁ : IntervalIntegrable (i10PsiCoeffOne t) volume 0 1 := by
    convert (hw₁.const_mul (-1)).sub (hq₁.const_mul (3 / t)) using 1
    funext u
    unfold i10PsiCoeffOne
    ring
  have hi₂ : IntervalIntegrable (i10PsiCoeffTwo t) volume 0 1 := by
    have hmid := ((hq₁.const_mul (log t)).sub hm).const_mul (3 / t)
    convert ((hw₂.const_mul (-(1 / 2))).sub hmid).add (hq₂.const_mul (9 / (2 * t))) using 1
    funext u
    unfold i10PsiCoeffTwo
    ring
  refine ⟨i10_ioo_of_interval ⟨hi₁, ?_⟩, i10_ioo_of_interval ⟨hi₂, ?_⟩⟩
  · exact integral_i10K2U_coeff_one ht
  · have hv := integral_i10K2U_coeff_two ht
    change (∫ u in (0 : ℝ)..1, i10PsiCoeffTwo t u) = _ at hv
    rw [hv]
    unfold i10K2PsiTwo i10K2UPrimOne i10K2UPrimTwo
    simp only [log_one, one_pow, zero_pow two_ne_zero, sub_zero]
    field_simp [ht.1.ne']
    ring

private noncomputable def k2CauchyBound (p : (ℝ × ℝ × ℝ) × ℝ) : ℝ :=
  8 * (((p.1.1 * (1 - p.1.1)) ^ (-(11 / 20) : ℝ) *
    ((p.1.2.1 * (1 - p.1.2.1)) ^ (-(11 / 20) : ℝ) *
      (p.1.2.2 * (1 - p.1.2.2)) ^ (-(11 / 20) : ℝ))) * p.2 ^ (-(7 / 10) : ℝ))

private theorem k2Inner_measurableSet : MeasurableSet i10K2Domain :=
  (measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)).prod measurableSet_Ioo

private theorem k2Inner_norm_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {p : (ℝ × ℝ × ℝ) × ℝ}
    (hp : p ∈ i10K2Domain) : ‖i10K2F ε p‖ ≤ k2CauchyBound p := by
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
    _ = k2CauchyBound p := by
      rw [k2CauchyBound, Real.sqrt_eq_rpow]
      rw [Real.mul_rpow hr.1.le hs.1.le,
        Real.mul_rpow hr.1.le hr'.le, Real.mul_rpow hs.1.le hs'.le]
      have e := rpow_mul_rpow_eq (t := z * (1 - z)) (a := -(21 / 20 : ℝ)) (c := -(11 / 20))
        hc (by norm_num : -(21 / 20 : ℝ) + 1 / 2 = -(11 / 20))
      rw [← e]
      ring

private theorem integrable_k2CauchyBound : IntegrableOn k2CauchyBound i10K2Domain := by
  simp only [IntegrableOn, i10K2Domain, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact ((integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
    ((integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
      (integrableOn_mul_one_sub_rpow_Ioo (by norm_num))) |>.mul_prod
    (integrableOn_rpow_Ioo (by norm_num))).const_mul 8

private theorem k2Inner_differentiable {p : (ℝ × ℝ × ℝ) × ℝ} (hp : p ∈ i10K2Domain) :
    Differentiable ℂ fun ε => i10K2F ε p := by
  have hz := hp.1.1
  have hr := hp.1.2.1
  have hs := hp.1.2.2
  have hu := hp.2
  have ha {x : ℝ} (hx : x < 1) : Differentiable ℂ fun ε => i10A ε x :=
    fun ε => differentiableAt_id.neg.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (sub_pos.mpr hx).ne'))
  have hw : Differentiable ℂ fun ε => i10W ε p.1.1 := fun ε =>
    (differentiableAt_id.sub_const _).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (i9_c_pos hz).ne'))
  have hb : Differentiable ℂ fun ε => i10K2B ε p.1 p.2 := by
    unfold i10K2B
    exact (((differentiable_i10PsiF (i10Tau_mem_Ioo hz hr hs) hu).sub
      ((differentiable_i10PsiF hs hu).const_mul _)).sub
      ((differentiable_i10PsiF hr hu).const_mul _))
  exact (((ha hr.2).mul (ha hs.2)).mul hw).mul hb

private theorem k2Inner_cauchy {p : (ℝ × ℝ × ℝ) × ℝ} (hp : p ∈ i10K2Domain) (n : ℕ) :
    ‖iteratedDeriv n (fun w => i10K2F w p) 0‖ ≤ n.factorial * k2CauchyBound p / (1 / 40) ^ n := by
  refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0 : ℝ) < 1 / 40)
    ((k2Inner_differentiable hp).differentiableOn.diffContOnCl_ball Subset.rfl) ?_
  intro w hw
  rw [Metric.mem_sphere, dist_zero_right] at hw
  exact k2Inner_norm_le (by linarith) hp

/-- The original coefficient integrands are integrable on the full four-parameter domain. -/
theorem integrableOn_i10K2_coefficients :
    IntegrableOn i10K2CoeffOne i10K2Domain ∧ IntegrableOn i10K2CoeffTwo i10K2Domain := by
  constructor
  · refine (integrable_k2CauchyBound.div_const (1 / 40)).mono' ?_
      (ae_restrict_of_forall_mem k2Inner_measurableSet fun p hp => ?_)
    · exact (by
        unfold i10K2CoeffOne i10K2Interpolation i10PsiCoeffOne i10PsiBase i10Tau
        fun_prop : Measurable i10K2CoeffOne).aestronglyMeasurable
    · have h := k2Inner_cauchy hp 1
      rw [iteratedDeriv_one, deriv_i10K2F_zero hp, Complex.norm_real] at h
      simpa only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one] using h
  · refine (integrable_k2CauchyBound.div_const ((1 / 40) ^ 2)).mono' ?_
      (ae_restrict_of_forall_mem k2Inner_measurableSet fun p hp => ?_)
    · exact (by
        unfold i10K2CoeffTwo i10K2LogWeight i10K2Interpolation i10PsiCoeffOne
          i10PsiCoeffTwo i10PsiBase i10Tau
        fun_prop : Measurable i10K2CoeffTwo).aestronglyMeasurable
    · have h := k2Inner_cauchy hp 2
      rw [iteratedDeriv_two_i10K2F_zero hp, norm_mul, Complex.norm_real] at h
      norm_num at h ⊢
      linarith


/-- The outer integration cube for the two coefficients of `K₂`. -/
def i10K2OuterDomain : Set (ℝ × ℝ × ℝ) :=
  Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)

/-- Degree one after integrating over the innermost parameter. -/
noncomputable def i10K2OuterOne (q : ℝ × ℝ × ℝ) : ℝ :=
  let (z, r, s) := q
  i10K2Interpolation i10K2PsiOne z r s / (z * (1 - z))

/-- Degree two after integrating over the innermost parameter. -/
noncomputable def i10K2OuterTwo (q : ℝ × ℝ × ℝ) : ℝ :=
  let (z, r, s) := q
  (i10K2Interpolation i10K2PsiTwo z r s +
    i10K2LogWeight z r s * i10K2Interpolation i10K2PsiOne z r s) / (z * (1 - z))

private theorem k2Inner_integral_interpolation {f : ℝ → ℝ → ℝ} {z r s : ℝ}
    (hr : IntegrableOn (f r) (Ioo 0 1)) (hs : IntegrableOn (f s) (Ioo 0 1))
    (ht : IntegrableOn (f (i10Tau z r s)) (Ioo 0 1)) :
    IntegrableOn (fun u => i10K2Interpolation (fun x => f x u) z r s) (Ioo 0 1) ∧
      ∫ u in Ioo (0 : ℝ) 1, i10K2Interpolation (fun x => f x u) z r s =
        i10K2Interpolation (fun x => ∫ u in Ioo (0 : ℝ) 1, f x u) z r s := by
  unfold i10K2Interpolation
  refine ⟨(ht.sub (hs.const_mul _)).sub (hr.const_mul _), ?_⟩
  have h₁ := integral_sub (ht.sub (hs.const_mul (1 - z))) (hr.const_mul z)
  have h₂ := integral_sub ht (hs.const_mul (1 - z))
  simp only [Pi.sub_apply] at h₁
  rw [h₁, h₂, integral_const_mul, integral_const_mul]

private theorem k2Inner_section {q : ℝ × ℝ × ℝ} (hq : q ∈ i10K2OuterDomain) :
    (∫ u in Ioo (0 : ℝ) 1, i10K2CoeffOne (q, u)) = i10K2OuterOne q ∧
    (∫ u in Ioo (0 : ℝ) 1, i10K2CoeffTwo (q, u)) = i10K2OuterTwo q := by
  rcases q with ⟨z, r, s⟩
  have hz : z ∈ Ioo (0 : ℝ) 1 := hq.1
  have hr : r ∈ Ioo (0 : ℝ) 1 := hq.2.1
  have hs : s ∈ Ioo (0 : ℝ) 1 := hq.2.2
  have hR := integral_i10K2PsiCoeff hr
  have hS := integral_i10K2PsiCoeff hs
  have hT := integral_i10K2PsiCoeff (i10Tau_mem_Ioo hz hr hs)
  have h₁ := k2Inner_integral_interpolation hR.1.1 hS.1.1 hT.1.1
  have h₂ := k2Inner_integral_interpolation hR.2.1 hS.2.1 hT.2.1
  have h₁' : (∫ u in Ioo (0 : ℝ) 1, i10K2Interpolation (fun t => i10PsiCoeffOne t u) z r s) =
      i10K2Interpolation i10K2PsiOne z r s := by
    rw [h₁.2, i10K2Interpolation, hR.1.2, hS.1.2, hT.1.2]
    rfl
  have h₂' : (∫ u in Ioo (0 : ℝ) 1, i10K2Interpolation (fun t => i10PsiCoeffTwo t u) z r s) =
      i10K2Interpolation i10K2PsiTwo z r s := by
    rw [h₂.2, i10K2Interpolation, hR.2.2, hS.2.2, hT.2.2]
    rfl
  constructor
  · dsimp only [i10K2CoeffOne, i10K2OuterOne]
    rw [integral_div, h₁']
  · dsimp only [i10K2CoeffTwo, i10K2OuterTwo]
    rw [integral_div, integral_add h₂.1 (h₁.1.const_mul (i10K2LogWeight z r s)),
      integral_const_mul, h₁', h₂']

private theorem k2Inner_fubini {f : (ℝ × ℝ × ℝ) × ℝ → ℝ} {g : ℝ × ℝ × ℝ → ℝ}
    (hf : IntegrableOn f i10K2Domain)
    (he : ∀ q ∈ i10K2OuterDomain, (∫ u in Ioo (0 : ℝ) 1, f (q, u)) = g q) :
    IntegrableOn g i10K2OuterDomain ∧ ∫ p in i10K2Domain, f p = ∫ q in i10K2OuterDomain, g q := by
  let S := i10K2OuterDomain
  let T := Ioo (0 : ℝ) 1
  have hS : MeasurableSet S := measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)
  change IntegrableOn f (S ×ˢ T) at hf
  have hfi : Integrable f ((volume.restrict S).prod (volume.restrict T)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hf
  refine ⟨hfi.integral_prod_left.congr (ae_restrict_of_forall_mem hS he), ?_⟩
  change (∫ p in S ×ˢ T, f p) = ∫ q in S, g q
  rw [Measure.volume_eq_prod] at hf ⊢
  rw [setIntegral_prod f hf]
  exact setIntegral_congr_fun hS he

/-- Fubini removes the inner integration variable from both original coefficient integrals. -/
theorem integral_i10K2_coefficients_outer :
    (IntegrableOn i10K2OuterOne i10K2OuterDomain ∧
      ∫ p in i10K2Domain, i10K2CoeffOne p = ∫ q in i10K2OuterDomain, i10K2OuterOne q) ∧
    (IntegrableOn i10K2OuterTwo i10K2OuterDomain ∧
      ∫ p in i10K2Domain, i10K2CoeffTwo p = ∫ q in i10K2OuterDomain, i10K2OuterTwo q) :=
  ⟨k2Inner_fubini integrableOn_i10K2_coefficients.1 fun _ hq => (k2Inner_section hq).1,
   k2Inner_fubini integrableOn_i10K2_coefficients.2 fun _ hq => (k2Inner_section hq).2⟩


/-- The derivative of the degree-one inner moment, with its cancellation at zero grouped. -/
theorem hasDerivAt_i10K2PsiOne {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i10K2PsiOne
      (1 / t - 3 * (t + (1 - t) * log (1 - t)) / t ^ 3) t := by
  have hc := (sub_pos.mpr ht.2).ne'
  have dt := hasDerivAt_id' t
  have dc := dt.const_sub (1 : ℝ)
  have h₁ := (((hasDerivAt_log ht.1.ne').neg.div_const 2).sub_const (3 / 2)).add
    ((hasDerivAt_const t (3 : ℝ)).div (dt.const_mul 2) (mul_ne_zero two_ne_zero ht.1.ne'))
  have h₂ := (((dc.pow 2).mul (dc.log hc)).const_mul (3 / 2)).div (dt.pow 2)
    (pow_ne_zero 2 ht.1.ne')
  have h : HasDerivAt i10K2PsiOne _ t := h₁.add h₂
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply]
  field_simp [ht.1.ne', hc]
  ring

/-- A derivative bound for integrating the linear coefficient in distance coordinates. -/
theorem abs_deriv_i10K2PsiOne_le {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    |deriv i10K2PsiOne t| ≤ 2 / t := by
  let c := 1 - t
  have hc : 0 < c := sub_pos.mpr ht.2
  have hlow : 0 ≤ t + c * log c := by
    have h := log_le_sub_one_of_pos (inv_pos.mpr hc)
    rw [log_inv, inv_eq_one_div] at h
    have h' := (le_div_iff₀ hc).1
      (show 1 - log c ≤ 1 / c by linarith only [h])
    dsimp only [c] at h' ⊢
    linarith only [h']
  have hupp : t + c * log c ≤ t ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos hc) hc.le
    dsimp only [c] at h ⊢
    nlinarith only [h]
  have hI : 0 < t ^ 3 := pow_pos ht.1 _
  have hlow' : 0 ≤ 3 * (t + c * log c) / t ^ 3 := div_nonneg (by positivity) hI.le
  have hupp' : 3 * (t + c * log c) / t ^ 3 ≤ 3 / t := by
    apply (div_le_iff₀ hI).2
    rw [show 3 / t * t ^ 3 = 3 * t ^ 2 by field_simp [ht.1.ne']]
    exact mul_le_mul_of_nonneg_left hupp (by norm_num)
  rw [(hasDerivAt_i10K2PsiOne ht).deriv, abs_le]
  change -(2 / t) ≤ 1 / t - 3 * (t + c * log c) / t ^ 3 ∧
    1 / t - 3 * (t + c * log c) / t ^ 3 ≤ 2 / t
  have hpos : 0 ≤ 1 / t := one_div_nonneg.mpr ht.1.le
  have htwo : 2 / t = 2 * (1 / t) := by ring
  have hthree : 3 / t = 3 * (1 / t) := by ring
  rw [htwo]
  rw [hthree] at hupp'
  exact ⟨by linarith only [hupp'], by linarith only [hlow', hpos]⟩

/-- Integration in the joining parameter of the linear coefficient for fixed bubbles. -/
theorem integral_i10K2OuterOne_join {r s : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    (∫ z in Ioo (0 : ℝ) 1, i10K2OuterOne (z, r, s)) =
      ∫ z in Ioo (0 : ℝ) 1,
        ((r - s) * deriv i10K2PsiOne (i10Tau z r s)) * (log (1 - z) - log z) := by
  let g : ℝ → ℝ := fun z => i10K2PsiOne (i10Tau z r s)
  let g' : ℝ → ℝ := fun z => (r - s) * deriv i10K2PsiOne (i10Tau z r s)
  have hτ (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : i10Tau z r s ∈ Ioo (0 : ℝ) 1 := by
    have e₁ : i10Tau z r s = min r s + (z * (r - min r s) + (1 - z) * (s - min r s)) := by
      unfold i10Tau
      ring
    have e₂ : i10Tau z r s = max r s - (z * (max r s - r) + (1 - z) * (max r s - s)) := by
      unfold i10Tau
      ring
    constructor
    · rw [e₁]
      exact add_pos_of_pos_of_nonneg (lt_min hr.1 hs.1)
        (add_nonneg (mul_nonneg hz.1 (sub_nonneg.mpr (min_le_left _ _)))
          (mul_nonneg (sub_nonneg.mpr hz.2) (sub_nonneg.mpr (min_le_right _ _))))
    · rw [e₂]
      exact (sub_le_self _ (add_nonneg (mul_nonneg hz.1 (sub_nonneg.mpr (le_max_left _ _)))
        (mul_nonneg (sub_nonneg.mpr hz.2) (sub_nonneg.mpr (le_max_right _ _))))).trans_lt
        (max_lt hr.2 hs.2)
  have hder (z : ℝ) : HasDerivAt (fun z => i10Tau z r s) (r - s) z := by
    have h := ((hasDerivAt_id' z).mul_const r).add
      (((hasDerivAt_id' z).const_sub 1).mul_const s)
    exact h.congr_deriv (by ring)
  have hD (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : HasDerivAt g (g' z) z := by
    have h := (hasDerivAt_i10K2PsiOne (hτ z hz)).comp z (hder z)
    refine h.congr_deriv ?_
    unfold g'
    rw [(hasDerivAt_i10K2PsiOne (hτ z hz)).deriv]
    ring
  have hC : ContinuousOn (deriv i10K2PsiOne) (Ioo (0 : ℝ) 1) := by
    have hE (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
        ContinuousAt (fun y => 1 / y - 3 * (y + (1 - y) * log (1 - y)) / y ^ 3) t := by
      have ht₀ := ht.1.ne'
      have hc := (sub_pos.mpr ht.2).ne'
      have ht₃ := pow_ne_zero 3 ht₀
      fun_prop
    have hcont : ContinuousOn (fun y => 1 / y - 3 * (y + (1 - y) * log (1 - y)) / y ^ 3)
        (Ioo (0 : ℝ) 1) := fun t ht => (hE t ht).continuousWithinAt
    exact hcont.congr (fun t ht => (hasDerivAt_i10K2PsiOne ht).deriv)
  have hg' : ContinuousOn g' (Icc (0 : ℝ) 1) :=
    (hC.comp (fun z _ => (hder z).continuousAt.continuousWithinAt) hτ).const_mul _
  simp only [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have e₀ : g 0 = i10K2PsiOne s := by simp [g, i10Tau]
  have e₁ : g 1 = i10K2PsiOne r := by simp [g, i10Tau]
  have h := integral_i10K2_interpolation hD hg'
  rw [e₀, e₁] at h
  exact h


/-- The joining integral in the affine argument, with oriented limits for either bubble order. -/
theorem integral_i10K2OuterOne_interval {r s : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    (∫ z in Ioo (0 : ℝ) 1, i10K2OuterOne (z, r, s)) =
      ∫ t in s..r, deriv i10K2PsiOne t * (log (r - t) - log (t - s)) := by
  rw [integral_i10K2OuterOne_join hr hs, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]
  rcases eq_or_ne r s with rfl | hne
  · simp only [sub_self, zero_mul, intervalIntegral.integral_zero, intervalIntegral.integral_same]
  · let F := fun t => deriv i10K2PsiOne t * (log (r - t) - log (t - s))
    calc
      _ = ∫ z in (0 : ℝ)..1, (r - s) * F ((r - s) * z + s) := by
        apply intervalIntegral.integral_congr_uIoo
        intro z hz
        rw [uIoo_of_le zero_le_one] at hz
        have e : (r - s) * z + s = i10Tau z r s := by unfold i10Tau; ring
        have e₁ : r - ((r - s) * z + s) = (r - s) * (1 - z) := by ring
        have e₂ : (r - s) * z + s - s = (r - s) * z := by ring
        dsimp only [F]
        rw [e₁, e₂, log_mul (sub_ne_zero.mpr hne) (sub_pos.mpr hz.2).ne',
          log_mul (sub_ne_zero.mpr hne) hz.1.ne', e]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul]
        have e := intervalIntegral.smul_integral_comp_mul_add F
          (a := (0 : ℝ)) (b := 1) (r - s) s
        simpa only [smul_eq_mul, mul_zero, zero_add, mul_one, sub_add_cancel] using e


/-- The linear coefficient as a bubble-pair integral of the oriented joining integral. -/
theorem integral_i10K2CoeffOne_joined :
    let T := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1
    let F := fun p : ℝ × ℝ => ∫ t in p.2..p.1,
      deriv i10K2PsiOne t * (log (p.1 - t) - log (t - p.2))
    IntegrableOn F T ∧
      (∫ p in i10K2Domain, i10K2CoeffOne p) = ∫ p in T, F p := by
  let S := Ioo (0 : ℝ) 1
  let T := S ×ˢ S
  let F := fun p : ℝ × ℝ => ∫ t in p.2..p.1,
      deriv i10K2PsiOne t * (log (p.1 - t) - log (t - p.2))
  have hT : MeasurableSet T := measurableSet_Ioo.prod measurableSet_Ioo
  obtain ⟨hi, hv⟩ := integral_i10K2_coefficients_outer.1
  have hi' : Integrable i10K2OuterOne ((volume.restrict S).prod (volume.restrict T)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hi
  have he (p : ℝ × ℝ) (hp : p ∈ T) : (∫ z in S, i10K2OuterOne (z, p)) = F p :=
    integral_i10K2OuterOne_interval hp.1 hp.2
  change IntegrableOn F T ∧ (∫ p in i10K2Domain, i10K2CoeffOne p) = ∫ p in T, F p
  refine ⟨hi'.integral_prod_right.congr (ae_restrict_of_forall_mem hT he), ?_⟩
  rw [hv]
  change (∫ q in S ×ˢ T, i10K2OuterOne q) = _
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ hi']
  exact setIntegral_congr_fun hT he

end QED.ThreeLoopE
