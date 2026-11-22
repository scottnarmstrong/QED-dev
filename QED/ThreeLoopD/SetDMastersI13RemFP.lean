/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13RemW
public import QED.ThreeLoopD.SetDMastersI9Strip
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Set (d), master `I₁₃`: the continued Beta integral `∫₀¹ w ^ (a - 1) φ(w) dw`

For `re a > 0`, `∫₀¹ w ^ (a - 1) φ(w) dw = B(a, 1/2)/2`. Subtracting the Taylor polynomial
`P = φ₀ + φ₁ w + φ₂ w²` of `φ` continues it to `re a > -3`:

  `FP(a) = φ₀/a + φ₁/(a + 1) + φ₂/(a + 2) + ∫₀¹ w ^ (a + 2) ψ(w) dw`.

Clearing the three poles, `Φ(a) = a(a + 1)(a + 2) FP(a)` (`QED.ThreeLoopD.i13FPhi`) is holomorphic
on `re a > -3`, and so is `Γ(a + 3) Γ(1/2) / (2 Γ(a + 1/2))`; they agree for `re a > 0`, hence on
the whole half-plane (`QED.ThreeLoopD.i13FPhi_eq_Gamma`, identity theorem).

At `a = 1 - ε, -ε, -1 - ε` these give the leading large-`t` coefficients of the bubble in the
form `QED.ThreeLoopD.i13Al0`, `i13Al1`, `i13Al2` via Legendre's duplication formula
(`QED.ThreeLoopD.i13Lc0_mul`, `i13Lc1_mul`, `i13Lc2_mul`).

## Main results

* `QED.ThreeLoopD.i13FPhi_eq_Gamma`.
* `QED.ThreeLoopD.i13Lc0_mul`, `QED.ThreeLoopD.i13Lc1_mul`, `QED.ThreeLoopD.i13Lc2_mul`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter Topology

namespace QED.ThreeLoopD

/-- `∫₀¹ w ^ (a + 2) ψ(w) dw`, convergent for `re a > -3`. -/
noncomputable def i13PsiInt (a : ℂ) : ℂ :=
  ∫ w in Ioo (0 : ℝ) 1, (w : ℂ) ^ (a + 2) * (i13Psi w : ℂ)

/-- `Φ(a) = a(a + 1)(a + 2) (φ₀/a + φ₁/(a + 1) + φ₂/(a + 2) + ∫₀¹ w ^ (a + 2) ψ)`, with the poles
cleared. -/
noncomputable def i13FPhi (a : ℂ) : ℂ :=
  1 / 2 * ((a + 1) * (a + 2)) + 1 / 4 * (a * (a + 2)) + 3 / 16 * (a * (a + 1)) +
    a * (a + 1) * (a + 2) * i13PsiInt a

/-- The Gamma side `Γ(a + 3) Γ(1/2) / (2 Γ(a + 1/2))`. -/
noncomputable def i13FGam (a : ℂ) : ℂ :=
  1 / 2 * Gamma (a + 3) * Gamma (1 / 2) * (Gamma (a + 1 / 2))⁻¹

theorem i13_norm_cpow_le {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) {a : ℂ} {r : ℝ} (ha : r ≤ a.re) :
    ‖(w : ℂ) ^ a‖ ≤ w ^ r := by
  rw [norm_cpow_eq_rpow_re_of_pos hw.1]
  exact Real.rpow_le_rpow_of_exponent_ge hw.1 hw.2.le ha

theorem integrableOn_i13PsiInt {a : ℂ} (ha : -3 < a.re) :
    IntegrableOn (fun w : ℝ => (w : ℂ) ^ (a + 2) * (i13Psi w : ℂ)) (Ioo 0 1) := by
  set r := min ((a.re + 3) / 2) (1 / 2) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
  refine Integrable.mono' (integrableOn_rpow_mul_phi hr0 (min_le_right _ _))
    ((by fun_prop : Measurable fun w : ℝ =>
      (w : ℂ) ^ (a + 2) * (i13Psi w : ℂ)).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun w hw => ?_)
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (i13Psi_nonneg hw)]
  refine mul_le_mul (i13_norm_cpow_le hw ?_) (i13Psi_le hw) (i13Psi_nonneg hw)
    (Real.rpow_nonneg hw.1.le _)
  rw [add_re]
  norm_num
  linarith [min_le_left ((a.re + 3) / 2) (1 / 2)]

theorem differentiableOn_i13PsiInt : DifferentiableOn ℂ i13PsiInt {a : ℂ | -3 < a.re} := by
  intro a₀ ha₀
  have ha₀' : -3 < a₀.re := ha₀
  set r := min ((a₀.re + 3) / 4) (1 / 2) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
  refine (QED.DimReg.differentiableAt_integral_of_holomorphic (z₁ := a₀) (R := (a₀.re + 3) / 2)
    (by linarith) (b := fun w => w ^ (r - 1) * i13Phi w)
    (integrableOn_rpow_mul_phi hr0 (min_le_right _ _))
    (fun a _ => (by fun_prop : Measurable fun w : ℝ =>
      (w : ℂ) ^ (a + 2) * (i13Psi w : ℂ)).aestronglyMeasurable) ?_ ?_).differentiableWithinAt
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun w hw a ha => ?_
    rw [mem_ball, dist_eq_norm] at ha
    have hre : a₀.re - (a₀.re + 3) / 2 < a.re := by
      have := abs_re_le_norm (a - a₀)
      rw [sub_re] at this
      linarith [neg_abs_le (a.re - a₀.re)]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (i13Psi_nonneg hw)]
    refine mul_le_mul (i13_norm_cpow_le hw ?_) (i13Psi_le hw) (i13Psi_nonneg hw)
      (Real.rpow_nonneg hw.1.le _)
    rw [add_re]
    norm_num
    linarith [min_le_left ((a₀.re + 3) / 4) (1 / 2)]
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun w hw => ?_
    have hw0 : (w : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw.1.ne'
    exact ((Differentiable.const_cpow (by fun_prop) (Or.inl hw0)).mul_const _).differentiableOn

theorem differentiableOn_i13FPhi : DifferentiableOn ℂ i13FPhi {a : ℂ | -3 < a.re} := by
  unfold i13FPhi
  have hp : Differentiable ℂ fun a : ℂ =>
      1 / 2 * ((a + 1) * (a + 2)) + 1 / 4 * (a * (a + 2)) + 3 / 16 * (a * (a + 1)) := by
    fun_prop
  exact hp.differentiableOn.add
    ((by fun_prop : Differentiable ℂ fun a : ℂ => a * (a + 1) * (a + 2)).differentiableOn.mul
      differentiableOn_i13PsiInt)

theorem differentiableOn_i13FGam : DifferentiableOn ℂ i13FGam {a : ℂ | -3 < a.re} := by
  intro a ha
  have ha' : -3 < a.re := ha
  have hG : DifferentiableAt ℂ (fun a : ℂ => Gamma (a + 3)) a := by
    refine (differentiableAt_Gamma _ fun m hm => ?_).comp a (by fun_prop)
    have := congr_arg re hm
    simp at this
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    linarith
  have hI : DifferentiableAt ℂ (fun a : ℂ => (Gamma (a + 1 / 2))⁻¹) a :=
    (differentiable_one_div_Gamma.comp (by fun_prop : Differentiable ℂ fun a : ℂ => a + 1 / 2)) a
  unfold i13FGam
  exact (((hG.const_mul _).mul_const _).mul hI).differentiableWithinAt

/-- The Taylor decomposition `φ = P + w³ ψ` on `(0, 1)`. -/
theorem i13Phi_eq_P_add {w : ℝ} (hw : w ≠ 0) :
    i13Phi w = 1 / 2 + w / 4 + 3 / 16 * w ^ 2 + w ^ 3 * i13Psi w := by
  unfold i13Psi i13PhiP
  field_simp
  ring

/-- For `re a > 0`,
`Φ(a) = a(a + 1)(a + 2) ∫₀¹ w ^ (a - 1) φ = Γ(a + 3) Γ(1/2) / (2 Γ(a + 1/2))`. -/
theorem i13FPhi_eq_Gamma_of_re_pos {a : ℂ} (ha : 0 < a.re) : i13FPhi a = i13FGam a := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have ha1 : a + 1 ≠ 0 := fun h => by
    have := congr_arg re h; simp at this; linarith
  have ha2 : a + 2 ≠ 0 := fun h => by
    have := congr_arg re h; simp at this; linarith
  -- `∫ w ^ (a - 1) φ = B(a, 1/2)/2`
  have hB : ∫ w in Ioo (0 : ℝ) 1, (w : ℂ) ^ (a - 1) * (i13Phi w : ℂ) =
      1 / 2 * (Gamma a * Gamma (1 / 2) / Gamma (a + 1 / 2)) := by
    have h := i9_integral_beta (u := a) (v := 1 / 2) ha (by norm_num)
    rw [i9Beta] at h
    rw [← h, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun w hw => ?_
    have h1w : 0 ≤ 1 - w := by linarith [hw.2]
    simp only [i13Phi]
    rw [ofReal_div, ofReal_cpow h1w]
    push_cast
    ring_nf
  -- split `φ = P + w³ ψ`
  have hint : ∀ k : ℕ, IntegrableOn (fun w : ℝ => (w : ℂ) ^ (a + k - 1)) (Ioo 0 1) := fun k =>
    i9_integrableOn_cpow (by simp; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
  have hval : ∀ k : ℕ, ∫ w in Ioo (0 : ℝ) 1, (w : ℂ) ^ (a + k - 1) = 1 / (a + k) := fun k =>
    i9_integral_cpow (by simp; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
  have hsplit : ∀ w ∈ Ioo (0 : ℝ) 1, (w : ℂ) ^ (a - 1) * (i13Phi w : ℂ) =
      1 / 2 * (w : ℂ) ^ (a + (0 : ℕ) - 1) + 1 / 4 * (w : ℂ) ^ (a + (1 : ℕ) - 1) +
        3 / 16 * (w : ℂ) ^ (a + (2 : ℕ) - 1) + (w : ℂ) ^ (a + 2) * (i13Psi w : ℂ) := by
    intro w hw
    have hw0 : (w : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw.1.ne'
    rw [i13Phi_eq_P_add hw.1.ne']
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, add_zero]
    rw [show a + 1 - 1 = (a - 1) + (1 : ℕ) by push_cast; ring,
      show a + 2 - 1 = (a - 1) + (2 : ℕ) by push_cast; ring,
      show a + 2 = (a - 1) + (3 : ℕ) by push_cast; ring, cpow_add _ _ hw0, cpow_add _ _ hw0,
      cpow_add _ _ hw0]
    simp only [cpow_natCast]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo hsplit, integral_add, integral_add, integral_add,
    integral_const_mul, integral_const_mul, integral_const_mul, hval, hval, hval] at hB
  · simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, add_zero] at hB
    unfold i13FPhi i13FGam i13PsiInt
    have hX : ∫ w in Ioo (0 : ℝ) 1, (w : ℂ) ^ (a + 2) * (i13Psi w : ℂ) =
        1 / 2 * (Gamma a * Gamma (1 / 2) / Gamma (a + 1 / 2)) -
          (1 / 2 * (1 / a) + 1 / 4 * (1 / (a + 1)) + 3 / 16 * (1 / (a + 2))) := by
      rw [← hB]; ring
    have hΓ : Gamma (a + 1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    rw [hX]
    have hG3 : Gamma (a + 3) = a * (a + 1) * (a + 2) * Gamma a := by
      rw [show a + 3 = (a + 2) + 1 by ring, Gamma_add_one _ ha2,
        show a + 2 = (a + 1) + 1 by ring, Gamma_add_one _ ha1, Gamma_add_one _ ha0]
      ring
    rw [hG3]
    field_simp
    ring
  all_goals first
    | exact (hint _).const_mul _
    | exact integrableOn_i13PsiInt (by linarith)
    | exact ((hint _).const_mul _).add ((hint _).const_mul _)
    | exact (((hint _).const_mul _).add ((hint _).const_mul _)).add ((hint _).const_mul _)

/-- **The continued Beta integral**: `Φ(a) = Γ(a + 3) Γ(1/2) / (2 Γ(a + 1/2))` on `re a > -3`. -/
theorem i13FPhi_eq_Gamma {a : ℂ} (ha : -3 < a.re) : i13FPhi a = i13FGam a := by
  have hU : IsOpen {a : ℂ | -3 < a.re} := isOpen_lt continuous_const continuous_re
  have hconv : Convex ℝ {a : ℂ | -3 < a.re} := convex_halfSpace_re_gt (-3)
  refine (differentiableOn_i13FPhi.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
    (differentiableOn_i13FGam.analyticOnNhd hU) hconv.isPreconnected (z₀ := 1) (by simp; norm_num)
    ?_ ha
  have hO : IsOpen {a : ℂ | 0 < a.re} := isOpen_lt continuous_const continuous_re
  exact eventually_of_mem (hO.mem_nhds (by simp)) fun a ha => i13FPhi_eq_Gamma_of_re_pos ha

/-! ### The leading coefficients -/

/-- `A₀ = Φ(1 - ε) / ((1 - ε)(2 - ε)(3 - ε))`. -/
noncomputable def i13Lc0 (ε : ℂ) : ℂ := i13FPhi (1 - ε) / ((1 - ε) * (2 - ε) * (3 - ε))

/-- `A₁ = Φ(-ε) / ((1 - ε)(2 - ε))`. -/
noncomputable def i13Lc1 (ε : ℂ) : ℂ := i13FPhi (-ε) / ((1 - ε) * (2 - ε))

/-- `A₂ = Φ(-1 - ε) / (2(1 - ε))`. -/
noncomputable def i13Lc2 (ε : ℂ) : ℂ := i13FPhi (-1 - ε) / (2 * (1 - ε))

theorem i13_eps_facts {ε : ℂ} (hε : ‖ε‖ < 1 / 2) :
    1 - ε ≠ 0 ∧ 2 - ε ≠ 0 ∧ 3 - ε ≠ 0 ∧ 1 - 2 * ε ≠ 0 ∧ 1 / 2 - ε ≠ 0 ∧
      -1 / 2 - ε ≠ 0 ∧ 0 < (1 / 2 - ε).re ∧ 0 < (1 - ε).re ∧ |ε.re| < 1 / 2 := by
  have hre : |ε.re| < 1 / 2 := (abs_re_le_norm ε).trans_lt hε
  have h1 := neg_abs_le ε.re
  have h2 := le_abs_self ε.re
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hre⟩
  all_goals first
    | (intro h; have := congr_arg re h; simp at this; linarith)
    | (simp; linarith)

theorem i13_Gamma_half : Gamma (1 / 2) = ↑(√Real.pi) := by
  rw [Gamma_one_half_eq, Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]
  push_cast
  ring_nf

/-- Legendre: `Γ(1/2 - ε) Γ(1 - ε) = Γ(1 - 2ε) 4 ^ ε √π`. -/
theorem i13_duplication (ε : ℂ) :
    Gamma (1 / 2 - ε) * Gamma (1 - ε) = Gamma (1 - 2 * ε) * ((4 : ℝ) : ℂ) ^ ε * ↑(√Real.pi) := by
  have h := Gamma_mul_Gamma_add_half (1 / 2 - ε)
  rw [show 1 / 2 - ε + 1 / 2 = 1 - ε by ring, show 2 * (1 / 2 - ε) = 1 - 2 * ε by ring,
    show (1 : ℂ) - (1 - 2 * ε) = ε + ε by ring, cpow_add _ _ two_ne_zero] at h
  rw [h, show ((4 : ℝ) : ℂ) = ((2 : ℝ) : ℂ) * ((2 : ℝ) : ℂ) by push_cast; norm_num,
    mul_cpow_ofReal_nonneg (by norm_num) (by norm_num)]
  push_cast
  ring

theorem i13_four_cpow_ne_zero (ε : ℂ) : ((4 : ℝ) : ℂ) ^ ε ≠ 0 := by
  rw [cpow_def_of_ne_zero (by norm_num)]
  exact exp_ne_zero _

/-- **The leading coefficients in Gamma form**: `4 ^ ε A₀ = α₀`, `4 ^ (1 + ε) A₁ = α₁`,
`4 ^ (2 + ε) A₂ = α₂`. -/
theorem i13Lc_gamma {ε : ℂ} (hε : ‖ε‖ < 1 / 2) :
    i13Lc0 ε * ((4 : ℝ) : ℂ) ^ ε = i13Al0 ε ∧ i13Lc1 ε * ((4 : ℝ) : ℂ) ^ ε * 4 = i13Al1 ε ∧
      i13Lc2 ε * ((4 : ℝ) : ℂ) ^ ε * 16 = i13Al2 ε := by
  obtain ⟨h1, h2, h3, h12, hh, hmh, hr, hr1, habs⟩ := i13_eps_facts hε
  have hΓ : Gamma (1 / 2 - ε) ≠ 0 := Gamma_ne_zero_of_re_pos hr
  have hg : Gamma (1 - ε) ≠ 0 := Gamma_ne_zero_of_re_pos hr1
  have hΓ2 : Gamma (1 - 2 * ε) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp; linarith [le_abs_self ε.re])
  have h4 := i13_four_cpow_ne_zero ε
  have hsq : (↑(√Real.pi) : ℂ) = Gamma (1 / 2 - ε) * Gamma (1 - ε) /
      (Gamma (1 - 2 * ε) * ((4 : ℝ) : ℂ) ^ ε) := by
    rw [i13_duplication]; field_simp
  have hG2 : Gamma (2 - ε) = (1 - ε) * Gamma (1 - ε) := by
    rw [show 2 - ε = (1 - ε) + 1 by ring, Gamma_add_one _ h1]
  have hG3 : Gamma (3 - ε) = (2 - ε) * (1 - ε) * Gamma (1 - ε) := by
    rw [show 3 - ε = (2 - ε) + 1 by ring, Gamma_add_one _ h2, hG2]; ring
  have hG4 : Gamma (4 - ε) = (3 - ε) * (2 - ε) * (1 - ε) * Gamma (1 - ε) := by
    rw [show 4 - ε = (3 - ε) + 1 by ring, Gamma_add_one _ h3, hG3]; ring
  have hH1 : Gamma (3 / 2 - ε) = (1 / 2 - ε) * Gamma (1 / 2 - ε) := by
    rw [show 3 / 2 - ε = (1 / 2 - ε) + 1 by ring, Gamma_add_one _ hh]
  have hH2 : Gamma (1 / 2 - ε) = (-1 / 2 - ε) * Gamma (-1 / 2 - ε) := by
    rw [show 1 / 2 - ε = (-1 / 2 - ε) + 1 by ring, Gamma_add_one _ hmh]
  have hk : Gamma (-1 / 2 - ε) ≠ 0 := fun h => hΓ (by rw [hH2, h, mul_zero])
  have e0 := i13FPhi_eq_Gamma (a := 1 - ε) (by simp; linarith [le_abs_self ε.re])
  have e1 := i13FPhi_eq_Gamma (a := -ε) (by simp; linarith [le_abs_self ε.re])
  have e2 := i13FPhi_eq_Gamma (a := -1 - ε) (by simp; linarith [le_abs_self ε.re])
  unfold i13FGam at e0 e1 e2
  rw [show 1 - ε + 3 = 4 - ε by ring, show 1 - ε + 1 / 2 = 3 / 2 - ε by ring, hG4, hH1] at e0
  rw [show -ε + 3 = 3 - ε by ring, show -ε + 1 / 2 = 1 / 2 - ε by ring, hG3] at e1
  rw [show -1 - ε + 3 = 2 - ε by ring, show -1 - ε + 1 / 2 = -1 / 2 - ε by ring, hG2] at e2
  rw [i13_Gamma_half, hsq] at e0 e1 e2
  unfold i13Lc0 i13Lc1 i13Lc2 i13Al0 i13Al1 i13Al2 i13G
  rw [e0, e1, e2]
  refine ⟨?_, ?_, ?_⟩
  · generalize Gamma (1 / 2 - ε) = H at hΓ ⊢
    generalize Gamma (1 - ε) = g at hg ⊢
    generalize Gamma (1 - 2 * ε) = L at hΓ2 ⊢
    generalize ((4 : ℝ) : ℂ) ^ ε = F at h4 ⊢
    field_simp
  · generalize Gamma (1 / 2 - ε) = H at hΓ ⊢
    generalize Gamma (1 - ε) = g at hg ⊢
    generalize Gamma (1 - 2 * ε) = L at hΓ2 ⊢
    generalize ((4 : ℝ) : ℂ) ^ ε = F at h4 ⊢
    field_simp
    ring
  · rw [hH2]
    generalize Gamma (-1 / 2 - ε) = H at hk ⊢
    generalize Gamma (1 - ε) = g at hg ⊢
    generalize Gamma (1 - 2 * ε) = L at hΓ2 ⊢
    generalize ((4 : ℝ) : ℂ) ^ ε = F at h4 ⊢
    field_simp
    ring

end QED.ThreeLoopD
