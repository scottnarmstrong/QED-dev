/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8Def
public import QED.ThreeLoopD.SetDMastersI9Strip
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Set (d), master `I₈`: the on-shell angular average

Write `QED.ThreeLoopD.i8Ang` as `A_ε(t) = N_ε J_ε(t)`, `N_ε = 2 Γ(2 - ε) / (Γ(1/2) Γ(3/2 - ε))`
(`QED.ThreeLoopD.i8Nrm`), `J_ε(t) = ∫₀¹ w_ε(z) / (t + 4 z²) dz` with the weight
`w_ε(z) = (1 - z²) ^ (1/2 - ε)` (`QED.ThreeLoopD.i8Wt`). For `‖ε‖ < 1/2`:

* `‖w_ε‖ ≤ 1`, so `‖J_ε(t)‖ ≤ 1/t` (`QED.ThreeLoopD.norm_i8J_le`);
* `ε ↦ A_ε(t)` is holomorphic and `t ↦ A_ε(t)` is measurable;
* the substitution `x = z²` turns the moments `∫ w_ε` and `∫ z² w_ε` into Beta integrals, so
  `N_ε ∫ w_ε = 1` and `4 N_ε ∫ z² w_ε = κ = 2/(2 - ε)` (`QED.ThreeLoopD.i8Nrm_mul_Mom0`,
  `QED.ThreeLoopD.i8Nrm_mul_Mom2`);
* with `1/(t + 4z²) = 1/t - 4z²/t² + 16 z⁴/(t² (t + 4z²))` this gives the large-`t` expansion
  `A_ε(t) = 1/t - κ/t² + 16 N_ε E_ε(t)/t²`, `‖E_ε(t)‖ ≤ 1/t` (`QED.ThreeLoopD.i8Ang_asym`).

## Main results

* `QED.ThreeLoopD.norm_i8J_le`, `QED.ThreeLoopD.differentiableAt_i8Ang`,
  `QED.ThreeLoopD.measurable_i8Ang`.
* `QED.ThreeLoopD.i8Nrm_mul_Mom0`, `QED.ThreeLoopD.i8Nrm_mul_Mom2`, `QED.ThreeLoopD.i8Ang_asym`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric

namespace QED.ThreeLoopD

/-- The normalization `N_ε = 2 Γ(2 - ε) / (Γ(1/2) Γ(3/2 - ε))` of the angular average. -/
noncomputable def i8Nrm (ε : ℂ) : ℂ := 2 * Gamma (2 - ε) / (Gamma (1 / 2) * Gamma (3 / 2 - ε))

/-- The angular weight `w_ε(z) = (1 - z²) ^ (1/2 - ε)`. -/
noncomputable def i8Wt (ε : ℂ) (z : ℝ) : ℂ := ((1 - z ^ 2 : ℝ) : ℂ) ^ (1 / 2 - ε)

/-- `J_ε(t) = ∫₀¹ w_ε(z) / (t + 4 z²) dz`. -/
noncomputable def i8J (ε : ℂ) (t : ℝ) : ℂ :=
  ∫ z in Ioo (0 : ℝ) 1, i8Wt ε z / ((t + 4 * z ^ 2 : ℝ) : ℂ)

/-- The moment `∫₀¹ w_ε(z) dz`. -/
noncomputable def i8Mom0 (ε : ℂ) : ℂ := ∫ z in Ioo (0 : ℝ) 1, i8Wt ε z

/-- The moment `∫₀¹ z² w_ε(z) dz`. -/
noncomputable def i8Mom2 (ε : ℂ) : ℂ := ∫ z in Ioo (0 : ℝ) 1, i8Wt ε z * ((z ^ 2 : ℝ) : ℂ)

/-- The large-`t` remainder `E_ε(t) = ∫₀¹ z⁴ w_ε(z) / (t + 4 z²) dz`. -/
noncomputable def i8AngE (ε : ℂ) (t : ℝ) : ℂ :=
  ∫ z in Ioo (0 : ℝ) 1, i8Wt ε z * ((z ^ 4 / (t + 4 * z ^ 2) : ℝ) : ℂ)

theorem i8Ang_eq (ε : ℂ) (t : ℝ) : i8Ang ε t = i8Nrm ε * i8J ε t := rfl

/-! ### The weight -/

theorem i8_one_sub_sq_pos {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) : 0 < 1 - z ^ 2 := by
  nlinarith [hz.1, hz.2]

theorem norm_i8Wt_le {ε : ℂ} (hε : ε.re ≤ 1 / 2) {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    ‖i8Wt ε z‖ ≤ 1 := by
  unfold i8Wt
  rw [norm_cpow_eq_rpow_re_of_pos (i8_one_sub_sq_pos hz)]
  refine Real.rpow_le_one (i8_one_sub_sq_pos hz).le (by nlinarith [hz.1]) ?_
  rw [sub_re]; norm_num; linarith

theorem measurable_i8Wt (ε : ℂ) : Measurable (i8Wt ε) := by
  unfold i8Wt; fun_prop

/-- Bounded measurable multiples of the weight are integrable. -/
theorem integrableOn_i8Wt_mul {ε : ℂ} (hε : ε.re ≤ 1 / 2) {g : ℝ → ℂ} (hg : Measurable g)
    {C : ℝ} (hC : ∀ z ∈ Ioo (0 : ℝ) 1, ‖g z‖ ≤ C) :
    IntegrableOn (fun z => i8Wt ε z * g z) (Ioo 0 1) := by
  refine Integrable.mono' (integrable_const C)
    ((measurable_i8Wt ε).mul hg).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioo fun z hz => ?_)
  rw [norm_mul]
  calc ‖i8Wt ε z‖ * ‖g z‖ ≤ 1 * C :=
        mul_le_mul (norm_i8Wt_le hε hz) (hC z hz) (norm_nonneg _) zero_le_one
    _ = C := one_mul C

/-! ### `J` -/

theorem i8_den_pos {t : ℝ} (ht : 0 < t) (z : ℝ) : 0 < t + 4 * z ^ 2 := by positivity

theorem norm_i8_inv_den_le {t : ℝ} (ht : 0 < t) (z : ℝ) :
    ‖(((t + 4 * z ^ 2 : ℝ) : ℂ))⁻¹‖ ≤ t⁻¹ := by
  rw [norm_inv, norm_real, Real.norm_eq_abs, abs_of_pos (i8_den_pos ht z)]
  exact inv_anti₀ ht (by nlinarith [sq_nonneg z])

theorem integrableOn_i8J {ε : ℂ} (hε : ε.re ≤ 1 / 2) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun z => i8Wt ε z / ((t + 4 * z ^ 2 : ℝ) : ℂ)) (Ioo 0 1) := by
  simp_rw [div_eq_mul_inv]
  exact integrableOn_i8Wt_mul hε (by fun_prop) fun z _ => norm_i8_inv_den_le ht z

/-- `‖J_ε(t)‖ ≤ 1/t`. -/
theorem norm_i8J_le {ε : ℂ} (hε : ε.re ≤ 1 / 2) {t : ℝ} (ht : 0 < t) : ‖i8J ε t‖ ≤ t⁻¹ := by
  unfold i8J
  have := norm_setIntegral_le_of_norm_le_const (s := Ioo (0 : ℝ) 1)
    (measure_Ioo_lt_top (μ := volume) (a := (0 : ℝ)) (b := 1)) (C := t⁻¹)
    (f := fun z => i8Wt ε z / ((t + 4 * z ^ 2 : ℝ) : ℂ)) (fun z hz => by
      rw [div_eq_mul_inv, norm_mul]
      calc ‖i8Wt ε z‖ * ‖(((t + 4 * z ^ 2 : ℝ) : ℂ))⁻¹‖ ≤ 1 * t⁻¹ :=
            mul_le_mul (norm_i8Wt_le hε hz) (norm_i8_inv_den_le ht z) (norm_nonneg _) zero_le_one
        _ = t⁻¹ := one_mul _)
  simpa [Real.volume_real_Ioo_of_le zero_le_one] using this

theorem measurable_i8J (ε : ℂ) : Measurable fun t => i8J ε t := by
  unfold i8J i8Wt
  have : StronglyMeasurable (fun p : ℝ × ℝ =>
      ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ (1 / 2 - ε) / ((p.1 + 4 * p.2 ^ 2 : ℝ) : ℂ)) :=
    (by fun_prop : Measurable fun p : ℝ × ℝ =>
      ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ (1 / 2 - ε) / ((p.1 + 4 * p.2 ^ 2 : ℝ) : ℂ)).stronglyMeasurable
  exact (this.integral_prod_right' (ν := volume.restrict (Ioo (0 : ℝ) 1))).measurable

theorem differentiableAt_i8J {ε₀ : ℂ} (h0 : ‖ε₀‖ < 1 / 4) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℂ (fun ε => i8J ε t) ε₀ := by
  have hre : ∀ ε ∈ ball ε₀ (1 / 4), ε.re ≤ 1 / 2 := fun ε hε => by
    rw [mem_ball, dist_eq_norm] at hε
    have := norm_sub_norm_le ε ε₀
    linarith [re_le_norm ε]
  unfold i8J
  refine QED.DimReg.differentiableAt_integral_of_holomorphic (by norm_num : (0 : ℝ) < 1 / 4)
    (b := fun _ => t⁻¹) (integrable_const _)
    (fun ε hε => (integrableOn_i8J (hre ε hε) ht).aestronglyMeasurable) ?_ ?_
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun z hz ε hε => ?_
    rw [div_eq_mul_inv, norm_mul]
    calc ‖i8Wt ε z‖ * ‖(((t + 4 * z ^ 2 : ℝ) : ℂ))⁻¹‖ ≤ 1 * t⁻¹ :=
          mul_le_mul (norm_i8Wt_le (hre ε hε) hz) (norm_i8_inv_den_le ht z) (norm_nonneg _)
            zero_le_one
      _ = t⁻¹ := one_mul _
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun z hz => ?_
    unfold i8Wt
    exact ((Differentiable.const_cpow (by fun_prop)
      (Or.inl (ofReal_ne_zero.mpr (i8_one_sub_sq_pos hz).ne'))).div_const _).differentiableOn

/-! ### The normalization -/

theorem i8_Gamma_facts {ε : ℂ} (hε : ‖ε‖ < 1 / 2) :
    DifferentiableAt ℂ (fun ε => Gamma (2 - ε)) ε ∧
      DifferentiableAt ℂ (fun ε => Gamma (3 / 2 - ε)) ε ∧
      Gamma (2 - ε) ≠ 0 ∧ Gamma (3 / 2 - ε) ≠ 0 ∧ Gamma (1 / 2) ≠ 0 := by
  have hre : ε.re < 1 / 2 := (re_le_norm ε).trans_lt hε
  have hG : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ Gamma s := fun s hs =>
    differentiableAt_Gamma _ fun m hm => by
      have := congr_arg re hm; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have h2 : 0 < (2 - ε).re := by simp; linarith
  have h3 : 0 < (3 / 2 - ε).re := by
    rw [sub_re]; norm_num; linarith
  have h1 : 0 < ((1 : ℂ) / 2).re := by norm_num
  exact ⟨(hG _ h2).comp ε (by fun_prop), (hG _ h3).comp ε (by fun_prop),
    Gamma_ne_zero_of_re_pos h2, Gamma_ne_zero_of_re_pos h3, Gamma_ne_zero_of_re_pos h1⟩

theorem differentiableAt_i8Nrm {ε : ℂ} (hε : ‖ε‖ < 1 / 2) : DifferentiableAt ℂ i8Nrm ε := by
  obtain ⟨d2, d3, -, n3, n1⟩ := i8_Gamma_facts hε
  unfold i8Nrm
  exact (d2.const_mul 2).div (d3.const_mul _) (mul_ne_zero n1 n3)

theorem i8Nrm_bound : ∃ C, ∀ ε : ℂ, ‖ε‖ ≤ 1 / 10 → ‖i8Nrm ε‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (1 / 10)).exists_bound_of_continuousOn
    fun ε hε => (differentiableAt_i8Nrm (by
      rw [mem_closedBall, dist_zero_right] at hε; linarith)).continuousAt.continuousWithinAt
  exact ⟨C, fun ε hε => hC ε (by rw [mem_closedBall, dist_zero_right]; exact hε)⟩

theorem differentiableAt_i8Ang {ε : ℂ} (hε : ‖ε‖ < 1 / 4) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℂ (fun ε => i8Ang ε t) ε :=
  (differentiableAt_i8Nrm (by linarith)).mul (differentiableAt_i8J hε ht)

theorem measurable_i8Ang (ε : ℂ) : Measurable fun t => i8Ang ε t :=
  measurable_const.mul (measurable_i8J ε)

theorem norm_i8Ang_le {C : ℝ} (hC : ∀ ε : ℂ, ‖ε‖ ≤ 1 / 10 → ‖i8Nrm ε‖ ≤ C) {ε : ℂ}
    (hε : ‖ε‖ ≤ 1 / 10) {t : ℝ} (ht : 0 < t) : ‖i8Ang ε t‖ ≤ C * t⁻¹ := by
  rw [i8Ang_eq, norm_mul]
  exact mul_le_mul (hC ε hε) (norm_i8J_le (by linarith [re_le_norm ε]) ht) (norm_nonneg _)
    ((norm_nonneg _).trans (hC ε hε))

/-! ### The moments -/

/-- **The substitution** `x = z²`: `∫₀¹ G(z²) dz = ∫₀¹ G(x) / (2 √x) dx`. -/
theorem i8_integral_sq_subst (G : ℝ → ℂ) :
    ∫ z in Ioo (0 : ℝ) 1, G (z ^ 2) = ∫ x in Ioo (0 : ℝ) 1, G x / (2 * (√x : ℂ)) := by
  have him : (fun z : ℝ => z ^ 2) '' Ioo 0 1 = Ioo 0 1 := by
    ext x
    constructor
    · rintro ⟨z, ⟨h0, h1⟩, rfl⟩
      constructor <;> nlinarith
    · rintro ⟨h0, h1⟩
      refine ⟨√x, ⟨Real.sqrt_pos.mpr h0, ?_⟩, Real.sq_sqrt h0.le⟩
      rw [Real.sqrt_lt' one_pos]; linarith
  have hcov := integral_image_eq_integral_abs_deriv_smul (f := fun z : ℝ => z ^ 2)
    (f' := fun z => 2 * z) (s := Ioo 0 1) measurableSet_Ioo
    (fun z _ => by
      simpa using (hasDerivAt_pow 2 z).hasDerivWithinAt)
    (fun x hx y hy hxy => by
      simp only at hxy
      nlinarith [hx.1, hy.1])
    (fun x => G x / (2 * (√x : ℂ)))
  rw [him] at hcov
  rw [hcov]
  refine setIntegral_congr_fun measurableSet_Ioo fun z hz => ?_
  have hz0 := hz.1
  rw [Real.sqrt_sq hz0.le, abs_of_pos (by linarith), real_smul]
  have : (z : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz0.ne'
  push_cast
  field_simp

theorem i8_cpow_half_sub_one {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ ((1 : ℂ) / 2 - 1) = 1 / (√x : ℂ) := by
  rw [Real.sqrt_eq_rpow, ofReal_cpow hx.le, show (1 : ℂ) / 2 - 1 = -((1 / 2 : ℝ) : ℂ) by
    push_cast; ring, cpow_neg]
  exact (one_div _).symm

theorem i8_cpow_three_half_sub_one {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ ((3 : ℂ) / 2 - 1) = (√x : ℂ) := by
  rw [Real.sqrt_eq_rpow, ofReal_cpow hx.le, show (3 : ℂ) / 2 - 1 = ((1 / 2 : ℝ) : ℂ) by
    push_cast; ring]

theorem i8Mom0_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 2) :
    i8Mom0 ε = Gamma (1 / 2) * Gamma (3 / 2 - ε) / Gamma (2 - ε) / 2 := by
  have hre : ε.re < 1 / 2 := (re_le_norm ε).trans_lt hε
  have hv : 0 < (3 / 2 - ε).re := by
    rw [sub_re]; norm_num; linarith
  have hB := i9_integral_beta (u := 1 / 2) (v := 3 / 2 - ε) (by norm_num) hv
  unfold i9Beta at hB
  rw [show (1 : ℂ) / 2 + (3 / 2 - ε) = 2 - ε by ring] at hB
  unfold i8Mom0 i8Wt
  have := i8_integral_sq_subst (fun x => ((1 - x : ℝ) : ℂ) ^ (1 / 2 - ε))
  rw [this, ← hB, ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  rw [i8_cpow_half_sub_one hx.1, show (3 : ℂ) / 2 - ε - 1 = 1 / 2 - ε by ring]
  have : (√x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx.1).ne'
  field_simp

theorem i8Mom2_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 2) :
    i8Mom2 ε = Gamma (3 / 2) * Gamma (3 / 2 - ε) / Gamma (3 - ε) / 2 := by
  have hre : ε.re < 1 / 2 := (re_le_norm ε).trans_lt hε
  have hv : 0 < (3 / 2 - ε).re := by
    rw [sub_re]; norm_num; linarith
  have hB := i9_integral_beta (u := 3 / 2) (v := 3 / 2 - ε) (by norm_num) hv
  unfold i9Beta at hB
  rw [show (3 : ℂ) / 2 + (3 / 2 - ε) = 3 - ε by ring] at hB
  unfold i8Mom2 i8Wt
  have := i8_integral_sq_subst (fun x => ((1 - x : ℝ) : ℂ) ^ (1 / 2 - ε) * (x : ℂ))
  rw [this, ← hB, ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  rw [i8_cpow_three_half_sub_one hx.1, show (3 : ℂ) / 2 - ε - 1 = 1 / 2 - ε by ring]
  have hs : (√x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx.1).ne'
  have hxx : (x : ℂ) = (√x : ℂ) * (√x : ℂ) := by
    rw [← ofReal_mul, Real.mul_self_sqrt hx.1.le]
  rw [hxx]
  field_simp

/-- `N_ε ∫₀¹ w_ε = 1`. -/
theorem i8Nrm_mul_Mom0 {ε : ℂ} (hε : ‖ε‖ < 1 / 2) : i8Nrm ε * i8Mom0 ε = 1 := by
  obtain ⟨-, -, n2, n3, n1⟩ := i8_Gamma_facts hε
  rw [i8Mom0_eq hε, i8Nrm]
  generalize Gamma (3 / 2 - ε) = c at n3 ⊢
  generalize Gamma (2 - ε) = d at n2 ⊢
  generalize Gamma (1 / 2) = e at n1 ⊢
  field_simp

/-- `4 N_ε ∫₀¹ z² w_ε = κ = 2/(2 - ε)`. -/
theorem i8Nrm_mul_Mom2 {ε : ℂ} (hε : ‖ε‖ < 1 / 2) : 4 * i8Nrm ε * i8Mom2 ε = i8Kap ε := by
  obtain ⟨-, -, n2, n3, n1⟩ := i8_Gamma_facts hε
  have h2 : (2 : ℂ) - ε ≠ 0 := by
    intro h; have := congr_arg re h; simp at this; linarith [(re_le_norm ε)]
  have g32 : Gamma (3 / 2) = 1 / 2 * Gamma (1 / 2) := by
    rw [show (3 : ℂ) / 2 = 1 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num)]
  have g3 : Gamma (3 - ε) = (2 - ε) * Gamma (2 - ε) := by
    rw [show (3 : ℂ) - ε = (2 - ε) + 1 by ring, Gamma_add_one _ h2]
  rw [i8Mom2_eq hε, i8Nrm, i8Kap, g32, g3]
  generalize Gamma (3 / 2 - ε) = c at n3 ⊢
  generalize Gamma (2 - ε) = d at n2 ⊢
  generalize Gamma (1 / 2) = e at n1 ⊢
  field_simp
  ring

/-! ### The large-`t` expansion -/

theorem i8_partial_frac {t : ℝ} (ht : 0 < t) (z : ℝ) :
    1 / (t + 4 * z ^ 2) = 1 / t - 4 * z ^ 2 / t ^ 2 + 16 * (z ^ 4 / (t + 4 * z ^ 2)) / t ^ 2 := by
  have := i8_den_pos ht z
  field_simp
  ring

theorem norm_i8AngE_le {ε : ℂ} (hε : ε.re ≤ 1 / 2) {t : ℝ} (ht : 0 < t) : ‖i8AngE ε t‖ ≤ t⁻¹ := by
  have hb : ∀ z ∈ Ioo (0 : ℝ) 1, ‖((z ^ 4 / (t + 4 * z ^ 2) : ℝ) : ℂ)‖ ≤ t⁻¹ := fun z hz => by
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (by have := i8_den_pos ht z; positivity),
      div_eq_mul_inv]
    have h4 : z ^ 4 ≤ 1 := pow_le_one₀ hz.1.le hz.2.le
    have hi := norm_i8_inv_den_le ht z
    rw [norm_inv, norm_real, Real.norm_eq_abs, abs_of_pos (i8_den_pos ht z)] at hi
    calc z ^ 4 * (t + 4 * z ^ 2)⁻¹ ≤ 1 * t⁻¹ :=
          mul_le_mul h4 hi (by have := i8_den_pos ht z; positivity) zero_le_one
      _ = t⁻¹ := one_mul _
  unfold i8AngE
  have := norm_setIntegral_le_of_norm_le_const (s := Ioo (0 : ℝ) 1)
    (measure_Ioo_lt_top (μ := volume) (a := (0 : ℝ)) (b := 1)) (C := t⁻¹)
    (f := fun z => i8Wt ε z * ((z ^ 4 / (t + 4 * z ^ 2) : ℝ) : ℂ)) (fun z hz => by
      rw [norm_mul]
      calc _ ≤ 1 * t⁻¹ := mul_le_mul (norm_i8Wt_le hε hz) (hb z hz) (norm_nonneg _) zero_le_one
        _ = t⁻¹ := one_mul _)
  simpa [Real.volume_real_Ioo_of_le zero_le_one] using this

/-- `J_ε(t) = I/t - 4K/t² + 16 E_ε(t)/t²`. -/
theorem i8J_eq {ε : ℂ} (hε : ε.re ≤ 1 / 2) {t : ℝ} (ht : 0 < t) :
    i8J ε t = i8Mom0 ε / t - 4 * i8Mom2 ε / t ^ 2 + 16 * i8AngE ε t / t ^ 2 := by
  have hI : IntegrableOn (fun z => i8Wt ε z) (Ioo 0 1) := by
    simpa using integrableOn_i8Wt_mul hε (g := fun _ => (1 : ℂ)) measurable_const
      (C := 1) fun _ _ => by simp
  have hK : IntegrableOn (fun z => i8Wt ε z * ((z ^ 2 : ℝ) : ℂ)) (Ioo 0 1) :=
    integrableOn_i8Wt_mul hε (by fun_prop) (C := 1) fun z hz => by
      rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_one₀ hz.1.le hz.2.le
  have hE : IntegrableOn (fun z => i8Wt ε z * ((z ^ 4 / (t + 4 * z ^ 2) : ℝ) : ℂ))
      (Ioo 0 1) :=
    integrableOn_i8Wt_mul hε (by fun_prop) (C := t⁻¹) fun z hz => by
      rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (by have := i8_den_pos ht z; positivity),
        div_eq_mul_inv]
      have h4 : z ^ 4 ≤ 1 := pow_le_one₀ hz.1.le hz.2.le
      have := i8_den_pos ht z
      calc z ^ 4 * (t + 4 * z ^ 2)⁻¹ ≤ 1 * t⁻¹ :=
            mul_le_mul h4 (inv_anti₀ ht (by nlinarith [sq_nonneg z])) (by positivity)
              zero_le_one
        _ = t⁻¹ := one_mul _
  have hpt : ∀ z ∈ Ioo (0 : ℝ) 1, i8Wt ε z / ((t + 4 * z ^ 2 : ℝ) : ℂ) =
      i8Wt ε z / t - 4 * (i8Wt ε z * ((z ^ 2 : ℝ) : ℂ)) / t ^ 2 +
        16 * (i8Wt ε z * ((z ^ 4 / (t + 4 * z ^ 2) : ℝ) : ℂ)) / t ^ 2 := fun z _ => by
    have h := congr_arg (fun r : ℝ => (r : ℂ)) (i8_partial_frac ht z)
    push_cast at h
    have hd : ((t : ℂ) + 4 * (z : ℂ) ^ 2) ≠ 0 := by
      rw [show ((t : ℂ) + 4 * (z : ℂ) ^ 2) = ((t + 4 * z ^ 2 : ℝ) : ℂ) by push_cast; ring]
      exact ofReal_ne_zero.mpr (i8_den_pos ht z).ne'
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    push_cast
    rw [div_eq_mul_one_div, h]
    field_simp
  unfold i8J
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_add (by
      exact (hI.div_const _).sub ((hK.const_mul 4).div_const _)) ((hE.const_mul 16).div_const _),
    integral_sub (hI.div_const _) ((hK.const_mul 4).div_const _), integral_div, integral_div,
    integral_div, integral_const_mul, integral_const_mul]
  rfl

/-- **The large-`t` expansion of the angular average**:
`A_ε(t) = 1/t - κ/t² + 16 N_ε E_ε(t)/t²`. -/
theorem i8Ang_asym {ε : ℂ} (hε : ‖ε‖ < 1 / 2) {t : ℝ} (ht : 0 < t) :
    i8Ang ε t = 1 / t - i8Kap ε / t ^ 2 + 16 * i8Nrm ε * i8AngE ε t / t ^ 2 := by
  rw [i8Ang_eq, i8J_eq (by linarith [re_le_norm ε]) ht, ← i8Nrm_mul_Mom2 hε,
    ← i8Nrm_mul_Mom0 hε]
  ring

end QED.ThreeLoopD
