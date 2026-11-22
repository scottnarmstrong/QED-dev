/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C0Val
public import QED.ThreeLoopD.SetDMastersI8R1Xi

/-!
# Set (d), master `I₅`: the constant term `c₀ = 3 - π²/3` of `Rem`

At `ε = 0` the bubble is `1` and `t K₀(t) = f(ξ) = 2 Li₂(ξ) + log ξ log (1 - ξ)`
(`QED.ThreeLoopD.i5Ker_zero_eq`), while the subtraction is `α₀ ∂_ε N(t, 0) = (log t + 2)/t`
(`QED.ThreeLoopD.i5AsymH_zero`, using `G'(0) = 0`). With `t = (1 - ξ)²/ξ`,
`dt/dξ = -(1 - ξ²)/ξ²`, the function (`QED.ThreeLoopD.i5Phi`)

  `Φ(ξ) = 2 (ξ + 1/ξ - 1) Li₂(ξ) + (1 - ξ)²/ξ · log ξ log (1 - ξ) + log² ξ / 2`
    `- (1 + ξ) log ξ + (ξ - 1/ξ) log (1 - ξ)`

has `d Φ(ξ(t))/dt = f(ξ(t))`, `Φ(1) = π²/3`, and `Φ(ξ(t)) - (log² t/2 + 2 log t) → 3` at
infinity. Hence `c₀ = (Φ(ξ(1)) - π²/3) + (3 - Φ(ξ(1))) = 3 - π²/3`
(`QED.ThreeLoopD.i5RemCoeff_zero`).

## Main results

* `QED.ThreeLoopD.i5RemInt1_zero`, `QED.ThreeLoopD.i5RemInt2_zero`.
* `QED.ThreeLoopD.i5RemCoeff_zero : i5RemCoeff 0 = -π²/3 + 3`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-! ### The integrands at `ε = 0` -/

theorem hasDerivAt_i13G_zero : HasDerivAt i13G 0 0 := by
  have h := (differentiableAt_i13G (by norm_num : ‖(0 : ℂ)‖ < 1 / 2)).hasDerivAt
  have e := i13GC_one
  unfold i13GC at e
  rw [i13Dsl_succ, i13Dsl_zero, dslope_same] at e
  rwa [e] at h

theorem i5AsymH_zero {t : ℝ} (ht : 0 < t) :
    i5AsymH 0 t = (((Real.log t + 2) / t : ℝ) : ℂ) := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hf : ∀ a : ℂ, HasDerivAt (fun ε : ℂ => -1 - a * ε) (-a) 0 := fun a => by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul a).const_sub (-1)
  have h2 : HasDerivAt (fun ε : ℂ => 1 - 2 * ε) (-2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul 2).const_sub 1
  have hN : HasDerivAt (i5AsymN t) (((Real.log t + 2) / t : ℝ) : ℂ) 0 := by
    have e := ((((hf 2).const_cpow (c := (t : ℂ)) (Or.inl ht0)).div h2 (by norm_num)).sub
      (hasDerivAt_i13G_zero.mul ((hf 3).const_cpow (c := (t : ℂ)) (Or.inl ht0))))
    convert e using 1
    · funext ε
      simp only [i5AsymN, Pi.sub_apply, Pi.div_apply, Pi.mul_apply]
    rw [i13G_zero, ← Complex.ofReal_log ht.le]
    simp only [mul_zero, sub_zero, Complex.cpow_neg_one]
    push_cast
    field_simp
    ring
  unfold i5AsymH i13Al0
  rw [dslope_same, hN.deriv, i13G_zero]
  simp

theorem i5RemInt1_zero {t : ℝ} (ht : 0 < t) : i5RemInt1 t 0 = ((i5F0 (i13Xi t) : ℝ) : ℂ) := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  unfold i5RemInt1
  rw [i13Bub_zero, sub_zero, Complex.cpow_one, mul_one, i5Ker_zero_eq ht]
  push_cast
  field_simp

theorem i5RemInt2_zero {t : ℝ} (ht : 0 < t) :
    i5RemInt2 t 0 = ((i5F0 (i13Xi t) - (Real.log t + 2) / t : ℝ) : ℂ) := by
  have h := i5RemInt1_zero ht
  unfold i5RemInt1 at h
  unfold i5RemInt2
  rw [h, i5AsymH_zero ht]
  push_cast
  ring

/-! ### Integrability -/

theorem integrableOn_i5Dsl_remInt1 (k : ℕ) :
    IntegrableOn (fun t => i13Dsl (i5RemInt1 t) k 0) (Ioo (0 : ℝ) 1) := by
  obtain ⟨C, hC⟩ := norm_i5RemInt1_le
  exact integrable_i13Dsl_zero (μ := volume.restrict (Ioo (0 : ℝ) 1)) (h := i5RemInt1)
    (R := 1 / 5) (ρ := 1 / 10) (M := fun t => C * t ^ (-(31 / 100 : ℝ))) (by norm_num)
    (by norm_num) ((integrableOn_rpow_Ioo (by norm_num)).const_mul C)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => differentiableOn_i5RemInt1 ht.1)
    (fun ε _ => (measurable_i5RemInt1 ε).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht ε hε => hC t ht ε hε.le) k

theorem integrableOn_i5Dsl_remInt2 (k : ℕ) :
    IntegrableOn (fun t => i13Dsl (i5RemInt2 t) k 0) (Ioi (1 : ℝ)) := by
  obtain ⟨C, hC⟩ := norm_i5RemInt2_le
  have hd : ∀ᵐ t ∂(volume.restrict (Ioi (1 : ℝ))),
      DifferentiableOn ℂ (i5RemInt2 t) (Metric.ball 0 (1 / 5)) :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      differentiableOn_i5RemInt2 (zero_lt_one.trans ht)
  exact integrable_i13Dsl_zero (μ := volume.restrict (Ioi (1 : ℝ))) (h := i5RemInt2)
    (R := 1 / 5) (ρ := 1 / 10) (M := fun t => C * t ^ (-(119 / 100 : ℝ))) (by norm_num)
    (by norm_num) ((integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul C) hd
    (i5_aesm_of_ne (by norm_num) hd fun ε _ h0 => (measurable_i5RemInt2 h0).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ε hε => by
      have h0 : ε ≠ 0 := fun h => by rw [h, norm_zero] at hε; norm_num at hε
      rw [i5RemInt2, i5AsymH_eq h0]
      exact hC t ht ε hε) k

theorem integrableOn_i5F0 : IntegrableOn (fun t => i5F0 (i13Xi t)) (Ioo (0 : ℝ) 1) :=
  (integrableOn_i5Dsl_remInt1 0).re.congr_fun (fun t ht => by
    simp [i5RemInt1_zero ht.1]) measurableSet_Ioo

theorem integrableOn_i5F0_sub :
    IntegrableOn (fun t => i5F0 (i13Xi t) - (Real.log t + 2) / t) (Ioi (1 : ℝ)) :=
  (integrableOn_i5Dsl_remInt2 0).re.congr_fun (fun t (ht : 1 < t) => by
    simp [i5RemInt2_zero (zero_lt_one.trans ht)])
    measurableSet_Ioi

/-! ### The primitive -/

/-- `Φ(ξ)`, with `(1 - ξ) log (1 - ξ)` written through `negMulLog`. -/
noncomputable def i5Phi (ξ : ℝ) : ℝ :=
  2 * (ξ + 1 / ξ - 1) * Li₂ ξ - (1 - ξ) / ξ * Real.log ξ * negMulLog (1 - ξ) +
    Real.log ξ ^ 2 / 2 - (1 + ξ) * Real.log ξ + (1 + ξ) / ξ * negMulLog (1 - ξ)

/-- `A(t) = log² t / 2 + 2 log t`. -/
noncomputable def i5Prim (t : ℝ) : ℝ := Real.log t ^ 2 / 2 + 2 * Real.log t

theorem hasDerivAt_i5Phi {ξ : ℝ} (h0 : 0 < ξ) (h1 : ξ < 1) :
    HasDerivAt i5Phi ((1 - 1 / ξ ^ 2) * i5F0 ξ) ξ := by
  have hξ := h0.ne'
  have h1' : 1 - ξ ≠ 0 := by linarith
  have hx := hasDerivAt_id' ξ
  have hl := Real.hasDerivAt_log hξ
  have hL := hasDerivAt_Li₂' ⟨h0, h1⟩
  have hN := (Real.hasDerivAt_negMulLog h1').comp ξ ((hasDerivAt_id' ξ).const_sub 1)
  have e := (((((((hx.add ((hasDerivAt_const ξ (1 : ℝ)).div hx hξ)).sub_const 1).const_mul
    2).mul hL).sub (((((hasDerivAt_const ξ (1 : ℝ)).sub hx).div hx hξ).mul hl).mul hN)).add
    ((hl.pow 2).div_const 2)).sub (((hasDerivAt_const ξ (1 : ℝ)).add hx).mul hl)).add
    ((((hasDerivAt_const ξ (1 : ℝ)).add hx).div hx hξ).mul hN)
  convert e using 1
  · funext y
    simp only [i5Phi, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply,
      Function.comp_apply]
  · simp only [Function.comp_apply, negMulLog, i5F0]
    norm_num
    field_simp
    ring

theorem hasDerivAt_i5Phi_xi {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => i5Phi (i13Xi t)) (i5F0 (i13Xi t)) t := by
  have hx0 := i13Xi_pos ht.le
  have hx1 := i13Xi_lt_one ht
  refine ((hasDerivAt_i5Phi hx0 hx1).comp t (hasDerivAt_i13Xi ht)).congr_deriv ?_
  set ξ := i13Xi t
  have h0 : ξ ≠ 0 := hx0.ne'
  have h3 : 1 - ξ ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring

theorem hasDerivAt_i5Prim {t : ℝ} (ht : 0 < t) :
    HasDerivAt i5Prim ((Real.log t + 2) / t) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  refine (((hl.pow 2).div_const 2).add (hl.const_mul 2)).congr_deriv ?_
  field_simp
  ring

theorem i5Phi_one : i5Phi 1 = π ^ 2 / 3 := by
  unfold i5Phi
  rw [Li₂_one]
  simp
  ring

theorem continuousOn_i5Phi : ContinuousOn i5Phi (Ioc 0 1) := by
  have hLi : ContinuousOn Li₂ (Ioc 0 1) :=
    continuousOn_Li₂.mono fun x hx => ⟨by linarith [hx.1], hx.2⟩
  have hne : ∀ x ∈ Ioc (0 : ℝ) 1, x ≠ 0 := fun x hx => hx.1.ne'
  unfold i5Phi
  fun_prop (disch := exact hne)

theorem continuousOn_i5Phi_xi : ContinuousOn (fun t => i5Phi (i13Xi t)) (Icc 0 1) :=
  continuousOn_i5Phi.comp continuous_i13Xi.continuousOn fun _ ht =>
    ⟨i13Xi_pos ht.1, i13Xi_le_one ht.1⟩

/-! ### The limit at infinity -/

/-- `Φ - A` in terms of `ξ`. -/
noncomputable def i5D0 (ξ : ℝ) : ℝ :=
  2 * (ξ - 1) * Li₂ ξ + 2 * (Li₂ ξ / ξ) + Real.log ξ * (Real.log (1 - ξ) + ξ) / ξ -
    ξ * Real.log ξ + ξ * Real.log ξ * Real.log (1 - ξ) -
    (1 + ξ) * (1 - ξ) * (Real.log (1 - ξ) / ξ) - 2 * Real.log (1 - ξ) ^ 2 -
    4 * Real.log (1 - ξ)

theorem i5Phi_sub_prim {t : ℝ} (ht : 0 < t) :
    i5Phi (i13Xi t) - i5Prim t = i5D0 (i13Xi t) := by
  have hx0 := i13Xi_pos ht.le
  unfold i5Phi i5Prim i5D0
  rw [i8_log_eq ht]
  simp only [negMulLog]
  set ξ := i13Xi t
  have h0 : ξ ≠ 0 := hx0.ne'
  field_simp
  ring

theorem tendsto_i5D0 : Tendsto i5D0 (𝓝[>] 0) (𝓝 3) := by
  have hxl : Tendsto (fun ξ : ℝ => ξ * Real.log ξ) (𝓝[>] 0) (𝓝 0) := tendsto_mul_log_zero
  have hx : Tendsto (fun ξ : ℝ => ξ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hl1 : Tendsto (fun ξ : ℝ => Real.log (1 - ξ)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun ξ : ℝ => Real.log (1 - ξ)) (𝓝 0) (𝓝 (Real.log (1 - 0))) :=
      ((continuous_const.sub continuous_id).continuousAt.log (by norm_num)).tendsto
    simpa using this.mono_left nhdsWithin_le_nhds
  have hA := ((hx.sub_const 1).const_mul 2).mul tendsto_Li₂_zero_right
  have hE := ((hx.const_add 1).mul (hx.const_sub 1)).mul tendsto_log_one_sub_div_zero'
  have hlim := ((((((hA.add (tendsto_Li₂_div_zero.const_mul 2)).add
    tendsto_log_mul_log_one_sub_add_div_zero).sub hxl).add (hxl.mul hl1)).sub hE).sub
    ((hl1.pow 2).const_mul 2)).sub (hl1.const_mul 4)
  convert hlim using 2
  · rfl
  · norm_num

theorem tendsto_i5Phi_sub_prim :
    Tendsto (fun t => i5Phi (i13Xi t) - i5Prim t) atTop (𝓝 3) :=
  (tendsto_i5D0.comp tendsto_i13Xi_atTop).congr'
    (eventually_atTop.2 ⟨1, fun t ht => (i5Phi_sub_prim (by linarith)).symm⟩)

/-! ### The coefficient -/

theorem integral_i5F0 : ∫ t in Ioo (0 : ℝ) 1, i5F0 (i13Xi t) = i5Phi (i13Xi 1) - π ^ 2 / 3 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one continuousOn_i5Phi_xi
      (fun t ht => hasDerivAt_i5Phi_xi ht.1)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
        (by rw [integrableOn_Ioc_iff_integrableOn_Ioo]; exact integrableOn_i5F0)),
    i13Xi_zero, i5Phi_one]

theorem integral_i5F0_sub :
    ∫ t in Ioi (1 : ℝ), (i5F0 (i13Xi t) - (Real.log t + 2) / t) = 3 - i5Phi (i13Xi 1) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t => i5Phi (i13Xi t) - i5Prim t)
    (((hasDerivAt_i5Phi_xi one_pos).sub (hasDerivAt_i5Prim one_pos)).continuousAt
      |>.continuousWithinAt)
    (fun _ ht => (hasDerivAt_i5Phi_xi (zero_lt_one.trans ht)).sub
      (hasDerivAt_i5Prim (zero_lt_one.trans ht)))
    integrableOn_i5F0_sub tendsto_i5Phi_sub_prim]
  unfold i5Prim
  simp

/-- **The constant term** `c₀ = 3 - π²/3`. -/
theorem i5RemCoeff_zero : i5RemCoeff 0 = -1 / 3 * (π : ℂ) ^ 2 + 3 := by
  unfold i5RemCoeff
  simp only [i13Dsl_zero]
  rw [setIntegral_congr_fun measurableSet_Ioo fun t ht => i5RemInt1_zero ht.1,
    setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) =>
      i5RemInt2_zero (zero_lt_one.trans ht),
    integral_complex_ofReal, integral_complex_ofReal, integral_i5F0, integral_i5F0_sub]
  push_cast
  ring

end QED.ThreeLoopD
