/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13RXi
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Set (d), master `I₁₃`: the coefficient `c₁ = -9/4` of `Rem`

With `λ = log t`, `β₁(t) = 2 + log ξ (1 + ξ)/(1 - ξ)` (`QED.ThreeLoopD.i13_integral_log`), the
first Taylor coefficients of the integrands of `Rem` are

  `p₁(t) = -t λ + 2 t β₁(t)` on `(0, 1)`, `p₁(t) - a₁(t)` on `(1, ∞)`,
  `a₁(t) = t (4 - 3λ) - 4 - 4λ + (4λ - 2)/t`.

They have the primitives `F(t) = Φ(ξ(t)) - t² λ/2 + t²/4` and
`A(t) = 11t²/4 - (3t²/2 + 4t) λ + 2λ² - 2λ`, with

  `Φ(ξ) = 5ξ²/2 - 8ξ + 2 log² ξ - 8/ξ - (ξ² - ξ⁻²) log ξ + 5/(2ξ²)`.

So `c₁ = (F(1) - F(0)) + (lim_{t→∞} (F - A) - F(1) + A(1)) = 11 - 16 + 11/4 = -9/4`: the value
`F(1)` at the golden-ratio point `ξ(1)` cancels. The limit is `-16`: in terms of `ξ`,
`F - A = -16 + 2 (log (1 - ξ) + ξ + ξ²/2)/ξ² + o(1)`.

## Main results

* `QED.ThreeLoopD.i13RemCoeff_one : i13RemCoeff 1 = -9/4`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real

namespace QED.ThreeLoopD

/-! ### Integrability of the pointwise coefficients -/

theorem integrable_i13Dsl_zero {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : α → ℂ → ℂ} {R ρ : ℝ} {M : α → ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hMi : Integrable M μ)
    (hd : ∀ᵐ t ∂μ, DifferentiableOn ℂ (h t) (Metric.ball 0 R))
    (hm : ∀ ε ∈ Metric.ball (0 : ℂ) R, AEStronglyMeasurable (fun t => h t ε) μ)
    (hb : ∀ᵐ t ∂μ, ∀ ε : ℂ, ‖ε‖ = ρ → ‖h t ε‖ ≤ M t) (k : ℕ) :
    Integrable (fun t => i13Dsl (h t) k 0) μ := by
  have hR : 0 < R := hρ.trans hρR
  refine Integrable.mono' ((hMi.const_mul (2 ^ k)).div_const (ρ ^ k))
    (aestronglyMeasurable_i13Dsl hR hd hm k 0 (Metric.mem_ball_self hR)) ?_
  filter_upwards [hd, hb] with t ht htb
  exact norm_i13Dsl_le hρ hρR ht htb k 0 (by simp [hρ.le])

theorem integrableOn_i13Dsl_remInt1 (k : ℕ) :
    IntegrableOn (fun t => i13Dsl (i13RemInt1 t) k 0) (Ioo (0 : ℝ) 1) :=
  integrable_i13Dsl_zero (μ := volume.restrict (Ioo (0 : ℝ) 1)) (h := i13RemInt1) (R := 1 / 5)
    (ρ := 1 / 10) (M := fun _ => 4) (by norm_num) (by norm_num) (integrable_const _)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht =>
      (differentiable_i13RemInt1 ht.1).differentiableOn)
    (fun ε _ => (measurable_i13RemInt1 ε).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht ε hε =>
      norm_i13RemInt1_le ht hε.le) k

theorem integrableOn_i13Dsl_remInt2 (k : ℕ) :
    IntegrableOn (fun t => i13Dsl (i13RemInt2 t) k 0) (Ioi (1 : ℝ)) := by
  obtain ⟨K, hK⟩ := norm_i13RemInt2_le
  exact integrable_i13Dsl_zero (μ := volume.restrict (Ioi (1 : ℝ))) (h := i13RemInt2)
    (R := 1 / 5) (ρ := 1 / 10) (M := fun t => K * t ^ ((3 : ℝ) / 10 - 2))
    (by norm_num) (by norm_num)
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul K)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      differentiableOn_i13RemInt2 (zero_lt_one.trans ht))
    (fun ε _ => (measurable_i13RemInt2 ε).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ε hε =>
      hK ε hε.le t (le_of_lt ht)) k

/-! ### The first coefficients as real functions -/

/-- `β₁(t) = 2 + log ξ (1 + ξ)/(1 - ξ)`. -/
noncomputable def i13Be1r (t : ℝ) : ℝ :=
  2 + Real.log (i13Xi t) * (1 + i13Xi t) / (1 - i13Xi t)

/-- `p₁(t) = -t log t + 2 t β₁(t)`. -/
noncomputable def i13P1 (t : ℝ) : ℝ := -(t * Real.log t) + 2 * t * i13Be1r t

/-- `a₁(t) = t (4 - 3 log t) - 4 - 4 log t + (4 log t - 2)/t`. -/
noncomputable def i13A1r (t : ℝ) : ℝ :=
  t * (4 - 3 * Real.log t) - 4 - 4 * Real.log t + (4 * Real.log t - 2) / t

theorem i13BubC_one {t : ℝ} (ht : 0 < t) : i13BubC t 1 = (i13Be1r t : ℂ) := by
  unfold i13BubC i13Be1r
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  rw [integral_complex_ofReal, integral_neg, i13_integral_log ht]
  push_cast
  ring

theorem i13Dsl_remInt1_one {t : ℝ} (ht : 0 < t) :
    i13Dsl (i13RemInt1 t) 1 0 = (i13P1 t : ℂ) := by
  rw [i13Dsl_remInt1 ht, i13R1C_one, i13BubC_one ht]
  unfold i13P1
  push_cast
  ring

theorem i13Dsl_remInt2_one {t : ℝ} (ht : 0 < t) :
    i13Dsl (i13RemInt2 t) 1 0 = ((i13P1 t - i13A1r t : ℝ) : ℂ) := by
  rw [i13Dsl_remInt2 ht, i13R1C_one, i13BubC_one ht, i13AsymC_one ht]
  unfold i13P1 i13A1r
  push_cast
  ring

/-! ### The primitives -/

/-- `Φ(ξ) = 5ξ²/2 - 8ξ + 2 log² ξ - 8/ξ - (ξ² - ξ⁻²) log ξ + 5/(2ξ²)`. -/
noncomputable def i13Phi1 (ξ : ℝ) : ℝ :=
  5 * ξ ^ 2 / 2 - 8 * ξ + 2 * Real.log ξ ^ 2 - 8 / ξ - (ξ ^ 2 - 1 / ξ ^ 2) * Real.log ξ +
    5 / (2 * ξ ^ 2)

/-- `F(t) = Φ(ξ(t)) - t² log t/2 + t²/4`. -/
noncomputable def i13F1 (t : ℝ) : ℝ :=
  i13Phi1 (i13Xi t) - t ^ 2 * Real.log t / 2 + t ^ 2 / 4

/-- `A(t) = 11t²/4 - (3t²/2 + 4t) log t + 2 log² t - 2 log t`. -/
noncomputable def i13Prim1 (t : ℝ) : ℝ :=
  11 * t ^ 2 / 4 - (3 * t ^ 2 / 2 + 4 * t) * Real.log t + 2 * Real.log t ^ 2 - 2 * Real.log t

theorem hasDerivAt_i13Phi1 {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt i13Phi1 (-2 * (1 - ξ) ^ 2 * (1 + ξ) *
      (ξ * Real.log ξ - 2 * ξ + Real.log ξ + 2) / ξ ^ 3) ξ := by
  have h0 := hξ.ne'
  have hl := Real.hasDerivAt_log h0
  have hx := hasDerivAt_id' ξ
  have e := ((((((hx.pow 2).div_const 2).const_mul 5).sub (hx.const_mul 8)).add
    ((hl.pow 2).const_mul 2)).sub ((hasDerivAt_const ξ (8 : ℝ)).div hx h0)).sub
    (((hx.pow 2).sub ((hasDerivAt_const ξ (1 : ℝ)).div (hx.pow 2) (pow_ne_zero 2 h0))).mul hl)
  have e' := e.add ((hasDerivAt_const ξ (5 : ℝ)).div ((hx.pow 2).const_mul 2)
    (mul_ne_zero two_ne_zero (pow_ne_zero 2 h0)))
  convert e' using 1
  · funext y
    simp only [i13Phi1, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
    ring
  · simp only [Pi.pow_apply]
    norm_num
    field_simp
    ring

theorem hasDerivAt_i13F1 {t : ℝ} (ht : 0 < t) : HasDerivAt i13F1 (i13P1 t) t := by
  have hx0 := i13Xi_pos ht.le
  have hx1 := i13Xi_lt_one ht
  have hT := i13Xi_t ht.le
  have e := ((hasDerivAt_i13Phi1 hx0).comp t (hasDerivAt_i13Xi ht)).sub
    ((((hasDerivAt_id' t).pow 2).mul (Real.hasDerivAt_log ht.ne')).div_const 2) |>.add
    (((hasDerivAt_id' t).pow 2).div_const 4)
  have hv : -2 * (1 - i13Xi t) ^ 2 * (1 + i13Xi t) * (i13Xi t * Real.log (i13Xi t) -
      2 * i13Xi t + Real.log (i13Xi t) + 2) / i13Xi t ^ 3 *
      (-i13Xi t ^ 2 / (1 - i13Xi t ^ 2)) = 2 * t * i13Be1r t := by
    unfold i13Be1r
    set ξ := i13Xi t
    have h0 : ξ ≠ 0 := hx0.ne'
    have h1 : 1 - ξ ≠ 0 := by linarith
    have h2 : 1 + ξ ≠ 0 := by linarith
    have h3 : 1 - ξ ^ 2 ≠ 0 := by nlinarith
    rw [hT]
    field_simp
    ring
  convert e using 1
  · funext y
    simp only [i13F1, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply,
      Function.comp_apply]
  · rw [hv]
    unfold i13P1
    simp only [Pi.pow_apply]
    norm_num
    field_simp
    ring

theorem hasDerivAt_i13Prim1 {t : ℝ} (ht : 0 < t) : HasDerivAt i13Prim1 (i13A1r t) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  have hx := hasDerivAt_id' t
  have e := (((((hx.pow 2).const_mul 11).div_const 4).sub
    (((((hx.pow 2).const_mul 3).div_const 2).add (hx.const_mul 4)).mul hl)).add
    ((hl.pow 2).const_mul 2)).sub (hl.const_mul 2)
  convert e using 1
  · funext y
    simp only [i13Prim1, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
  · unfold i13A1r
    simp only [Pi.pow_apply]
    norm_num
    field_simp
    ring

theorem i13F1_zero : i13F1 0 = -11 := by
  unfold i13F1 i13Phi1
  rw [i13Xi_zero]
  norm_num

theorem continuous_mul_sq_log : Continuous fun t : ℝ => t ^ 2 * Real.log t := by
  have : (fun t : ℝ => t ^ 2 * Real.log t) = fun t => t * (t * Real.log t) := by
    funext t; ring
  rw [this]
  exact continuous_id.mul Real.continuous_mul_log

theorem continuousOn_i13F1 : ContinuousOn i13F1 (Ici 0) := by
  have hX : ContinuousOn (fun t => i13Phi1 (i13Xi t)) (Ici 0) := by
    intro t ht
    have h0 := (i13Xi_pos ht).ne'
    have hc := continuous_i13Xi.continuousAt (x := t)
    unfold i13Phi1
    refine ContinuousAt.continuousWithinAt ?_
    have hl : ContinuousAt (fun t => Real.log (i13Xi t)) t := hc.log h0
    exact ((((((hc.pow 2).const_mul 5).div_const 2).sub (hc.const_mul 8)).add
      ((hl.pow 2).const_mul 2)).sub (continuousAt_const.div hc h0)).sub
      (((hc.pow 2).sub (continuousAt_const.div (hc.pow 2) (pow_ne_zero 2 h0))).mul hl) |>.add
      (continuousAt_const.div ((hc.pow 2).const_mul 2) (by positivity))
  unfold i13F1
  exact (hX.sub (continuous_mul_sq_log.div_const 2).continuousOn).add
    ((continuous_pow 2).div_const 4).continuousOn

/-! ### The limit at infinity -/

/-- `F - A` in terms of `ξ`. -/
noncomputable def i13D1 (ξ : ℝ) : ℝ :=
  -2 * Real.log ξ * ξ ^ 2 - 8 * Real.log (1 - ξ) ^ 2 +
    Real.log (1 - ξ) * (8 * Real.log ξ + 2 * ξ ^ 2 + 2 / ξ ^ 2) + 2 * ξ - 15 + 2 / ξ

theorem i13F1_sub_prim1 {t : ℝ} (ht : 0 < t) : i13F1 t - i13Prim1 t = i13D1 (i13Xi t) := by
  have hx0 := i13Xi_pos ht.le
  have hx1 := i13Xi_lt_one ht
  have hT := i13Xi_t ht.le
  have hlog : Real.log t = 2 * Real.log (1 - i13Xi t) - Real.log (i13Xi t) := by
    have h1 : 0 < 1 - i13Xi t := by linarith
    conv_lhs => rw [hT]
    rw [Real.log_div (by positivity) hx0.ne', Real.log_pow]
    push_cast; ring
  unfold i13F1 i13Prim1 i13D1 i13Phi1
  rw [hlog]
  set ξ := i13Xi t
  rw [hT]
  field_simp
  ring

theorem tendsto_i13D1 : Tendsto i13D1 (𝓝[>] 0) (𝓝 (-16)) := by
  -- `r(ξ) = log (1 - ξ) + ξ + ξ²/2 = O(ξ³)`
  have hr : Tendsto (fun ξ : ℝ => (Real.log (1 - ξ) + ξ + ξ ^ 2 / 2) / ξ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have hb : ∀ ξ ∈ Ioo (0 : ℝ) (1 / 2),
        ‖(Real.log (1 - ξ) + ξ + ξ ^ 2 / 2) / ξ ^ 2‖ ≤ 2 * ξ := by
      intro ξ hξ
      have ha : |ξ| < 1 := by rw [abs_of_pos hξ.1]; linarith [hξ.2]
      have h := Real.abs_log_sub_add_sum_range_le ha 2
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_of_pos hξ.1] at h
      norm_num at h
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hξ.1 2),
        div_le_iff₀ (pow_pos hξ.1 2)]
      have h2 : ξ ^ 3 / (1 - ξ) ≤ 2 * ξ ^ 3 := by
        rw [div_le_iff₀ (by linarith [hξ.2])]
        nlinarith [hξ.1, hξ.2, pow_pos hξ.1 3]
      calc |Real.log (1 - ξ) + ξ + ξ ^ 2 / 2| = |ξ + ξ ^ 2 / 2 + Real.log (1 - ξ)| := by
            ring_nf
        _ ≤ 2 * ξ ^ 3 := h.trans h2
        _ = 2 * ξ * ξ ^ 2 := by ring
    refine squeeze_zero_norm' (a := fun ξ => 2 * ξ) ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with ξ hξ using hb ξ hξ
    · have : Tendsto (fun ξ : ℝ => 2 * ξ) (𝓝 0) (𝓝 (2 * 0)) := (continuous_const_mul 2).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
  have hxl : Tendsto (fun ξ : ℝ => ξ * Real.log ξ) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuous_mul_log.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have hx : Tendsto (fun ξ : ℝ => ξ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hl1 : Tendsto (fun ξ : ℝ => Real.log (1 - ξ)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun ξ : ℝ => Real.log (1 - ξ)) (𝓝 0) (𝓝 (Real.log (1 - 0))) :=
      ((continuous_const.sub continuous_id).continuousAt.log (by norm_num)).tendsto
    simpa using this.mono_left nhdsWithin_le_nhds
  have hl1d : Tendsto (fun ξ : ℝ => Real.log (1 - ξ) / ξ) (𝓝[>] 0) (𝓝 (-1)) := by
    have hd : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1) 0 := by
      have := ((hasDerivAt_id' (0 : ℝ)).const_sub 1).log (by norm_num)
      simpa using this
    refine (hd.tendsto_slope_zero_right).congr fun y => ?_
    simp [div_eq_inv_mul]
  have hlim := (((((hr.const_mul 2).sub ((hx.mul hxl).const_mul 2)).sub
    ((hl1.pow 2).const_mul 8)).add ((hl1d.mul hxl).const_mul 8)).add
    (((hl1.mul (hx.pow 2))).const_mul 2)).add (hx.const_mul 2)
  have e : Tendsto i13D1 (𝓝[>] 0) (𝓝 (-16 + (2 * 0 - 2 * (0 * 0) - 8 * 0 ^ 2 +
      8 * (-1 * 0) + 2 * (0 * 0 ^ 2) + 2 * 0))) := by
    refine (hlim.const_add (-16)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ξ hξ
    have h0 : ξ ≠ 0 := (show 0 < ξ from hξ).ne'
    unfold i13D1
    field_simp
    ring
  simpa using e

theorem tendsto_i13F1_sub_prim1 :
    Tendsto (fun t => i13F1 t - i13Prim1 t) atTop (𝓝 (-16)) :=
  (tendsto_i13D1.comp tendsto_i13Xi_atTop).congr'
    (eventually_atTop.2 ⟨1, fun t ht => (i13F1_sub_prim1 (by linarith)).symm⟩)

/-! ### The coefficient -/

theorem integrableOn_i13P1 : IntegrableOn i13P1 (Ioo (0 : ℝ) 1) := by
  have h := (integrableOn_i13Dsl_remInt1 1).re
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioo
  simp [i13Dsl_remInt1_one ht.1]

theorem integrableOn_i13P1_sub : IntegrableOn (fun t => i13P1 t - i13A1r t) (Ioi (1 : ℝ)) := by
  have h := (integrableOn_i13Dsl_remInt2 1).re
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [i13Dsl_remInt2_one (zero_lt_one.trans ht)]
  simp

theorem integral_i13P1 : ∫ t in Ioo (0 : ℝ) 1, i13P1 t = i13F1 1 + 11 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      (continuousOn_i13F1.mono Icc_subset_Ici_self) (fun t ht => hasDerivAt_i13F1 ht.1)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
        (by rw [integrableOn_Ioc_iff_integrableOn_Ioo]; exact integrableOn_i13P1)), i13F1_zero]
  ring

theorem integral_i13P1_sub :
    ∫ t in Ioi (1 : ℝ), (i13P1 t - i13A1r t) = -16 - (i13F1 1 - i13Prim1 1) :=
  integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t => i13F1 t - i13Prim1 t)
    (((hasDerivAt_i13F1 one_pos).sub (hasDerivAt_i13Prim1 one_pos)).continuousAt
      |>.continuousWithinAt)
    (fun _ ht => (hasDerivAt_i13F1 (zero_lt_one.trans ht)).sub
      (hasDerivAt_i13Prim1 (zero_lt_one.trans ht)))
    integrableOn_i13P1_sub tendsto_i13F1_sub_prim1

theorem i13Prim1_one : i13Prim1 1 = 11 / 4 := by
  unfold i13Prim1
  norm_num

/-- **The coefficient `c₁ = -9/4`.** -/
theorem i13RemCoeff_one : i13RemCoeff 1 = -9 / 4 := by
  unfold i13RemCoeff
  rw [setIntegral_congr_fun measurableSet_Ioo fun t ht => i13Dsl_remInt1_one ht.1,
    setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) =>
      i13Dsl_remInt2_one (zero_lt_one.trans ht),
    integral_complex_ofReal, integral_complex_ofReal, integral_i13P1, integral_i13P1_sub,
    i13Prim1_one]
  push_cast
  ring

end QED.ThreeLoopD
