/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RestWire
public import QED.ThreeLoopD.SetDMastersI12RPrim
import QED.Polylog.Reflection
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Set (d), master `I₁₂`: the first Taylor coefficient of the remainder

`QED.ThreeLoopD.i12Rest = ε (R₁ + R_A + R_B) + T_A + T_B` with `T_A(0) = T_B(0) = 0`, so

  `i12Rest'(0) = R₁(0) + R_A(0) + R_B(0) + T_A'(0) + T_B'(0)`.

**Values at `ε = 0`.** There `Φ₁(X, Y) = X Y`, `Φ₀ = 2` and the weights are `(c t)⁻¹`,
`ρ⁻¹ θ⁻¹`:
* `R₁(0) = ∫ u (1 - u) = 1/6`;
* the integrand of `R_A` vanishes, `2/h(ρ) - 4 - 2/h(ρ) + 4 = 0`;
* the integrand of `R_B` is `(2/h(ρθ) - 4) / (ρθ) = 4 / (2 - ρθ)`, so
  `R_B(0) = ∫₀¹ -4 log (1 - ρ/2) / ρ dρ = 4 Li₂ (1/2) = π²/3 - 2 log² 2`.

**Derivatives of the face terms.** Differentiating under the integral sign (the Cauchy estimate
from the bounds of `QED.ThreeLoopD.SetDMastersI12RestAnalytic`), the `ε`-derivative of the
integrand of `T_A` at `0` is `2 g(kθ) / θ` and that of `T_B` is `2 g(θ/k) / θ`, with
`k = 2u / (1 - u)` and `g = QED.ThreeLoopD.i12Rg`. By Fubini and
`QED.ThreeLoopD.integral_i12Rg_pair`,

  `T_A'(0) + T_B'(0) = ∫₀¹ 2 (-6 - π² - 3 log² (2u / (1 - u))) du = -12 - 4π² - 6 log² 2`.

Altogether `r₁ = -71/6 - 11π²/3 - 8 log² 2` (`QED.ThreeLoopD.i12RestR1`).

## Main results

* `QED.ThreeLoopD.i12R1_zero`, `QED.ThreeLoopD.i12RA3_zero`, `QED.ThreeLoopD.i12RB3_zero`.
* `QED.ThreeLoopD.deriv_i12TA_add_deriv_i12TB`.
* `QED.ThreeLoopD.iteratedDeriv_one_i12Rest`: `iteratedDeriv 1 i12Rest 0 / 1! = i12RestR1`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter Topology QED.Polylog
open scoped Real

namespace QED.ThreeLoopD

/-! ### Differentiation under the integral sign -/

/-- **Derivative of a holomorphic parametric integral**: under the hypotheses of
`QED.DimReg.differentiableAt_integral_of_holomorphic`, the derivative at the centre is the
integral of the pointwise derivatives, which are integrable. -/
theorem i12_hasDerivAt_integral_of_holomorphic {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : ℂ → α → ℂ} {z₁ : ℂ} {R : ℝ} (hR : 0 < R) {b : α → ℝ}
    (hb : Integrable b μ) (hFm : ∀ w ∈ ball z₁ R, AEStronglyMeasurable (F w) μ)
    (hFb : ∀ᵐ t ∂μ, ∀ w ∈ ball z₁ R, ‖F w t‖ ≤ b t)
    (hFd : ∀ᵐ t ∂μ, DifferentiableOn ℂ (fun w => F w t) (ball z₁ R)) :
    Integrable (fun t => deriv (fun w => F w t) z₁) μ ∧
      HasDerivAt (fun w => ∫ t, F w t ∂μ) (∫ t, deriv (fun w => F w t) z₁ ∂μ) z₁ := by
  set r := R / 3 with hrdef
  have hr : 0 < r := div_pos hR (by norm_num)
  have hF'b : ∀ᵐ t ∂μ, ∀ w ∈ ball z₁ r, ‖deriv (fun w => F w t) w‖ ≤ b t / r := by
    filter_upwards [hFb, hFd] with t hb' hd' w hw
    have hsub : closedBall w r ⊆ ball z₁ R := by
      intro u hu
      rw [mem_ball] at hw ⊢
      rw [mem_closedBall] at hu
      calc dist u z₁ ≤ dist u w + dist w z₁ := dist_triangle _ _ _
        _ < R := by linarith
    refine norm_deriv_le_of_forall_mem_sphere_norm_le hr (hd'.diffContOnCl_ball hsub) ?_
    intro u hu
    exact hb' u (hsub (sphere_subset_closedBall hu))
  have hz₁ : z₁ ∈ ball z₁ R := mem_ball_self hR
  have hFint : Integrable (F z₁) μ := by
    refine hb.mono' (hFm z₁ hz₁) ?_
    filter_upwards [hFb] with t ht using ht z₁ hz₁
  have hF'm : AEStronglyMeasurable (fun t => deriv (fun w => F w t) z₁) μ := by
    set δ : ℕ → ℂ := fun n => ((r * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ) with hδ
    have hδmem : ∀ n : ℕ, z₁ + δ n ∈ ball z₁ R := by
      intro n
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hδ, norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      rw [hrdef] at ⊢
      nlinarith
    have hδt : Tendsto δ atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h1 := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul r
        rw [mul_zero] at h1
        have h2 := (continuous_ofReal.tendsto 0).comp h1
        rw [ofReal_zero] at h2
        exact h2
      · simp only [hδ, mem_compl_iff, mem_singleton_iff, ofReal_eq_zero]
        positivity
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n t => (δ n)⁻¹ • (F (z₁ + δ n) t - F z₁ t)) (fun n => ?_) ?_
    · exact (((hFm _ (hδmem n)).sub (hFm z₁ hz₁)).const_smul (δ n)⁻¹ :)
    · filter_upwards [hFd] with t ht
      have hd := (ht.differentiableAt (isOpen_ball.mem_nhds hz₁)).hasDerivAt
      rw [hasDerivAt_iff_tendsto_slope_zero] at hd
      exact hd.comp hδt
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F)
    (F' := fun w t => deriv (fun w => F w t) w) (x₀ := z₁)
    (bound := fun t => b t / r) (s := ball z₁ r) (ball_mem_nhds z₁ hr)
    (eventually_of_mem (isOpen_ball.mem_nhds hz₁) hFm) hFint hF'm hF'b (hb.div_const r)
    (by
      filter_upwards [hFd] with t ht x hx
      exact (ht.differentiableAt (isOpen_ball.mem_nhds
        (ball_subset_ball (by rw [hrdef]; linarith) hx))).hasDerivAt)

/-! ### The derivative of the face bracket -/

theorem i12Phi0_comm (ε : ℂ) (X Y : ℝ) : i12Phi0 ε X Y = i12Phi0 ε Y X := by
  simp only [i12Phi0, add_comm X Y, mul_comm X Y]
  ring

/-- `g(X/Y)` in the variables `X, Y`. -/
theorem i12Rg_div_eq {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    i12Rg (X / Y) = 3 + 6 * Real.log Y - 3 * ((X + Y) ^ 2 * Real.log (X + Y) -
      X ^ 2 * Real.log X - Y ^ 2 * Real.log Y) / (X * Y) := by
  have h1 : Real.log (1 + X / Y) = Real.log (X + Y) - Real.log Y := by
    rw [show 1 + X / Y = (X + Y) / Y by field_simp; ring]
    exact Real.log_div (by linarith) hY.ne'
  have h2 : Real.log (X / Y) = Real.log X - Real.log Y := Real.log_div hX.ne' hY.ne'
  simp only [i12Rg]
  rw [h1, h2]
  field_simp
  ring

theorem i12_hasDerivAt_cpow_two_sub {c : ℝ} (hc : 0 < c) :
    HasDerivAt (fun ε : ℂ => (c : ℂ) ^ (2 - 3 * ε)) ((c : ℂ) ^ 2 * (Real.log c : ℂ) * (-3)) 0 := by
  have h1 : HasDerivAt (fun ε : ℂ => 2 - 3 * ε) (-3) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul 3).const_sub 2
  have := h1.const_cpow (c := (c : ℂ)) (Or.inl (ofReal_ne_zero.mpr hc.ne'))
  convert this using 1
  rw [ofReal_log hc.le]
  norm_num

/-- **The `ε`-derivative of the face bracket** `Φ₀(X, Y) - (2 - 3ε) Y ^ (-3ε)` at `0` is
`g(X/Y)`. -/
theorem hasDerivAt_i12_bracket {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    HasDerivAt (fun ε : ℂ => i12Phi0 ε X Y - (2 - 3 * ε) * (Y : ℂ) ^ (-3 * ε))
      ((i12Rg (X / Y) : ℝ) : ℂ) 0 := by
  have hXY : 0 < X + Y := by linarith
  have hlin : HasDerivAt (fun ε : ℂ => 2 - 3 * ε) (-3) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul 3).const_sub 2
  have hq : HasDerivAt (fun ε : ℂ => (Y : ℂ) ^ (-3 * ε)) ((Real.log Y : ℂ) * (-3)) 0 := by
    have h1 : HasDerivAt (fun ε : ℂ => -3 * ε) (-3) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (-3)
    have := h1.const_cpow (c := (Y : ℂ)) (Or.inl (ofReal_ne_zero.mpr hY.ne'))
    convert this using 1
    rw [ofReal_log hY.le]
    simp
  have h := ((((i12_hasDerivAt_cpow_two_sub hXY).sub (i12_hasDerivAt_cpow_two_sub hX)).sub
    (i12_hasDerivAt_cpow_two_sub hY)).div_const ((X * Y : ℝ) : ℂ)).sub (hlin.mul hq)
  convert h using 1
  · funext ε
    simp only [i12Phi0, Pi.sub_apply, Pi.mul_apply]
  rw [i12Rg_div_eq hX hY]
  have hX0 : (X : ℂ) ≠ 0 := ofReal_ne_zero.mpr hX.ne'
  have hY0 : (Y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hY.ne'
  simp only [mul_zero, cpow_zero]
  push_cast
  field_simp
  ring

/-! ### The pointwise derivatives of the face integrands -/

/-- `k = 2u / (1 - u)`, the ratio `X / (Yθ)` of the face `ρ = 0` of the sector `t < v`. -/
noncomputable def i12Rk (u : ℝ) : ℝ := 2 * u / (1 - u)

theorem i12Rk_pos {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : 0 < i12Rk u :=
  div_pos (by linarith [hu.1]) (by linarith [hu.2])

/-- The `ε`-derivative at `0` of the integrand of `T_A` is `2 g(kθ) / θ`. -/
theorem hasDerivAt_i12TA_integrand {θ u : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun ε : ℂ => (θ : ℂ) ^ (2 * ε - 1) * (i12GA ε 0 θ u - i12GA0 ε 0 u))
      ((2 * i12Rg (i12Rk u * θ) / θ : ℝ) : ℂ) 0 := by
  have hθ0 : 0 < θ := hθ.1
  have hH : 0 < i12H 0 := i12H_pos (by norm_num)
  have hP : 0 < u * (1 - u) := mul_pos hu.1 (by linarith [hu.2])
  have hY : 0 < (1 - u) * i12H 0 := mul_pos (by linarith [hu.2]) hH
  have hX : 0 < u * θ := mul_pos hu.1 hθ0
  have e : (fun ε : ℂ => (θ : ℂ) ^ (2 * ε - 1) * (i12GA ε 0 θ u - i12GA0 ε 0 u)) =
      fun ε => ((θ : ℂ) ^ (2 * ε - 1) * ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1) *
        ((u * (1 - u) : ℝ) : ℂ) ^ ε) * (i12Phi0 ε (u * θ) ((1 - u) * i12H 0) -
          (2 - 3 * ε) * (((1 - u) * i12H 0 : ℝ) : ℂ) ^ (-3 * ε)) := by
    funext ε
    simp only [i12GA, i12GA0, zero_mul, sub_zero, ofReal_one, one_cpow, mul_one]
    ring
  have hA : DifferentiableAt ℂ (fun ε : ℂ => (θ : ℂ) ^ (2 * ε - 1) *
      ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1) * ((u * (1 - u) : ℝ) : ℂ) ^ ε) 0 := by
    fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))
  have h := hA.hasDerivAt.mul (hasDerivAt_i12_bracket hX hY)
  rw [e]
  convert h using 1
  have hk : u * θ / ((1 - u) * i12H 0) = i12Rk u * θ := by
    rw [i12H_zero, i12Rk]
    have : 1 - u ≠ 0 := by linarith [hu.2]
    field_simp
  rw [hk, i12Phi0_zero hX hY, i12H_zero]
  have hθc : (θ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hθ0.ne'
  simp only [mul_zero, zero_sub, cpow_zero, cpow_neg_one, sub_zero, mul_one]
  push_cast
  field_simp
  ring

/-- The `ε`-derivative at `0` of the integrand of `T_B` is `2 g(θ/k) / θ`. -/
theorem hasDerivAt_i12TB_integrand {θ u : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun ε : ℂ => (θ : ℂ) ^ (2 * ε - 1) * (i12GB ε 0 θ u - i12GB0 ε 0 u))
      ((2 * i12Rg (θ / i12Rk u) / θ : ℝ) : ℂ) 0 := by
  have hθ0 : 0 < θ := hθ.1
  have hH : 0 < i12H 0 := i12H_pos (by norm_num)
  have hP : 0 < u * (1 - u) := mul_pos hu.1 (by linarith [hu.2])
  have hY : 0 < (1 - u) * θ * i12H 0 := mul_pos (mul_pos (by linarith [hu.2]) hθ0) hH
  have hX : 0 < u := hu.1
  have e : (fun ε : ℂ => (θ : ℂ) ^ (2 * ε - 1) * (i12GB ε 0 θ u - i12GB0 ε 0 u)) =
      fun ε => ((θ : ℂ) ^ (2 * ε - 1) * ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1) *
        ((u * (1 - u) : ℝ) : ℂ) ^ ε) * (i12Phi0 ε ((1 - u) * θ * i12H 0) u -
          (2 - 3 * ε) * (u : ℂ) ^ (-3 * ε)) := by
    funext ε
    simp only [i12GB, i12GB0, zero_mul, sub_zero, ofReal_one, one_cpow, mul_one,
      i12Phi0_comm ε u]
    ring
  have hA : DifferentiableAt ℂ (fun ε : ℂ => (θ : ℂ) ^ (2 * ε - 1) *
      ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1) * ((u * (1 - u) : ℝ) : ℂ) ^ ε) 0 := by
    fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))
  have h := hA.hasDerivAt.mul (hasDerivAt_i12_bracket hY hX)
  rw [e]
  convert h using 1
  have hk : (1 - u) * θ * i12H 0 / u = θ / i12Rk u := by
    rw [i12H_zero, i12Rk]
    have : 1 - u ≠ 0 := by linarith [hu.2]
    have : u ≠ 0 := hX.ne'
    field_simp
  rw [hk, i12Phi0_zero hY hX, i12H_zero]
  have hθc : (θ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hθ0.ne'
  simp only [mul_zero, zero_sub, cpow_zero, cpow_neg_one, sub_zero, mul_one]
  push_cast
  field_simp
  ring

/-! ### The three-dimensional remainders at `ε = 0` -/

theorem i12_volume_real_Ioo : (volume.restrict (Ioo (0 : ℝ) 1)).real univ = 1 := by
  simp

/-- An integral over the cube of a function of the last coordinate. -/
theorem i12_integral_cube_snd_snd (f : ℝ → ℝ) :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), f z.2.2 =
      ∫ u in Ioo (0 : ℝ) 1, f u := by
  rw [volume_restrict_prod3, integral_fun_snd (f := fun w : ℝ × ℝ => f w.2), integral_fun_snd,
    i12_volume_real_Ioo, one_smul, one_smul]

/-- `R₁(0) = ∫ u (1 - u) = 1/6`. -/
theorem i12R1_zero : i12R1 0 = 1 / 6 := by
  have hpt : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1),
      i12Wt 0 (z.1 * (1 - z.1)) z.2.1 z.2.2 *
        i12Phi1 0 (z.2.2 * z.2.1) ((1 - z.2.2) * (z.1 * (1 - z.1))) =
        ((z.2.2 * (1 - z.2.2) : ℝ) : ℂ) := by
    rintro ⟨y, t, u⟩ ⟨hy, ht, hu⟩
    have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.1.ne'
    have hy1 : (1 - (y : ℂ)) ≠ 0 := by
      rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (by linarith [hy.2])
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
    have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.1.ne'
    have hu1 : (1 - (u : ℂ)) ≠ 0 := by
      rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (by linarith [hu.2])
    simp only [i12Wt, i12Phi1, mul_zero, zero_sub, neg_zero, cpow_zero, cpow_neg_one,
      sub_zero, mul_one, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast, cpow_one]
    push_cast
    field_simp
    ring
  rw [i12R1, setIntegral_congr_fun i12_measurableSet3 hpt, integral_complex_ofReal,
    i12_integral_cube_snd_snd (fun u => u * (1 - u)), ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]
  have : ∫ u in (0 : ℝ)..1, u * (1 - u) = 1 / 6 := by
    simp only [mul_sub, mul_one]
    rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
      ((by fun_prop : Continuous fun u : ℝ => u * u).intervalIntegrable _ _)]
    simp only [← sq, integral_id, integral_pow]
    norm_num
  rw [this]
  push_cast
  ring

/-- The integrand of `R_A` vanishes at `ε = 0`. -/
theorem i12RA3_zero : i12RA3 0 = 0 := by
  refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
  obtain ⟨hρ, hθ, hu⟩ := hz
  have hH : ∀ ρ : ℝ, ρ ∈ Ico (0 : ℝ) 1 → 0 < (1 - z.2.2) * i12H ρ := fun ρ hρ =>
    mul_pos (by linarith [hu.2]) (i12H_pos (by linarith [hρ.2]))
  have hX : 0 < z.2.2 * z.2.1 := mul_pos hu.1 hθ.1
  simp only [i12GA, i12GA0, i12Phi0_zero hX (hH z.1 ⟨hρ.1.le, hρ.2⟩),
    i12Phi0_zero hX (hH 0 ⟨le_rfl, one_pos⟩)]
  simp

/-- `R_B(0) = 4 Li₂ (1/2)`: the integrand is `4 / (2 - ρθ)`. -/
theorem i12RB3_zero : i12RB3 0 = ((4 * Li₂ (1 / 2) : ℝ) : ℂ) := by
  have hpt : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1),
      i12SecWt 0 z.1 z.2.1 * (i12GB 0 z.1 z.2.1 z.2.2 - i12GB 0 0 z.2.1 z.2.2 -
        i12GB0 0 z.1 z.2.2 + i12GB0 0 0 z.2.2) = ((4 / (2 - z.1 * z.2.1) : ℝ) : ℂ) := by
    rintro ⟨ρ, θ, u⟩ ⟨hρ, hθ, hu⟩
    have hH : ∀ x : ℝ, x < 2 → 0 < (1 - u) * θ * i12H x := fun x hx =>
      mul_pos (mul_pos (by linarith [hu.2]) hθ.1) (i12H_pos hx)
    have hρθ : ρ * θ < 1 := by nlinarith [hρ.1, hρ.2, hθ.1, hθ.2]
    have hρ0 : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ.1.ne'
    have hθ0 : (θ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hθ.1.ne'
    have hd : (2 - (ρ : ℂ) * θ) ≠ 0 := by
      rw [← ofReal_mul, ← ofReal_ofNat, ← ofReal_sub]
      exact ofReal_ne_zero.mpr (by linarith)
    simp only [i12SecWt, i12GB, i12GB0, i12Phi0_zero hu.1 (hH _ (by linarith : ρ * θ < 2)),
      i12Phi0_zero hu.1 (hH _ (by norm_num : (0 : ℝ) * θ < 2))]
    simp only [zero_mul, mul_zero, zero_sub, neg_zero, cpow_zero, cpow_neg_one, sub_zero,
      mul_one, i12H]
    push_cast
    field_simp
    ring
  have hin : ∀ ρ ∈ Ioo (0 : ℝ) 1, ∫ θ in Ioo (0 : ℝ) 1, 4 / (2 - ρ * θ) =
      -4 * Real.log (1 - ρ / 2) / ρ := by
    intro ρ hρ
    have hpos : ∀ θ ∈ uIcc (0 : ℝ) 1, 0 < 2 - ρ * θ := by
      intro θ hθ
      rw [uIcc_of_le zero_le_one] at hθ
      nlinarith [hρ.1, hρ.2, hθ.1, hθ.2]
    have hd : ∀ θ ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x => -(4 / ρ) * Real.log (2 - ρ * x))
        (4 / (2 - ρ * θ)) θ := by
      intro θ hθ
      have h := ((((hasDerivAt_id' θ).const_mul ρ).const_sub 2).log (hpos θ hθ).ne').const_mul
        (-(4 / ρ))
      refine h.congr_deriv ?_
      have := hρ.1.ne'
      have := (hpos θ hθ).ne'
      field_simp
    have hc : ContinuousOn (fun θ => 4 / (2 - ρ * θ)) (uIcc (0 : ℝ) 1) :=
      continuousOn_const.div (by fun_prop) fun θ hθ => (hpos θ hθ).ne'
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
    have h2 : Real.log (1 - ρ / 2) = Real.log (2 - ρ) - Real.log 2 := by
      rw [show 1 - ρ / 2 = (2 - ρ) / 2 by ring]
      exact Real.log_div (by linarith [hρ.2]) (by norm_num)
    rw [h2]
    simp only [mul_one, mul_zero, sub_zero]
    field_simp
    ring
  have hmeas : Measurable fun z : ℝ × ℝ × ℝ => 4 / (2 - z.1 * z.2.1) := by fun_prop
  have hbd : ∀ᵐ z ∂(volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))),
      ‖4 / (2 - z.1 * z.2.1)‖ ≤ 4 := by
    refine ae_restrict_of_forall_mem i12_measurableSet3 fun z hz => ?_
    obtain ⟨hρ, hθ, -⟩ := hz
    have h1 : 1 ≤ 2 - z.1 * z.2.1 := by nlinarith [hρ.1, hρ.2, hθ.1, hθ.2]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_iff₀ (by linarith)]
    linarith
  rw [volume_restrict_prod3] at hbd
  have hint := Integrable.of_bound hmeas.aestronglyMeasurable 4 hbd
  rw [i12RB3, setIntegral_congr_fun i12_measurableSet3 hpt, integral_complex_ofReal,
    volume_restrict_prod3, integral_prod _ hint]
  have hfst : ∀ ρ : ℝ, ∫ w, 4 / (2 - (ρ, w).1 * (ρ, w).2.1) ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))) = ∫ θ in Ioo (0 : ℝ) 1, 4 / (2 - ρ * θ) := fun ρ => by
    rw [integral_fun_fst (f := fun θ => 4 / (2 - ρ * θ)), i12_volume_real_Ioo, one_smul]
  simp_rw [hfst]
  rw [setIntegral_congr_fun measurableSet_Ioo hin, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegrable_and_integral_i12_log_half.2]

/-! ### The derivatives of the face terms -/

/-- The `ε`-derivative of `T_A` at `0` is the integral of `2 g(kθ) / θ`, which is integrable. -/
theorem hasDerivAt_i12TA_zero :
    Integrable (fun z : ℝ × ℝ => ((2 * i12Rg (i12Rk z.2 * z.1) / z.1 : ℝ) : ℂ))
        (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) ∧
      HasDerivAt i12TA (∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
        ((2 * i12Rg (i12Rk z.2 * z.1) / z.1 : ℝ) : ℂ)) 0 := by
  have h0 : ‖(0 : ℂ)‖ < 1 / 200 := by norm_num
  obtain ⟨hi, hd⟩ := i12_hasDerivAt_integral_of_holomorphic (z₁ := 0)
    (F := fun ε (z : ℝ × ℝ) => (z.1 : ℂ) ^ (2 * ε - 1) * (i12GA ε 0 z.1 z.2 - i12GA0 ε 0 z.2))
    (by norm_num : (0 : ℝ) < 1 / 200)
    (b := fun z => 6912 * i12Maj2 z) (integrable_i12Maj2.const_mul 6912)
    (fun ε _ => (by unfold i12GA i12GA0 i12Phi0 i12H; fun_prop :
      Measurable fun z : ℝ × ℝ => (z.1 : ℂ) ^ (2 * ε - 1) *
        (i12GA ε 0 z.1 z.2 - i12GA0 ε 0 z.2)).aestronglyMeasurable)
    (ae_restrict_of_forall_mem i12_measurableSet2 fun z hz ε hε =>
      norm_i12TA_integrand_le (i12_ball_small h0 ε hε) hz)
    (by
      refine ae_restrict_of_forall_mem i12_measurableSet2 fun z hz => ?_
      obtain ⟨hθ, hu⟩ := hz
      have h0' : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
      have hθ0 := hθ.1
      have hd : Differentiable ℂ fun ε : ℂ => (z.1 : ℂ) ^ (2 * ε - 1) := by
        fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))
      exact (hd.mul ((differentiable_i12GA h0' hθ hu).sub
        (differentiable_i12GA0 h0' hu))).differentiableOn)
  have hpt : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
      deriv (fun ε : ℂ => (z.1 : ℂ) ^ (2 * ε - 1) * (i12GA ε 0 z.1 z.2 - i12GA0 ε 0 z.2)) 0 =
        ((2 * i12Rg (i12Rk z.2 * z.1) / z.1 : ℝ) : ℂ) := fun z hz =>
    (hasDerivAt_i12TA_integrand hz.1 hz.2).deriv
  refine ⟨hi.congr (ae_restrict_of_forall_mem i12_measurableSet2 hpt), ?_⟩
  rw [← setIntegral_congr_fun i12_measurableSet2 hpt]
  exact hd

/-- The `ε`-derivative of `T_B` at `0` is the integral of `2 g(θ/k) / θ`, which is integrable. -/
theorem hasDerivAt_i12TB_zero :
    Integrable (fun z : ℝ × ℝ => ((2 * i12Rg (z.1 / i12Rk z.2) / z.1 : ℝ) : ℂ))
        (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) ∧
      HasDerivAt i12TB (∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
        ((2 * i12Rg (z.1 / i12Rk z.2) / z.1 : ℝ) : ℂ)) 0 := by
  have h0 : ‖(0 : ℂ)‖ < 1 / 200 := by norm_num
  obtain ⟨hi, hd⟩ := i12_hasDerivAt_integral_of_holomorphic (z₁ := 0)
    (F := fun ε (z : ℝ × ℝ) => (z.1 : ℂ) ^ (2 * ε - 1) * (i12GB ε 0 z.1 z.2 - i12GB0 ε 0 z.2))
    (by norm_num : (0 : ℝ) < 1 / 200)
    (b := fun z => 1728 * i12Maj2 z) (integrable_i12Maj2.const_mul 1728)
    (fun ε _ => (by unfold i12GB i12GB0 i12Phi0 i12H; fun_prop :
      Measurable fun z : ℝ × ℝ => (z.1 : ℂ) ^ (2 * ε - 1) *
        (i12GB ε 0 z.1 z.2 - i12GB0 ε 0 z.2)).aestronglyMeasurable)
    (ae_restrict_of_forall_mem i12_measurableSet2 fun z hz ε hε =>
      norm_i12TB_integrand_le (i12_ball_small h0 ε hε) hz)
    (by
      refine ae_restrict_of_forall_mem i12_measurableSet2 fun z hz => ?_
      obtain ⟨hθ, hu⟩ := hz
      have h0' : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
      have hθ0 := hθ.1
      have hd : Differentiable ℂ fun ε : ℂ => (z.1 : ℂ) ^ (2 * ε - 1) := by
        fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))
      exact (hd.mul ((differentiable_i12GB h0' hθ hu).sub
        (differentiable_i12GB0 h0' hu))).differentiableOn)
  have hpt : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
      deriv (fun ε : ℂ => (z.1 : ℂ) ^ (2 * ε - 1) * (i12GB ε 0 z.1 z.2 - i12GB0 ε 0 z.2)) 0 =
        ((2 * i12Rg (z.1 / i12Rk z.2) / z.1 : ℝ) : ℂ) := fun z hz =>
    (hasDerivAt_i12TB_integrand hz.1 hz.2).deriv
  refine ⟨hi.congr (ae_restrict_of_forall_mem i12_measurableSet2 hpt), ?_⟩
  rw [← setIntegral_congr_fun i12_measurableSet2 hpt]
  exact hd

/-- The combined real integrand `2 (g(kθ) + g(θ/k)) / θ` of `T_A'(0) + T_B'(0)`. -/
noncomputable def i12RT (z : ℝ × ℝ) : ℝ :=
  2 * ((i12Rg (i12Rk z.2 * z.1) + i12Rg (z.1 / i12Rk z.2)) / z.1)

/-- **`∫∫ 2 (g(kθ) + g(θ/k)) / θ = -12 - 4π² - 6 log² 2`**, given integrability. -/
theorem integral_i12RT (hi : Integrable i12RT (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))) :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i12RT z = -12 - 4 * π ^ 2 - 6 * Real.log 2 ^ 2 := by
  rw [volume_restrict_prod2] at hi ⊢
  rw [integral_prod_symm _ hi]
  have hinner : ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)), ∫ θ in Ioo (0 : ℝ) 1, i12RT (θ, u) =
      (-12 - 2 * π ^ 2) - 6 * Real.log (2 * u / (1 - u)) ^ 2 := by
    filter_upwards [hi.prod_left_ae, ae_restrict_mem measurableSet_Ioo] with u hu hu'
    have hk := i12Rk_pos hu'
    have hu2 : IntegrableOn (fun θ => (i12Rg (i12Rk u * θ) + i12Rg (θ / i12Rk u)) / θ)
        (Ioo (0 : ℝ) 1) := by
      refine (hu.div_const 2).congr (ae_of_all _ fun θ => ?_)
      simp only [i12RT]
      ring
    simp only [i12RT]
    rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one, integral_i12Rg_pair hk
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hu2), i12Rk]
    ring
  rw [integral_congr_ae hinner]
  have hL := intervalIntegrable_and_integral_i12_log_sq
  have hLi : IntegrableOn (fun u : ℝ => Real.log (2 * u / (1 - u)) ^ 2) (Ioo (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 hL.1
  rw [integral_sub (integrable_const _) (hLi.const_mul 6), integral_const_mul, integral_const,
    i12_volume_real_Ioo, one_smul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, hL.2]
  ring

/-- **`T_A'(0) + T_B'(0) = -12 - 4π² - 6 log² 2`.** -/
theorem deriv_i12TA_add_deriv_i12TB :
    deriv i12TA 0 + deriv i12TB 0 = ((-12 - 4 * π ^ 2 - 6 * Real.log 2 ^ 2 : ℝ) : ℂ) := by
  obtain ⟨hiA, hdA⟩ := hasDerivAt_i12TA_zero
  obtain ⟨hiB, hdB⟩ := hasDerivAt_i12TB_zero
  have hpt : ∀ z : ℝ × ℝ, ((2 * i12Rg (i12Rk z.2 * z.1) / z.1 : ℝ) : ℂ) +
      ((2 * i12Rg (z.1 / i12Rk z.2) / z.1 : ℝ) : ℂ) = ((i12RT z : ℝ) : ℂ) := fun z => by
    simp only [i12RT]
    push_cast
    ring
  have hiR : Integrable i12RT (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) := by
    refine (hiA.add hiB).re.congr (ae_of_all _ fun z => ?_)
    simp only [Pi.add_apply, hpt]
    exact ofReal_re _
  rw [hdA.deriv, hdB.deriv, ← integral_add hiA hiB]
  simp_rw [hpt]
  rw [integral_complex_ofReal, integral_i12RT hiR]

/-! ### The first Taylor coefficient -/

/-- **The first Taylor coefficient of the remainder**:
`i12Rest'(0) = -71/6 - 11π²/3 - 8 log² 2`. -/
theorem iteratedDeriv_one_i12Rest :
    iteratedDeriv 1 i12Rest 0 / (1 : ℕ).factorial = i12RestR1 := by
  have h0 : ‖(0 : ℂ)‖ < 1 / 200 := by norm_num
  have hS := (((differentiableAt_i12R1 h0).add (differentiableAt_i12RA3 h0)).add
    (differentiableAt_i12RB3 h0)).hasDerivAt
  have h := (((hasDerivAt_id' (0 : ℂ)).mul hS).add (differentiableAt_i12TA h0).hasDerivAt).add
    (differentiableAt_i12TB h0).hasDerivAt
  have h' : HasDerivAt i12Rest _ 0 := h
  rw [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, div_one, h'.deriv]
  simp only [one_mul, zero_mul, add_zero, Pi.add_apply]
  rw [i12R1_zero, i12RA3_zero, i12RB3_zero, add_assoc, deriv_i12TA_add_deriv_i12TB,
    Li₂_one_half, i12RestR1]
  push_cast
  ring

end QED.ThreeLoopD
