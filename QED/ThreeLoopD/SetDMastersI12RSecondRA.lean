/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondPt
public import QED.ThreeLoopD.SetDMastersI12RSecondK
import QED.Polylog.Deriv
import QED.Polylog.ExtraIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Set (d), master `I₁₂`: reduction of `R_A'(0)` to one dimension

By `QED.ThreeLoopD.hasDerivAt_i12RA3_zero`, `R_A'(0)` is the integral over `(ρ, θ, u) ∈ (0, 1)³`
of `(i12RAd ρ θ u - i12RAd 0 θ u) / (ρθ)`. With `m = 1 / h(ρ)` this integrand is

  `(m (-2 log (1 - ρθ) + g(m u θ / (1 - u))) - 2 g(2uθ / (1 - u))) / (ρθ)`.

**`θ` first.** Since `Φ' = g / r` with `Φ(0⁺) = 0`, and `d/dθ Li₂ (ρθ) = -log (1 - ρθ) / θ`,
the `θ`-integral is `(m (2 Li₂ ρ + Φ(m u / (1 - u))) - 2 Φ(2u / (1 - u))) / ρ`.

**`u` second.** By the definition of `K` (`QED.ThreeLoopD.i12RK`), the `u`-integral is
`(m (2 Li₂ ρ + K(m)) - 2 K(2)) / ρ`. Hence

  `R_A'(0) = ∫₀¹ (m (2 Li₂ ρ + K(m)) - 2 K(2)) / ρ dρ`,  `m = 1 / h(ρ) = 4 / (2 - ρ)`.

## Main results

* `QED.ThreeLoopD.integral_i12RA_theta`, `QED.ThreeLoopD.integral_i12RA_u`.
* `QED.ThreeLoopD.deriv_i12RA3_zero_eq`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- The real integrand of `R_A'(0)`. -/
noncomputable def i12RAf (z : ℝ × ℝ × ℝ) : ℝ :=
  (i12RAd z.1 z.2.1 z.2.2 - i12RAd 0 z.2.1 z.2.2) / (z.1 * z.2.1)

/-- The `θ`-antiderivative of the integrand of `R_A'(0)`. -/
noncomputable def i12RAPrim (ρ u θ : ℝ) : ℝ :=
  (1 / i12H ρ * (2 * Li₂ (ρ * θ) + i12RPhi (1 / i12H ρ * u / (1 - u) * θ)) -
    2 * i12RPhi (2 * u / (1 - u) * θ)) / ρ

theorem i12_tendsto_mul_nhdsGT {a : ℝ} (ha : 0 < a) :
    Tendsto (fun θ : ℝ => a * θ) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have := ((continuous_const_mul a).tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with θ (hθ : 0 < θ)
    exact mul_pos ha hθ

theorem hasDerivAt_i12RAPrim {ρ u θ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1)
    (hθ : θ ∈ Ioc (0 : ℝ) 1) :
    HasDerivAt (i12RAPrim ρ u) (i12RAf (ρ, θ, u)) θ := by
  have hH : 0 < i12H ρ := i12H_pos (by linarith [hρ.2])
  have hu1 : 0 < 1 - u := by linarith [hu.2]
  have ha : 0 < 1 / i12H ρ * u / (1 - u) := div_pos (mul_pos (by positivity) hu.1) hu1
  have hb : 0 < 2 * u / (1 - u) := div_pos (by linarith [hu.1]) hu1
  have hρθ : 0 < ρ * θ := mul_pos hρ.1 hθ.1
  have hρθ1 : |ρ * θ| < 1 := by
    rw [abs_of_pos hρθ]; nlinarith [hρ.1, hρ.2, hθ.1, hθ.2]
  have hL := (hasDerivAt_Li₂ hρθ1 hρθ.ne').comp θ ((hasDerivAt_id' θ).const_mul ρ)
  have hA := (hasDerivAt_i12RPhi (mul_pos ha hθ.1)).comp θ ((hasDerivAt_id' θ).const_mul _)
  have hB := (hasDerivAt_i12RPhi (mul_pos hb hθ.1)).comp θ ((hasDerivAt_id' θ).const_mul _)
  have h := ((((hL.const_mul 2).add hA).const_mul (1 / i12H ρ)).sub (hB.const_mul 2)).div_const ρ
  refine h.congr_deriv ?_
  have hθ0 := hθ.1.ne'
  have hρ0 := hρ.1.ne'
  have hH0 := hH.ne'
  have hu0 := hu.1.ne'
  have hu10 := hu1.ne'
  have e1 : u * θ / ((1 - u) * i12H ρ) = 1 / i12H ρ * u / (1 - u) * θ := by
    field_simp
  have e2 : u * θ / ((1 - u) * (1 / 2)) = 2 * u / (1 - u) * θ := by
    field_simp
  simp only [i12RAf, i12RAd, e1, zero_mul, sub_zero, Real.log_one, mul_zero, zero_add,
    i12H_zero, e2]
  field_simp

/-- **The `θ`-integral** of the integrand of `R_A'(0)`, given its integrability. -/
theorem integral_i12RA_theta {ρ u : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1)
    (hint : IntervalIntegrable (fun θ => i12RAf (ρ, θ, u)) volume 0 1) :
    ∫ θ in (0 : ℝ)..1, i12RAf (ρ, θ, u) =
      (1 / i12H ρ * (2 * Li₂ ρ + i12RPhi (1 / i12H ρ * u / (1 - u))) -
        2 * i12RPhi (2 * u / (1 - u))) / ρ := by
  have hH : 0 < i12H ρ := i12H_pos (by linarith [hρ.2])
  have hu1 : 0 < 1 - u := by linarith [hu.2]
  have ha : 0 < 1 / i12H ρ * u / (1 - u) := div_pos (mul_pos (by positivity) hu.1) hu1
  have hb : 0 < 2 * u / (1 - u) := div_pos (by linarith [hu.1]) hu1
  have h0 : Tendsto (i12RAPrim ρ u) (𝓝[>] 0) (𝓝 0) := by
    have hq : Tendsto (fun θ : ℝ => ρ * θ) (𝓝[>] 0) (𝓝 0) :=
      (i12_tendsto_mul_nhdsGT hρ.1).mono_right nhdsWithin_le_nhds
    have hLi : Tendsto (fun θ : ℝ => Li₂ (ρ * θ)) (𝓝[>] 0) (𝓝 (Li₂ 0)) := by
      refine tendsto_Li₂_comp (by norm_num) hq ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ
      exact ⟨by nlinarith [hρ.1, hθ.1], by nlinarith [hρ.1, hρ.2, hθ.1, hθ.2]⟩
    have hA := tendsto_i12RPhi_zero.comp (i12_tendsto_mul_nhdsGT ha)
    have hB := tendsto_i12RPhi_zero.comp (i12_tendsto_mul_nhdsGT hb)
    have h := ((((hLi.const_mul 2).add hA).const_mul (1 / i12H ρ)).sub
      (hB.const_mul 2)).div_const ρ
    rw [Li₂_zero] at h
    convert h using 1
    · rfl
    · simp
  have h1 : Tendsto (i12RAPrim ρ u) (𝓝[<] 1) (𝓝 (i12RAPrim ρ u 1)) :=
    (hasDerivAt_i12RAPrim hρ hu ⟨one_pos, le_rfl⟩).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun θ hθ => hasDerivAt_i12RAPrim hρ hu ⟨hθ.1, hθ.2.le⟩) hint h0 h1]
  simp [i12RAPrim]

/-- **The `u`-integral**: `∫₀¹` of the `θ`-integral is `(m (2 Li₂ ρ + K(m)) - 2 K(2)) / ρ`. -/
theorem integral_i12RA_u {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    ∫ u in Ioo (0 : ℝ) 1, (1 / i12H ρ * (2 * Li₂ ρ + i12RPhi (1 / i12H ρ * u / (1 - u))) -
        2 * i12RPhi (2 * u / (1 - u))) / ρ =
      (1 / i12H ρ * (2 * Li₂ ρ + i12RK (1 / i12H ρ)) - 2 * i12RK 2) / ρ := by
  have hm : 0 < 1 / i12H ρ := by have := i12H_pos (show ρ < 2 by linarith [hρ.2]); positivity
  have hA := integrableOn_i12RK hm
  have hB := integrableOn_i12RK (show (0 : ℝ) < 2 by norm_num)
  have hc : IntegrableOn (fun _ : ℝ => 2 * Li₂ ρ) (Ioo 0 1) := integrableOn_const (by simp)
  have h1 : IntegrableOn (fun u : ℝ => 1 / i12H ρ * (2 * Li₂ ρ +
      i12RPhi (1 / i12H ρ * u / (1 - u)))) (Ioo 0 1) := (hc.add hA).const_mul _
  have h2 : IntegrableOn (fun u : ℝ => 2 * i12RPhi (2 * u / (1 - u))) (Ioo 0 1) :=
    hB.const_mul 2
  rw [integral_div, integral_sub h1 h2,
    integral_const_mul, integral_add hc hA, integral_const_mul, integral_const]
  simp only [i12RK, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  simp [integral_const_mul]

/-- **`R_A'(0)` in one dimension**:
`R_A'(0) = ∫₀¹ (m (2 Li₂ ρ + K(m)) - 2 K(2)) / ρ dρ` with `m = 1 / h(ρ)`; the integrand is
integrable. -/
theorem deriv_i12RA3_zero_eq :
    IntegrableOn (fun ρ => (1 / i12H ρ * (2 * Li₂ ρ + i12RK (1 / i12H ρ)) - 2 * i12RK 2) / ρ)
        (Ioo 0 1) ∧
      deriv i12RA3 0 = ((∫ ρ in Ioo (0 : ℝ) 1,
        (1 / i12H ρ * (2 * Li₂ ρ + i12RK (1 / i12H ρ)) - 2 * i12RK 2) / ρ : ℝ) : ℂ) := by
  obtain ⟨hi, hd⟩ := hasDerivAt_i12RA3_zero
  have hiR : Integrable i12RAf
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))) :=
    hi.re.congr (ae_of_all _ fun z => Complex.ofReal_re _)
  rw [volume_restrict_prod3] at hiR
  have hae : ∀ᵐ ρ ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ∫ w, i12RAf (ρ, w) ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) =
      (1 / i12H ρ * (2 * Li₂ ρ + i12RK (1 / i12H ρ)) - 2 * i12RK 2) / ρ := by
    filter_upwards [hiR.prod_right_ae, ae_restrict_mem measurableSet_Ioo] with ρ hρi hρ
    rw [integral_prod_symm _ hρi, ← integral_i12RA_u hρ]
    refine integral_congr_ae ?_
    filter_upwards [hρi.prod_left_ae, ae_restrict_mem measurableSet_Ioo] with u hu hu'
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    exact integral_i12RA_theta hρ hu'
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hu)
  refine ⟨hiR.integral_prod_left.congr hae, ?_⟩
  rw [hd.deriv, integral_complex_ofReal]
  congr 1
  change ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), i12RAf z = _
  rw [volume_restrict_prod3, integral_prod _ hiR]
  exact integral_congr_ae hae

end QED.ThreeLoopD
