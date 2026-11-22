/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondT2Inner
public import QED.ThreeLoopD.SetDMastersI12RSecondT2Lim

/-!
# Set (d), master `I₁₂`: the value of `T_A''(0) + T_B''(0)`

By `QED.ThreeLoopD.deriv_deriv_i12TA_zero` and `QED.ThreeLoopD.deriv_deriv_i12TB_zero`, the sum
`T_A''(0) + T_B''(0)` is the integral over `(θ, u) ∈ (0, 1)²` of the face values, which are
`QED.ThreeLoopD.i12T2In u θ` (`QED.ThreeLoopD.i12Tdd_TA_eq`, `QED.ThreeLoopD.i12Tdd_TB_eq`).
Fubini puts `θ` inside; the `θ`-integral is `QED.ThreeLoopD.i12T2Out u`
(`QED.ThreeLoopD.integral_i12T2In`). With `k = 2u/(1-u)`, the reflection
`Φ(k) + Φ(1/k) = -6 - π² - 3 log² k` and the identities `k/(1+k) = 2u/(1+u)`,
`1/(1+k) = (1-u)/(1+u)`, `log k = ℓ + log u - log (1 - u)`,
`log (1 + k) = log (1 + u) - log (1 - u)` turn it into
`4 i12T2Q u`. The antiderivative `QED.ThreeLoopD.i12T2G` and its endpoint values give, with
`ℓ = log 2`,

  `T_A''(0) + T_B''(0) = 4 (G(1⁻) - G(0⁺))
    = 2 (-36 + 15π²/4 + 6ℓ + 9ℓ² + 3π²ℓ + 2ℓ³ + 45 ζ(3))`.

## Main results

* `QED.ThreeLoopD.i12T2Out_eq`.
* `QED.ThreeLoopD.deriv_deriv_i12TA_add_deriv_deriv_i12TB`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- **The `θ`-integral at fixed `u`, in the letters `u`, `1 - u`, `1 + u`.** -/
theorem i12T2Out_eq {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i12T2Out u = 4 * i12T2Q u := by
  obtain ⟨hu0, hu1⟩ := hu
  have h1m : 0 < 1 - u := by linarith
  have h1p : 0 < 1 + u := by linarith
  have hk := i12Rk_pos ⟨hu0, hu1⟩
  have hk' : i12Rk u = 2 * u / (1 - u) := rfl
  have a1 : i12Rk u / (1 + i12Rk u) = 2 * u / (1 + u) := by rw [hk']; field_simp; ring
  have a2 : 1 / (1 + i12Rk u) = (1 - u) / (1 + u) := by rw [hk']; field_simp; ring
  have a3 : 1 / i12Rk u / (1 + 1 / i12Rk u) = (1 - u) / (1 + u) := by
    rw [hk']; field_simp; ring
  have a4 : 1 / (1 + 1 / i12Rk u) = 2 * u / (1 + u) := by rw [hk']; field_simp; ring
  have l1 : log (i12Rk u) = log 2 + log u - log (1 - u) := by
    rw [hk', log_div (by positivity) h1m.ne', log_mul (by norm_num) hu0.ne']
  have l2 : log (1 + i12Rk u) = log (1 + u) - log (1 - u) := by
    rw [show 1 + i12Rk u = (1 + u) / (1 - u) by rw [hk']; field_simp; ring,
      log_div h1p.ne' h1m.ne']
  have l3 : log (1 / i12Rk u) = -(log 2 + log u - log (1 - u)) := by
    rw [one_div, log_inv, l1]
  have l4 : log (1 + 1 / i12Rk u) = log (1 + u) - log 2 - log u := by
    rw [show 1 + 1 / i12Rk u = (1 + u) / (2 * u) by rw [hk']; field_simp; ring,
      log_div h1p.ne' (by positivity), log_mul (by norm_num) hu0.ne']
    ring
  have hP : i12RPhi (i12Rk u) = -6 - π ^ 2 - 3 * log (i12Rk u) ^ 2 - i12RPhi (1 / i12Rk u) := by
    linarith [i12RPhi_add_i12RPhi_inv hk]
  rw [i12T2Out, hP]
  simp only [i12ThPrim, i12RPhi]
  rw [a3, a4, l3, l4, a1, a2, l1, l2]
  simp only [i12T2Q]
  rw [hk']
  field_simp
  ring

/-- The real integrand of `T_A''(0) + T_B''(0)` on `(θ, u) ∈ (0, 1)²`. -/
noncomputable def i12T2R (z : ℝ × ℝ) : ℝ := i12T2In z.2 z.1

/-- **`T_A''(0) + T_B''(0) = 2 (-36 + 15π²/4 + 6ℓ + 9ℓ² + 3π²ℓ + 2ℓ³ + 45 ζ(3))`.** -/
theorem deriv_deriv_i12TA_add_deriv_deriv_i12TB :
    deriv (deriv i12TA) 0 + deriv (deriv i12TB) 0 =
      ((2 * (-36 + 15 * π ^ 2 / 4 + 6 * log 2 + 9 * log 2 ^ 2 + 3 * π ^ 2 * log 2 +
        2 * log 2 ^ 3 + 45 * zeta3) : ℝ) : ℂ) := by
  obtain ⟨hiA, hdA⟩ := deriv_deriv_i12TA_zero
  obtain ⟨hiB, hdB⟩ := deriv_deriv_i12TB_zero
  have hpt : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
      ((i12Tdd z.1 (i12H 0) (z.2 * (1 - z.2)) (z.2 * z.1) ((1 - z.2) * i12H 0) : ℝ) : ℂ) +
        ((i12Tdd z.1 (i12H 0) (z.2 * (1 - z.2)) ((1 - z.2) * z.1 * i12H 0) z.2 : ℝ) : ℂ) =
      ((i12T2R z : ℝ) : ℂ) := fun z hz => by
    rw [i12Tdd_TA_eq hz.1 hz.2, i12Tdd_TB_eq hz.1 hz.2, i12T2R, i12T2In]
    push_cast
    ring
  have hiR : Integrable i12T2R (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) := by
    refine (hiA.add hiB).re.congr (ae_restrict_of_forall_mem i12_measurableSet2 fun z hz => ?_)
    simp only [Pi.add_apply, hpt z hz]
    exact Complex.ofReal_re _
  rw [hdA, hdB, ← integral_add hiA hiB, setIntegral_congr_fun i12_measurableSet2 hpt,
    integral_complex_ofReal]
  congr 1
  rw [volume_restrict_prod2] at hiR ⊢
  rw [integral_prod_symm _ hiR]
  have hinner : ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ∫ θ in Ioo (0 : ℝ) 1, i12T2R (θ, u) = 4 * i12T2Q u := by
    filter_upwards [hiR.prod_left_ae, ae_restrict_mem measurableSet_Ioo] with u hu hu'
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    change ∫ θ in (0 : ℝ)..1, i12T2In u θ = _
    rw [integral_i12T2In hu' ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hu),
      i12T2Out_eq hu']
  have hQi : IntegrableOn (fun u => 4 * i12T2Q u) (Ioo (0 : ℝ) 1) :=
    hiR.integral_prod_right.congr hinner
  have hQi' : IntervalIntegrable i12T2Q volume 0 1 := by
    refine (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 ?_
    refine (hQi.const_mul (1 / 4)).congr (ae_of_all _ fun u => ?_)
    simp only
    ring
  rw [integral_congr_ae hinner, integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
      (fun u hu => hasDerivAt_i12T2G hu) hQi' tendsto_i12T2G_zero tendsto_i12T2G_one]
  ring

end QED.ThreeLoopD
