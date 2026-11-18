/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.HeavyVPUnit
public import QED.Chain.HeavyLepton
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The limit value of the heavy-flavour VP unit is `A₂⁽⁴⁾(1/M_L)` (O3-M2 with O3-M3)

Helper-level link between the heavy-flavour VP unit of `QED/Chain/HeavyVPUnit.lean` and the
closed form `QED.Chain.HeavyLepton.a2Heavy` (Passera (10)) of `QED/Chain/HeavyLepton.lean`. It is
**not** frozen and does not depend on any multi-lepton model.

## Main statements

* `vpLim_eq_heavyIntegral`: for `M ≠ 0`,
  `vpLim M = ∫₀¹ dv ρ(v) f2(4M²/(1-v²)) = ∫₀¹ (1-x) Π̂((1/M)² x²/(1-x)) dx = heavyIntegral (1/M)`.
  Pointwise in `x` this is the spectral form of `Π̂` (`QED.Chain.piHat_eq_spectral`), and the two
  integrations are exchanged by Fubini for the bounded kernel `ρ(v) f2Kernel(4M²/(1-v²), x)`
  (`limKernel_bound`, at most `1/(4M²)` on `(0,1]²`).
* `vpLim_eq_a2Heavy`: for `M_L > 1`, `vpLim M_L = a2Heavy (1/M_L)` (by `integral_heavy`); at
  `M_L = 1` the value is `vpLim_one`, the limit `a2Heavy y → 119/36 - π²/3` as `y → 1⁻`.
* `abs_heavyLimSum_sub_a2Heavy_le`: for `1 < M_L ≤ M₁, M₂`,
  `|heavyLimSum M_L M₁ M₂ - a2Heavy (1/M_L)| ≤ (1/M₁² + 1/M₂²)/45`.
* `heavyUnitReg_iterated_limit_a2Heavy`: for `y ∈ (0,1)` and loop mass `M_L = 1/y`, the D-37.4
  iterated limit of `heavyUnitReg (1/y) m_γ Λ M₁ M₂` (masses first) is `a2Heavy y`.
* `heavyUnitReg_iterated_limit_mass`: the same in physical units, for an open line of mass
  `m₀ > 0` and a loop of mass `m_ℓ > m₀`, with every mass divided by `m₀` (the analytic content of
  the mass-scaling step; the coefficients are scale invariant, `pvC1L_smul`); the target is
  `a2Heavy (m₀/m_ℓ)`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.Chain.HeavyVP

open QED.TwoLoop.VPUnit QED.Chain.HeavyLepton

/-! ### The spectral form on the photon curve with loop mass `M` -/

/-- On the photon curve, `(1-x) ρ(v) s/(s + 4/(1-v²))` with `s = (1/M)² x²/(1-x)` is
`ρ(v) f2Kernel(4M²/(1-v²), x)`, for `0 < x < 1`, `0 ≤ v < 1`. -/
theorem spectral_integrand_eq {M x v : ℝ} (hM : M ≠ 0) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hv0 : 0 ≤ v) (hv1 : v < 1) :
    (1 - x) * (v ^ 2 * (1 - v ^ 2 / 3) / (1 - v ^ 2) *
        ((1 / M) ^ 2 * (x ^ 2 / (1 - x)) / ((1 / M) ^ 2 * (x ^ 2 / (1 - x)) + 4 / (1 - v ^ 2)))) =
      rho v * f2Kernel (4 * M ^ 2 / (1 - v ^ 2)) x := by
  obtain ⟨hx0, hx1⟩ := hx
  have h1x : 0 < 1 - x := by linarith
  have hs : 0 < 1 - v ^ 2 := by nlinarith
  have hM2 : 0 < M ^ 2 := by positivity
  have hd : 0 < x ^ 2 + (1 - x) * (4 * M ^ 2 / (1 - v ^ 2)) := by positivity
  have hd' : 0 < (1 / M) ^ 2 * (x ^ 2 / (1 - x)) + 4 / (1 - v ^ 2) := by positivity
  unfold rho f2Kernel
  field_simp

/-- **The heavy-lepton insertion integrand as a `v`-integral.** For `M ≠ 0` and `0 < x < 1`,
`(1-x) Π̂((1/M)² x²/(1-x)) = ∫₀¹ ρ(v) f2Kernel(4M²/(1-v²), x) dv`. -/
theorem heavy_integrand_eq_spectral {M x : ℝ} (hM : M ≠ 0) (hx : x ∈ Ioo (0 : ℝ) 1) :
    (1 - x) * QED.Chain.piHat ((1 / M) ^ 2 * (x ^ 2 / (1 - x))) =
      ∫ v in (0 : ℝ)..1, rho v * f2Kernel (4 * M ^ 2 / (1 - v ^ 2)) x := by
  have hs : -4 < (1 / M) ^ 2 * (x ^ 2 / (1 - x)) := by
    have : 0 ≤ (1 / M) ^ 2 * (x ^ 2 / (1 - x)) :=
      mul_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg x) (by linarith [hx.2]))
    linarith
  rw [QED.Chain.piHat_eq_spectral hs, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ 1 := by simp [ae_iff, measure_singleton]
  filter_upwards [hne] with v hv1 hv
  rw [uIoc_of_le zero_le_one] at hv
  exact spectral_integrand_eq hM hx hv.1.le (lt_of_le_of_ne hv.2 hv1)

/-! ### Fubini on `(0,1]²` -/

/-- The integrand of `vpLim M` before the `x`-integration: `ρ(v) f2Kernel(4M²/(1-v²), x)`. -/
noncomputable def limKernel (M : ℝ) (q : ℝ × ℝ) : ℝ :=
  rho q.1 * f2Kernel (4 * M ^ 2 / (1 - q.1 ^ 2)) q.2

theorem measurable_limKernel (M : ℝ) : Measurable (limKernel M) := by
  unfold limKernel rho f2Kernel
  fun_prop

theorem limKernel_bound {M : ℝ} (hM : M ≠ 0) {q : ℝ × ℝ}
    (hq : q ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) : ‖limKernel M q‖ ≤ 1 / (4 * M ^ 2) := by
  obtain ⟨⟨hv0, hv1⟩, ⟨hx0, hx1⟩⟩ := hq
  have hx : q.2 ∈ Icc (0 : ℝ) 1 := ⟨hx0.le, hx1⟩
  have hM2 : 0 < M ^ 2 := by positivity
  rcases hv1.lt_or_eq with hv1 | hv1
  · have hs : 0 < 1 - q.1 ^ 2 := by nlinarith
    have hc : 0 < 4 * M ^ 2 / (1 - q.1 ^ 2) := by positivity
    have hr : 0 ≤ rho q.1 := div_nonneg (mul_nonneg (sq_nonneg _) (by nlinarith)) hs.le
    have k0 := f2Kernel_nonneg hc hx
    have k1 := f2Kernel_le hc hx
    have k2 : q.2 ^ 2 / (4 * M ^ 2 / (1 - q.1 ^ 2)) ≤ 1 / (4 * M ^ 2 / (1 - q.1 ^ 2)) :=
      div_le_div_of_nonneg_right (by nlinarith) hc.le
    unfold limKernel
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr k0)]
    calc rho q.1 * f2Kernel (4 * M ^ 2 / (1 - q.1 ^ 2)) q.2
        ≤ rho q.1 * (1 / (4 * M ^ 2 / (1 - q.1 ^ 2))) :=
          mul_le_mul_of_nonneg_left (k1.trans k2) hr
      _ = q.1 ^ 2 * (1 - q.1 ^ 2 / 3) / (4 * M ^ 2) := by
          unfold rho
          field_simp
      _ ≤ 1 / (4 * M ^ 2) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith
  · have : rho q.1 = 0 := by simp [rho, hv1]
    simp only [limKernel, this, zero_mul, norm_zero]
    positivity

theorem integrable_limKernel {M : ℝ} (hM : M ≠ 0) :
    Integrable (limKernel M)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  refine Integrable.mono' (integrable_const (1 / (4 * M ^ 2)))
    (measurable_limKernel M).aestronglyMeasurable ?_
  rw [Measure.prod_restrict]
  exact (ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)).2
    (Eventually.of_forall fun q hq => limKernel_bound hM hq)

/-- **The limited one-flavour function is the heavy-lepton insertion.** For `M ≠ 0`,
`vpLim M = ∫₀¹ (1-x) Π̂((1/M)² x²/(1-x)) dx = heavyIntegral (1/M)`. -/
theorem vpLim_eq_heavyIntegral {M : ℝ} (hM : M ≠ 0) : vpLim M = heavyIntegral (1 / M) := by
  have hI := integrable_limKernel hM
  unfold vpLim heavyIntegral
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  have hv : ∀ v, rho v * f2 (4 * M ^ 2 / (1 - v ^ 2)) =
      ∫ x in Ioc (0 : ℝ) 1, limKernel M (v, x) := fun v => by
    unfold f2 limKernel
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact (integral_const_mul _ _).symm
  simp only [hv]
  rw [integral_integral_swap (f := fun v x => limKernel M (v, x)) hI]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae
    (show ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 by simp [ae_iff, measure_singleton])] with x hx hx1
  have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
  rw [heavy_integrand_eq_spectral hM hx', intervalIntegral.integral_of_le zero_le_one]
  rfl

/-- **The heavy limit value is Passera (10).** For `M_L > 1`, `vpLim M_L = a2Heavy (1/M_L)`. -/
theorem vpLim_eq_a2Heavy {ML : ℝ} (hML : 1 < ML) : vpLim ML = a2Heavy (1 / ML) := by
  have hML0 : 0 < ML := by linarith
  rw [vpLim_eq_heavyIntegral hML0.ne']
  exact heavyIntegral_eq ⟨by positivity, (div_lt_one hML0).2 hML⟩

/-- In the mass ratio `y = m/m_ℓ ∈ (0,1)`: `vpLim (1/y) = a2Heavy y`. -/
theorem vpLim_inv_eq_a2Heavy {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : vpLim (1 / y) = a2Heavy y := by
  have h1 : 1 < 1 / y := by rw [lt_div_iff₀ hy.1]; linarith [hy.2]
  rw [vpLim_eq_a2Heavy h1, one_div_one_div]

/-- At loop mass `1` the value is the electron value (consistency with `vpLim_one`). -/
theorem heavyIntegral_one_eq_vpLim_one : vpLim 1 = heavyIntegral 1 := by
  rw [vpLim_eq_heavyIntegral one_ne_zero, div_one]

/-! ### Decoupling and iterated limit with the closed-form target -/

/-- **Decoupling with the closed-form target.** For `1 < M_L ≤ M₁, M₂`,
`|heavyLimSum M_L M₁ M₂ - a2Heavy (1/M_L)| ≤ (1/M₁² + 1/M₂²)/45`. -/
theorem abs_heavyLimSum_sub_a2Heavy_le {ML M₁ M₂ : ℝ} (hML : 1 < ML) (h1 : ML ≤ M₁)
    (h2 : ML ≤ M₂) :
    |heavyLimSum ML M₁ M₂ - a2Heavy (1 / ML)| ≤ (1 / M₁ ^ 2 + 1 / M₂ ^ 2) / 45 := by
  rw [← vpLim_eq_a2Heavy hML]
  exact abs_heavyLimSum_sub_le (by linarith) h1 h2

/-- **The heavy-flavour VP unit tends to `A₂⁽⁴⁾(y)` in the order of D-37.4.** For `y ∈ (0,1)` and
loop mass `M_L = 1/y` (open-line mass `1`): for every `η > 0` there is `R` such that for all
`M₁, M₂ > R` there are `δ > 0` and `Λ₀` with `|heavyUnitReg (1/y) m_γ Λ M₁ M₂ - a2Heavy y| < η`
for all `m_γ ∈ (0, δ)` and `Λ > Λ₀`. -/
theorem heavyUnitReg_iterated_limit_a2Heavy {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ∀ η > 0, ∃ R : ℝ, ∀ M₁ M₂ : ℝ, R < M₁ → R < M₂ → ∃ δ > 0, ∃ Λ₀ : ℝ,
      ∀ mγ Λ : ℝ, 0 < mγ → mγ < δ → Λ₀ < Λ →
        |heavyUnitReg (1 / y) mγ Λ M₁ M₂ - a2Heavy y| < η := by
  rw [← vpLim_inv_eq_a2Heavy hy]
  exact heavyUnitReg_iterated_limit (by have := hy.1; positivity)

/-- **The same in physical units (the analytic mass-scaling step).** For an open line of mass
`m₀ > 0` and a loop lepton of mass `m_ℓ > m₀`, with all masses divided by `m₀`: for every `η > 0`
there is `R` such that for all regulator masses `M₁, M₂ > R` there are `δ > 0` and `Λ₀` with
`|heavyUnitReg (m_ℓ/m₀) (m_γ/m₀) (Λ/m₀) (M₁/m₀) (M₂/m₀) - a2Heavy (m₀/m_ℓ)| < η` for all
`m_γ ∈ (0, δ)` and `Λ > Λ₀`. -/
theorem heavyUnitReg_iterated_limit_mass {m₀ mℓ : ℝ} (hm₀ : 0 < m₀) (hmℓ : m₀ < mℓ) :
    ∀ η > 0, ∃ R : ℝ, ∀ M₁ M₂ : ℝ, R < M₁ → R < M₂ → ∃ δ > 0, ∃ Λ₀ : ℝ,
      ∀ mγ Λ : ℝ, 0 < mγ → mγ < δ → Λ₀ < Λ →
        |heavyUnitReg (mℓ / m₀) (mγ / m₀) (Λ / m₀) (M₁ / m₀) (M₂ / m₀) - a2Heavy (m₀ / mℓ)| < η := by
  have hmℓ0 : 0 < mℓ := hm₀.trans hmℓ
  have hy : m₀ / mℓ ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, (div_lt_one hmℓ0).2 hmℓ⟩
  have e : 1 / (m₀ / mℓ) = mℓ / m₀ := one_div_div m₀ mℓ
  intro η hη
  obtain ⟨R, hR⟩ := heavyUnitReg_iterated_limit_a2Heavy hy η hη
  refine ⟨R * m₀, fun M₁ M₂ h1 h2 => ?_⟩
  have h1' : R < M₁ / m₀ := by rw [lt_div_iff₀ hm₀]; exact h1
  have h2' : R < M₂ / m₀ := by rw [lt_div_iff₀ hm₀]; exact h2
  obtain ⟨δ, hδ, Λ₀, hΛ₀⟩ := hR (M₁ / m₀) (M₂ / m₀) h1' h2'
  refine ⟨δ * m₀, mul_pos hδ hm₀, Λ₀ * m₀, fun mγ Λ hm0 hm1 hΛ => ?_⟩
  have key := hΛ₀ (mγ / m₀) (Λ / m₀) (div_pos hm0 hm₀) (by rw [div_lt_iff₀ hm₀]; exact hm1)
    (by rw [lt_div_iff₀ hm₀]; exact hΛ)
  rwa [e] at key

end QED.Chain.HeavyVP
