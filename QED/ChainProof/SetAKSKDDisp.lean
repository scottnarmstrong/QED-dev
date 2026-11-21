/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKSSpec
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# R-KS, stage D: the dispersion step and the change to the velocity `δ`

Helper level for the identification (R-KS) of the regulator limit of the frozen goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` with the Källén–Sabry function (the open
input `SetAKSFix e`). Stage D of (R-KS) ends with a once-subtracted dispersive integral over the
spectral variable `t > 4M²`, which stage S compares with `ρ⁽⁴⁾ - (3/4) L ρ_D` in the velocity
`δ`. This file provides the two generic steps:

* `ksD_log_eq_integral`: the dispersion of one logarithmic node,
  `log(1 + s/t₀) = ∫_{t₀}^∞ s/(t(s + t)) dt` for `t₀ > 0`, `s > -t₀`;
* `ksD_integral_Ioi_eq_delta`: the substitution `t = 4M²/(1-δ²)`,
  `∫_{t > 4M²} g(t) dt = ∫₀¹ 8M²δ/(1-δ²)² g(4M²/(1-δ²)) dδ`;
* `ksD_dispersion_eq_delta`: hence
  `∫_{t > 4M²} ρ(t)/t · s/(s + t) dt = ∫₀¹ ksSpecKer(s/M², δ) ρ(4M²/(1-δ²)) dδ`, the form of
  `ksS_decT_eq_spectral`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology intervalIntegral

namespace QED.ChainProof.SetAKS

/-! ### The dispersion of a logarithmic node -/

/-- The antiderivative `log(t/(s + t))` of `s/(t(s + t))`. -/
theorem ksD_hasDerivAt_logNode {s t : ℝ} (ht : 0 < t) (hst : 0 < s + t) :
    HasDerivAt (fun t : ℝ => log (t / (s + t))) (s / (t * (s + t))) t := by
  have h := ((hasDerivAt_id' t).fun_div ((hasDerivAt_id' t).const_add s) hst.ne').log
    (div_pos ht hst).ne'
  refine h.congr_deriv ?_
  field_simp
  ring

theorem ksD_tendsto_logNode (s : ℝ) :
    Tendsto (fun t : ℝ => log (t / (s + t))) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => 1 / (s / t + 1)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun t : ℝ => s / t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    simpa using (h0.add_const 1).inv₀ (by norm_num)
  have h1 : Tendsto (fun t : ℝ => t / (s + t)) atTop (𝓝 1) := by
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    field_simp
  have := (continuousAt_log one_ne_zero).tendsto.comp h1
  simpa [Function.comp_def] using this

/-- **The dispersion of a logarithmic node**: `log(1 + s/t₀) = ∫_{t > t₀} s/(t(s + t)) dt`. -/
theorem ksD_log_eq_integral {s t₀ : ℝ} (ht₀ : 0 < t₀) (hs : -t₀ < s) :
    log (1 + s / t₀) = ∫ t in Ioi t₀, s / (t * (s + t)) := by
  have hpos : ∀ t ∈ Ioi t₀, 0 < t ∧ 0 < s + t := fun t ht => by
    have : t₀ < t := ht
    exact ⟨by linarith, by linarith⟩
  have hder : ∀ t ∈ Ioi t₀, HasDerivAt (fun t : ℝ => log (t / (s + t))) (s / (t * (s + t))) t :=
    fun t ht => ksD_hasDerivAt_logNode (hpos t ht).1 (hpos t ht).2
  have hcont : ContinuousWithinAt (fun t : ℝ => log (t / (s + t))) (Ici t₀) t₀ := by
    have hst : 0 < s + t₀ := by linarith
    refine ContinuousAt.continuousWithinAt ?_
    exact ((continuousAt_id.div (continuousAt_const.add continuousAt_id) hst.ne')).log
      (div_pos ht₀ hst).ne'
  have hval : 0 - log (t₀ / (s + t₀)) = log (1 + s / t₀) := by
    have hst : 0 < s + t₀ := by linarith
    rw [zero_sub, ← log_inv, inv_div]
    congr 1
    field_simp
    ring
  rcases le_or_gt 0 s with h0 | h0
  · rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hder (fun t ht => by
      obtain ⟨a, b⟩ := hpos t ht
      positivity) (ksD_tendsto_logNode s), hval]
  · rw [integral_Ioi_of_hasDerivAt_of_nonpos hcont hder (fun t ht => by
      obtain ⟨a, b⟩ := hpos t ht
      exact div_nonpos_of_nonpos_of_nonneg h0.le (mul_pos a b).le) (ksD_tendsto_logNode s),
      hval]

/-! ### The change of variables `t = 4M²/(1-δ²)` -/

/-- The spectral variable as a function of the velocity, `T(δ) = 4M²/(1-δ²)`. -/
noncomputable def ksDT (M δ : ℝ) : ℝ := 4 * M ^ 2 / (1 - δ ^ 2)

theorem ksD_hasDerivAt_ksDT (M : ℝ) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (ksDT M) (8 * M ^ 2 * δ / (1 - δ ^ 2) ^ 2) δ := by
  have hd : 1 - δ ^ 2 ≠ 0 := by nlinarith [hδ.1, hδ.2]
  have h := (hasDerivAt_const δ (4 * M ^ 2)).fun_div ((hasDerivAt_pow 2 δ).const_sub 1) hd
  refine h.congr_deriv ?_
  push_cast
  ring

theorem ksD_image_ksDT {M : ℝ} (hM : 0 < M) : ksDT M '' Ioo 0 1 = Ioi (4 * M ^ 2) := by
  have hM2 : 0 < 4 * M ^ 2 := by positivity
  ext T
  constructor
  · rintro ⟨δ, ⟨h0, h1⟩, rfl⟩
    have hd : 0 < 1 - δ ^ 2 := by nlinarith
    have hd1 : 1 - δ ^ 2 < 1 := by nlinarith
    show 4 * M ^ 2 < 4 * M ^ 2 / (1 - δ ^ 2)
    rw [lt_div_iff₀ hd]
    nlinarith
  · intro hT
    have hT' : 4 * M ^ 2 < T := hT
    have hT0 : 0 < T := hM2.trans hT'
    have hq : 0 < 1 - 4 * M ^ 2 / T := by
      rw [sub_pos, div_lt_one hT0]
      exact hT'
    have hq1 : 1 - 4 * M ^ 2 / T < 1 := by
      have : 0 < 4 * M ^ 2 / T := div_pos hM2 hT0
      linarith
    refine ⟨sqrt (1 - 4 * M ^ 2 / T), ⟨sqrt_pos.2 hq, ?_⟩, ?_⟩
    · rw [sqrt_lt' one_pos, one_pow]
      exact hq1
    · simp only [ksDT]
      rw [sq_sqrt hq.le]
      field_simp
      ring

theorem ksD_injOn_ksDT {M : ℝ} (hM : 0 < M) : InjOn (ksDT M) (Ioo 0 1) := by
  intro δ₁ h₁ δ₂ h₂ he
  have hM2 : 4 * M ^ 2 ≠ 0 := by positivity
  have hd₁ : 1 - δ₁ ^ 2 ≠ 0 := by nlinarith [h₁.1, h₁.2]
  have hd₂ : 1 - δ₂ ^ 2 ≠ 0 := by nlinarith [h₂.1, h₂.2]
  simp only [ksDT] at he
  rw [div_eq_div_iff hd₁ hd₂] at he
  have hsq : δ₁ ^ 2 = δ₂ ^ 2 := by
    have := mul_left_cancel₀ hM2 he
    linarith
  exact (sq_eq_sq₀ h₁.1.le h₂.1.le).1 hsq

/-- **The substitution `t = 4M²/(1-δ²)`** (no integrability hypothesis: both sides are `0` when
the integrand is not integrable). -/
theorem ksD_integral_Ioi_eq_delta {M : ℝ} (hM : 0 < M) (g : ℝ → ℝ) :
    ∫ t in Ioi (4 * M ^ 2), g t =
      ∫ δ in (0 : ℝ)..1, 8 * M ^ 2 * δ / (1 - δ ^ 2) ^ 2 * g (ksDT M δ) := by
  rw [← ksD_image_ksDT hM, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun δ hδ => (ksD_hasDerivAt_ksDT M hδ).hasDerivWithinAt) (ksD_injOn_ksDT hM),
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun δ hδ => ?_
  rw [smul_eq_mul, abs_of_nonneg (by have := hδ.1; positivity)]

/-- **The once-subtracted dispersive integral in the velocity**: for `M > 0`,
`∫_{t > 4M²} ρ(t)/t · s/(s + t) dt = ∫₀¹ ksSpecKer(s/M², δ) ρ(4M²/(1-δ²)) dδ`. -/
theorem ksD_dispersion_eq_delta {M : ℝ} (hM : 0 < M) (ρ : ℝ → ℝ) (s : ℝ) :
    ∫ t in Ioi (4 * M ^ 2), ρ t / t * (s / (s + t)) =
      ∫ δ in (0 : ℝ)..1, ksSpecKer (s / M ^ 2) δ * ρ (ksDT M δ) := by
  rw [ksD_integral_Ioi_eq_delta hM]
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun δ hδ => ?_)
  rw [uIoc_of_le zero_le_one] at hδ
  obtain ⟨h0, h1⟩ := hδ
  rcases h1.lt_or_eq with h1 | rfl
  · have hd : 0 < 1 - δ ^ 2 := by nlinarith
    have hM0 : M ≠ 0 := hM.ne'
    simp only [ksSpecKer, ksDT]
    rcases eq_or_ne (s * (1 - δ ^ 2) + 4 * M ^ 2) 0 with hz | hz
    · have e1 : s + 4 * M ^ 2 / (1 - δ ^ 2) = 0 := by
        rw [show s + 4 * M ^ 2 / (1 - δ ^ 2) = (s * (1 - δ ^ 2) + 4 * M ^ 2) / (1 - δ ^ 2) by
          field_simp, hz, zero_div]
      have e2 : s / M ^ 2 + 4 / (1 - δ ^ 2) = 0 := by
        rw [show s / M ^ 2 + 4 / (1 - δ ^ 2) = (s * (1 - δ ^ 2) + 4 * M ^ 2) /
          (M ^ 2 * (1 - δ ^ 2)) by field_simp, hz, zero_div]
      rw [e1, e2]
      simp
    · have e1 : s + 4 * M ^ 2 / (1 - δ ^ 2) = (s * (1 - δ ^ 2) + 4 * M ^ 2) / (1 - δ ^ 2) := by
        field_simp
      have e2 : s / M ^ 2 + 4 / (1 - δ ^ 2) =
          (s * (1 - δ ^ 2) + 4 * M ^ 2) / (M ^ 2 * (1 - δ ^ 2)) := by
        field_simp
      rw [e1, e2]
      field_simp
      ring
  · simp [ksSpecKer, ksDT]

end QED.ChainProof.SetAKS

end
