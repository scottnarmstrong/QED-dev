/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKSDer

/-!
# R-KS, stage A: `SetAKSFix e` from the spectral form of `decT₀`

Helper level for the identification (R-KS) of the regulator limit of the frozen goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` with the Källén–Sabry function (the open
input `SetAKSFix e`). Stage D of (R-KS) is to produce the per-flavour limit `decT₀ e μ x s` as a
once-subtracted dispersive integral in the velocity `δ`, over some density `ρ μ x δ`, plus a part
affine in `x` (`KsSpecForm e ρ`). Stage S identifies `ρ μ x` with the target density
`ρ_L = ρ⁽⁴⁾ - (3/4) log(x/μ²) ρ_D` on `(0, 1)`. This file assembles the two into `SetAKSFix e`.

Main results:

* `KsSpecForm e ρ`: the output statement of stage D;
* `ksA_setAKSFix_of_eqOn`: `KsSpecForm e ρ` and `ρ μ x = ρ_L` on `(0, 1)` give `SetAKSFix e`;
* `ksA_setAKSFix_of_deriv`: the same, with stage S in its derivative form (the derivative of
  `ρ μ x` on `(0, 1)` and its limit at `1⁻`).
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology intervalIntegral

namespace QED.ChainProof.SetAKS

open QED.GradedProof.RPi4

/-- **The output statement of stage D**: the per-flavour limit `decT₀ e μ x s` is the
once-subtracted dispersive integral of the density `ρ μ x` (in the velocity `δ`, at
`σ = s/x`), over `16π⁴`, plus a part affine in `x`. -/
def KsSpecForm (e : ℝ) (ρ : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∃ α β : ℝ → ℝ → ℂ, ∀ μ x s : ℝ, 0 < μ → μ ^ 2 ≤ x → -(4 * μ ^ 2) < s →
    decT₀ e μ x s = (((∫ δ in (0 : ℝ)..1, ksSpecKer (s / x) δ * ρ μ x δ) /
      (16 * π ^ 4) : ℝ) : ℂ) + (α μ s + β μ s * x)

theorem ksA_neg_four_lt_div {μ x s : ℝ} (hμ : 0 < μ) (hx : μ ^ 2 ≤ x)
    (hs : -(4 * μ ^ 2) < s) : -4 < s / x := by
  have hx0 : 0 < x := (by positivity : 0 < μ ^ 2).trans_le hx
  rw [lt_div_iff₀ hx0]
  linarith

/-- Two densities equal on `(0, 1)` have the same dispersive integral. -/
theorem ksA_integral_congr {σ : ℝ} {ρ ρ' : ℝ → ℝ} (h : EqOn ρ ρ' (Ioo 0 1)) :
    ∫ δ in (0 : ℝ)..1, ksSpecKer σ δ * ρ δ = ∫ δ in (0 : ℝ)..1, ksSpecKer σ δ * ρ' δ := by
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo fun δ hδ => by rw [h hδ]

/-- **Stage A**: the spectral form of stage D with the density identity of stage S gives
`SetAKSFix e`. -/
theorem ksA_setAKSFix_of_eqOn {e : ℝ} {ρ : ℝ → ℝ → ℝ → ℝ} (hD : KsSpecForm e ρ)
    (hS : ∀ μ x : ℝ, 0 < μ → μ ^ 2 ≤ x →
      EqOn (ρ μ x) (ksSpecRho (log (x / μ ^ 2))) (Ioo 0 1)) :
    SetAKSFix e := by
  obtain ⟨α, β, hT⟩ := hD
  refine ⟨α, β, fun μ x s hμ hx hs => ?_⟩
  rw [hT μ x s hμ hx hs, ksS_decT_eq_spectral (ksA_neg_four_lt_div hμ hx hs),
    ksA_integral_congr (hS μ x hμ hx)]

/-- **Stage A with stage S in derivative form**: if the density of stage D has, at every
`μ > 0`, `x ≥ μ²`, the derivative `ksSpecRhoDer (log(x/μ²))` on `(0, 1)` and the same limit
at `1⁻` as the target density, then `SetAKSFix e`. -/
theorem ksA_setAKSFix_of_deriv {e : ℝ} {ρ : ℝ → ℝ → ℝ → ℝ} (hD : KsSpecForm e ρ)
    (hρ : ∀ μ x : ℝ, 0 < μ → μ ^ 2 ≤ x → ∀ δ ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (ρ μ x) (ksSpecRhoDer (log (x / μ ^ 2)) δ) δ)
    (hlim : ∀ μ x : ℝ, 0 < μ → μ ^ 2 ≤ x →
      Tendsto (fun δ => ρ μ x δ - ksSpecRho (log (x / μ ^ 2)) δ) (𝓝[<] 1) (𝓝 0)) :
    SetAKSFix e :=
  ksA_setAKSFix_of_eqOn hD fun μ x hμ hx => ksS_eqOn_ksSpecRho (hρ μ x hμ hx) (hlim μ x hμ hx)

end QED.ChainProof.SetAKS

end
