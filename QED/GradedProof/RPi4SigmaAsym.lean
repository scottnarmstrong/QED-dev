/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4PhotonMass

/-!
# (R-Π₄) step L6d (M): the heavy-photon asymptotics of the mass-insertion density

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), item (M) of step L6d. The
mass-insertion density `σ(u) = -(e²/8π²) ∫₀¹ (1 - x²)/(x² m² + (1 - x) u) dx`
(`QED.GradedProof.RPi4.sigma`) behaves like `-3e²/(16π² u)` for a heavy photon:

* `sigma_add_eq`: `σ(u) + 3e²/(16π² u) = (e²/(8π² u)) ∫₀¹ (1 + x) x² m²/(x² m² + (1 - x) u) dx`;
* `abs_sigma_add_le`: `|σ(u) + 3e²/(16π² u)| ≤ e² m² log(1 + u/m²)/(4π² u²)`.

In the units of the face coefficients, `-3e²/(16π²) = -3e²κ` with `κ = 1/(16π²)`: the mass
insertion cancels the `3κ M` part of the self-energy faces.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

/-- The pointwise split of the integrand of `σ`. -/
theorem sigma_integrand_split {m x u : ℝ} (hm : m ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) (hu : 0 < u) :
    (1 - x ^ 2) / (x ^ 2 * m ^ 2 + (1 - x) * u) =
      (1 + x) / u - (1 + x) * x ^ 2 * m ^ 2 / (u * (x ^ 2 * m ^ 2 + (1 - x) * u)) := by
  have hD := (onShell_denom_pos hm hx hu).ne'
  field_simp
  ring

/-- **The leading term of `σ`**: `σ(u) + 3e²/(16π² u)` is an explicit positive remainder. -/
theorem sigma_add_eq (e : ℝ) {m u : ℝ} (hm : m ≠ 0) (hu : 0 < u) :
    sigma e m u + 3 * e ^ 2 / (16 * π ^ 2 * u) =
      e ^ 2 / (8 * π ^ 2 * u) *
        ∫ x in (0 : ℝ)..1, (1 + x) * x ^ 2 * m ^ 2 / (x ^ 2 * m ^ 2 + (1 - x) * u) := by
  have hc1 : ContinuousOn (fun x : ℝ => (1 + x) / u) (uIcc 0 1) := by fun_prop
  have hc2 : ContinuousOn (fun x : ℝ =>
      (1 + x) * x ^ 2 * m ^ 2 / (u * (x ^ 2 * m ^ 2 + (1 - x) * u))) (uIcc 0 1) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    exact mul_ne_zero hu.ne' (onShell_denom_pos hm hx hu).ne'
  have hsplit : ∫ x in (0 : ℝ)..1, (1 - x ^ 2) / (x ^ 2 * m ^ 2 + (1 - x) * u) =
      (∫ x in (0 : ℝ)..1, (1 + x) / u) -
        ∫ x in (0 : ℝ)..1, (1 + x) * x ^ 2 * m ^ 2 / (u * (x ^ 2 * m ^ 2 + (1 - x) * u)) := by
    rw [← intervalIntegral.integral_sub hc1.intervalIntegrable hc2.intervalIntegrable]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    exact sigma_integrand_split hm hx hu
  have h1 : ∫ x in (0 : ℝ)..1, (1 + x) / u = 3 / (2 * u) := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id, intervalIntegral.integral_const, integral_id]
    field_simp
    ring
  have h2 : ∫ x in (0 : ℝ)..1, (1 + x) * x ^ 2 * m ^ 2 / (u * (x ^ 2 * m ^ 2 + (1 - x) * u)) =
      u⁻¹ * ∫ x in (0 : ℝ)..1, (1 + x) * x ^ 2 * m ^ 2 / (x ^ 2 * m ^ 2 + (1 - x) * u) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [mul_div_assoc', div_mul_eq_div_div, inv_mul_eq_div]
  rw [sigma, hsplit, h1, h2]
  generalize (∫ x in (0 : ℝ)..1, (1 + x) * x ^ 2 * m ^ 2 / (x ^ 2 * m ^ 2 + (1 - x) * u)) = J
  field_simp
  ring

/-- `∫₀¹ m²/(m² + (1 - x) u) dx = (m²/u) log(1 + u/m²)`. -/
theorem integral_onShell_tail {m u : ℝ} (hm : m ≠ 0) (hu : 0 < u) :
    ∫ x in (0 : ℝ)..1, m ^ 2 / (m ^ 2 + (1 - x) * u) = m ^ 2 / u * Real.log (1 + u / m ^ 2) := by
  have hm2 : 0 < m ^ 2 := by positivity
  have hpos : ∀ x ∈ uIcc (0 : ℝ) 1, 0 < (m ^ 2 + u) + (-u) * x := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    nlinarith [hx.2]
  have hlog := log_sub_log_eq_integral hpos
  have hL : Real.log ((m ^ 2 + u) + -u * 1) - Real.log ((m ^ 2 + u) + -u * 0) =
      -Real.log (1 + u / m ^ 2) := by
    rw [show (m ^ 2 + u) + -u * 1 = m ^ 2 by ring,
      show (m ^ 2 + u) + -u * 0 = m ^ 2 * (1 + u / m ^ 2) by field_simp; ring,
      Real.log_mul hm2.ne' (by positivity)]
    ring
  rw [hL] at hlog
  have : ∫ x in (0 : ℝ)..1, m ^ 2 / (m ^ 2 + (1 - x) * u) =
      -(m ^ 2 / u) * ∫ x in (0 : ℝ)..1, -u / ((m ^ 2 + u) + -u * x) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    have := (hpos x hx).ne'
    field_simp
    ring_nf
  rw [this, ← hlog]
  ring

/-- **The heavy-photon bound of the mass-insertion density**:
`|σ(u) + 3e²/(16π² u)| ≤ e² m² log(1 + u/m²)/(4π² u²)`. -/
theorem abs_sigma_add_le (e : ℝ) {m u : ℝ} (hm : m ≠ 0) (hu : 0 < u) :
    |sigma e m u + 3 * e ^ 2 / (16 * π ^ 2 * u)| ≤
      e ^ 2 * m ^ 2 / (4 * π ^ 2 * u ^ 2) * Real.log (1 + u / m ^ 2) := by
  have hm2 : 0 < m ^ 2 := by positivity
  set I := ∫ x in (0 : ℝ)..1, (1 + x) * x ^ 2 * m ^ 2 / (x ^ 2 * m ^ 2 + (1 - x) * u)
  have hcont : ContinuousOn (fun x : ℝ => (1 + x) * x ^ 2 * m ^ 2 /
      (x ^ 2 * m ^ 2 + (1 - x) * u)) (uIcc 0 1) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    exact (onShell_denom_pos hm hx hu).ne'
  have hcont2 : ContinuousOn (fun x : ℝ => 2 * (m ^ 2 / (m ^ 2 + (1 - x) * u))) (uIcc 0 1) := by
    refine continuousOn_const.mul (ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_)
    rw [uIcc_of_le zero_le_one] at hx
    nlinarith [hx.2]
  have hI0 : 0 ≤ I := by
    refine intervalIntegral.integral_nonneg zero_le_one fun x hx => ?_
    have := onShell_denom_pos hm hx hu
    have : 0 ≤ 1 + x := by linarith [hx.1]
    positivity
  have hI : I ≤ 2 * (m ^ 2 / u * Real.log (1 + u / m ^ 2)) := by
    rw [← integral_onShell_tail hm hu, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on zero_le_one hcont.intervalIntegrable
      hcont2.intervalIntegrable fun x hx => ?_
    have hD := onShell_denom_pos hm hx hu
    have hD' : 0 < m ^ 2 + (1 - x) * u := by nlinarith [hx.2]
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
    have h1x : 1 + x ≤ 2 := by linarith [hx.2]
    rw [div_le_iff₀ hD, mul_assoc]
    rw [mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hD']
    have hc : 0 ≤ (1 - x) * u := mul_nonneg (by linarith [hx.2]) hu.le
    have : 0 ≤ x ^ 2 * m ^ 2 := by positivity
    nlinarith [mul_nonneg (mul_nonneg hc hm2.le) (sub_nonneg.mpr hx2), mul_le_mul_of_nonneg_right
      h1x (mul_nonneg this hD'.le)]
  rw [sigma_add_eq e hm hu, abs_of_nonneg (by positivity)]
  have he : 0 ≤ e ^ 2 / (8 * π ^ 2 * u) := by positivity
  calc e ^ 2 / (8 * π ^ 2 * u) * I ≤ e ^ 2 / (8 * π ^ 2 * u) *
        (2 * (m ^ 2 / u * Real.log (1 + u / m ^ 2))) := mul_le_mul_of_nonneg_left hI he
    _ = _ := by field_simp; ring

end QED.GradedProof.RPi4

end
