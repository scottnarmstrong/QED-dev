/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighSParK1

/-!
# Set (d), master `I₁₂`: the coefficient `K₂` as a one-dimensional integral

The order-2 coefficient of `K(z) = ∫₀¹ c^{-ε-1} (φ(z/c) - a (z/c)^{-3ε}) dρ` is
`K₂(z) = ∫₀¹ (ψ₂(z/c) - log c · ψ₁(z/c))/c dρ` (`i12HSQK2`; the order-0 coefficient `ψ₀`
vanishes), with `ψ₂(r) = (9/2)((1 + r)² log² (1 + r) - r² log² r)/r - 9 log² r - 9 log r`.
In `σ = 1 - ρ`, `t = 1 - σ² = 4c`, `q = 4z` (`i12HSQK2_eq_integral`):

  `K₂ = ∫₀¹ [(18/q)(B λ² + 2 L₀ X + L₀²) + (12/q)(log t - 2 log 2) f] dσ`,

`B = (q + t)²/t²`, `λ = log ((q + t)/q)`, `L₀ = log (q/t)`, `X = B λ - q/t`, `f = L₀ + X` (the
integrand of `K₁`).

## Main definitions

* `QED.ThreeLoopD.i12HSQKpsi2`, `QED.ThreeLoopD.i12HSQK2`, `QED.ThreeLoopD.i12HSQKf2`.

## Main results

* `QED.ThreeLoopD.i12HSQKpsi2_div`, `QED.ThreeLoopD.i12HSQK2_eq_integral`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ThreeLoopD

/-- `ψ₂(r) = [ε²](φ(r) - a r^{-3ε})
= (9/2)((1 + r)² log² (1 + r) - r² log² r)/r - 9 log² r - 9 log r`. -/
noncomputable def i12HSQKpsi2 (r : ℝ) : ℝ :=
  9 / 2 * ((1 + r) ^ 2 * log (1 + r) ^ 2 - r ^ 2 * log r ^ 2) / r - 9 * log r ^ 2 - 9 * log r

/-- `K₂(z) = ∫₀¹ (ψ₂(z/c) - log c · ψ₁(z/c))/c dρ`, `c = ρ(2 - ρ)/4`. -/
noncomputable def i12HSQK2 (z : ℝ) : ℝ :=
  ∫ ρ in Ioo (0 : ℝ) 1,
    (i12HSQKpsi2 (z / (ρ * (2 - ρ) / 4)) -
      log (ρ * (2 - ρ) / 4) * i12HSQKpsi (z / (ρ * (2 - ρ) / 4))) / (ρ * (2 - ρ) / 4)

/-- The reduced integrand of `K₂`. -/
noncomputable def i12HSQKf2 (q t : ℝ) : ℝ :=
  18 / q * ((q + t) ^ 2 / t ^ 2 * (log (q + t) - log q) ^ 2 +
      2 * (log q - log t) * ((q + t) ^ 2 / t ^ 2 * (log (q + t) - log q) - q / t) +
      (log q - log t) ^ 2) +
    12 / q * (log t - 2 * log 2) * i12HSQKf q t

theorem i12HSQKpsi2_div {q t : ℝ} (hq : 0 < q) (ht : 0 < t) :
    (i12HSQKpsi2 (q / t) - log (t / 4) * i12HSQKpsi (q / t)) / (t / 4) = i12HSQKf2 q t := by
  have e1 : 1 + q / t = (q + t) / t := by field_simp; ring
  have hqt : 0 < q + t := by linarith
  unfold i12HSQKpsi2 i12HSQKpsi i12HSQKf2 i12HSQKf
  rw [e1, log_div hqt.ne' ht.ne', log_div hq.ne' ht.ne', log_div ht.ne' (by norm_num : (4 : ℝ) ≠ 0),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  field_simp
  ring

/-- `K₂` in the variable `σ = 1 - ρ`. -/
theorem i12HSQK2_eq_integral {ξ : ℝ} (hξ : 1 < ξ) :
    i12HSQK2 ((ξ ^ 2 - 1) / 4) = ∫ σ in Ioo (0 : ℝ) 1, i12HSQKf2 (ξ ^ 2 - 1) (1 - σ ^ 2) := by
  have hq : 0 < ξ ^ 2 - 1 := by nlinarith
  set F : ℝ → ℝ := fun ρ =>
    (i12HSQKpsi2 ((ξ ^ 2 - 1) / 4 / (ρ * (2 - ρ) / 4)) -
      log (ρ * (2 - ρ) / 4) * i12HSQKpsi ((ξ ^ 2 - 1) / 4 / (ρ * (2 - ρ) / 4))) /
      (ρ * (2 - ρ) / 4) with hF
  have hcov : ∫ ρ in (0 : ℝ)..1, F ρ = ∫ σ in (0 : ℝ)..1, F (1 - σ) := by
    rw [intervalIntegral.integral_comp_sub_left]; norm_num
  unfold i12HSQK2
  rw [← hF, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, hcov,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun σ hσ => ?_
  have ht : 0 < 1 - σ ^ 2 := by nlinarith [hσ.1, hσ.2]
  have e : (1 - σ) * (2 - (1 - σ)) / 4 = (1 - σ ^ 2) / 4 := by ring
  have e2 : (ξ ^ 2 - 1) / 4 / ((1 - σ ^ 2) / 4) = (ξ ^ 2 - 1) / (1 - σ ^ 2) := by
    field_simp
  simp only [hF]
  rw [e, e2, i12HSQKpsi2_div hq ht]

end QED.ThreeLoopD
