/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCtJetOut

/-!
# The `δ₂, δ_m` half of the self-energy unit `S`

Sections 5.2 and 7 of `docs/TWO-LOOP-UNITS.md`. The self-energy unit is the graph half plus the
two `δ₂, δ_m` counterterm classes, `sCtHalf P = (1/(64 m⁵)) (1/i) (d2InZero P + d2OutZero P)`
(`QED.TwoLoop.UnitSCReduce.sixteen_pi_pow_four_mul_unitF2_S`). This file evaluates that half in
closed form (`sixteen_pi_pow_four_mul_sCtHalf`): at `m = 1`, `0 < m_γ < Λ`, for every
`d₁ d₂ d_m d₃` and `P₁ = atUnitCharge P d₁ d₂ d_m d₃`,

`16π⁴ sCtHalf P₁ = 8π² (d₂ (V_k(m_γ) - V_k(Λ)) + d_m (V_m(m_γ) - V_m(Λ)))`,

with `V_k`, `V_m` the insertions of section 5.2 (`QED.TwoLoop.UnitSCClose.selfVk`, `selfVm`): the
Pauli–Villars difference over the internal photon mass, with `δ_doc = 4π² d` (the factor of
`QED.TwoLoop.UnitLLink.sixteen_pi_pow_four_mul_ctHalf`), each line contributing half.

The proof: the pointwise second-order coefficient of each class is `ctPoint`
(`QED.TwoLoop.UnitSCCt.d2Pointwise_In`, `d2Pointwise_Out`: Dirac traces through the base pattern
of the self-energy classes and planar jets), and its parametric integral is the one-dimensional
integral of the `V_k`, `V_m` integrands (`QED.TwoLoop.UnitSCCt.sixteen_pi_pow_four_mul_sCtHalf_of_pointwise`:
merging of the line groups, Cheng–Wu, the auxiliary-loop scale and the photon split).
-/

@[expose] public section

open Complex
open scoped Real

namespace QED.TwoLoop.UnitSCReduce

open QED.WickModel QED.TwoLoop.UnitsRegulated QED.TwoLoop.UnitSCClose QED.TwoLoop.UnitSCCt

/-- **The `δ₂, δ_m` half of the unit `S`** (`m = 1`, `0 < m_γ < Λ`, any `d₁ d₂ d_m d₃`):
`16π⁴ sCtHalf P₁ = 8π² (d₂ (V_k(m_γ) - V_k(Λ)) + d_m (V_m(m_γ) - V_m(Λ)))`. -/
theorem sixteen_pi_pow_four_mul_sCtHalf (P : Params) (hm : P.m = 1) (hmγ : 0 < P.mγ)
    (hΛ : P.mγ < P.Λ) (d₁ d₂ dm d₃ : ℝ) :
    16 * (π : ℂ) ^ 4 * sCtHalf (atUnitCharge P d₁ d₂ dm d₃) =
      ((8 * π ^ 2 * (d₂ * (selfVk P.mγ - selfVk P.Λ) + dm * (selfVm P.mγ - selfVm P.Λ)) : ℝ) :
        ℂ) :=
  sixteen_pi_pow_four_mul_sCtHalf_of_pointwise P hm hmγ hΛ d₁ d₂ dm d₃
    (d2Pointwise_In (P := atUnitCharge P d₁ d₂ dm d₃) hm rfl)
    (d2Pointwise_Out (P := atUnitCharge P d₁ d₂ dm d₃) hm rfl)

/-- **The unit `S` at finite regulators, both halves explicit** (`m = 1`, `0 < m_γ < Λ`): the
graph half of eq. (5.1) plus `8π² (d₂ ΔV_k + d_m ΔV_m)`. -/
theorem sixteen_pi_pow_four_mul_unitF2_S_explicit (P : Params) (hm : P.m = 1) (hmγ : 0 < P.mγ)
    (hΛ : P.mγ < P.Λ) (d₁ d₂ dm d₃ : ℝ) :
    16 * (π : ℂ) ^ 4 * unitF2 .S (atUnitCharge P d₁ d₂ dm d₃) =
      ((2 * ∫ Y in Set.Ioo (0 : ℝ) 1, ∫ zo in Set.Ioi (0 : ℝ), ∫ za in Set.Ioi (0 : ℝ),
          selfDocSum P Y zo za : ℝ) : ℂ) +
        ((8 * π ^ 2 * (d₂ * (selfVk P.mγ - selfVk P.Λ) + dm * (selfVm P.mγ - selfVm P.Λ)) :
          ℝ) : ℂ) := by
  rw [sixteen_pi_pow_four_mul_unitF2_S P hm hmγ hΛ d₁ d₂ dm d₃,
    sixteen_pi_pow_four_mul_sCtHalf P hm hmγ hΛ d₁ d₂ dm d₃]

end QED.TwoLoop.UnitSCReduce

end
