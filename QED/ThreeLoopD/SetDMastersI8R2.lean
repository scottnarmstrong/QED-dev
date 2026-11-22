/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R2L

/-!
# Set (d), master `I₈`: the coefficient `c₂ = 491/8 - 13π²/3 + 2ζ(3)` of `Rem`

`F₂ = Ψ₂ ∘ ξ` is a primitive of `p₂` on `t > 0`, continuous on `[0, ∞)`
(`QED.ThreeLoopD.hasDerivAt_i8F2`, `QED.ThreeLoopD.continuousOn_i8F2`), and `A₂` a primitive of
`a₂` (`QED.ThreeLoopD.hasDerivAt_i8Prim2`). With `F₂(0) = 12 + 10π²/3 - 2ζ(3)`,
`F₂ - A₂ → 323/8 - 2π²/3` and `A₂(1) = 33 - π²/3`,

  `c₂ = ∫₀¹ p₂ + ∫₁^∞ (p₂ - a₂) = -F₂(0) + lim (F₂ - A₂) + A₂(1) = 491/8 - 13π²/3 + 2ζ(3)`.

## Main results

* `QED.ThreeLoopD.i8RemCoeff_two`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

theorem integrableOn_i8P2 : IntegrableOn i8P2 (Ioo (0 : ℝ) 1) := by
  have h := (integrableOn_i8Dsl_remInt1 2).re
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioo
  simp [i8Dsl_remInt1_two ht.1]

theorem integrableOn_i8P2_sub : IntegrableOn (fun t => i8P2 t - i8A2r t) (Ioi (1 : ℝ)) := by
  have h := (integrableOn_i8Dsl_remInt2 2).re
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [i8Dsl_remInt2_two (zero_lt_one.trans ht)]
  simp

theorem integral_i8P2 :
    ∫ t in Ioo (0 : ℝ) 1, i8P2 t = i8F2 1 - (12 + 10 * π ^ 2 / 3 - 2 * zeta3) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      (continuousOn_i8F2.mono Icc_subset_Ici_self) (fun t ht => hasDerivAt_i8F2 ht.1)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
        (by rw [integrableOn_Ioc_iff_integrableOn_Ioo]; exact integrableOn_i8P2)), i8F2_zero]

theorem integral_i8P2_sub :
    ∫ t in Ioi (1 : ℝ), (i8P2 t - i8A2r t) =
      323 / 8 - 2 / 3 * π ^ 2 - (i8F2 1 - i8Prim2 1) :=
  integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t => i8F2 t - i8Prim2 t)
    (((hasDerivAt_i8F2 one_pos).sub (hasDerivAt_i8Prim2 one_pos)).continuousAt
      |>.continuousWithinAt)
    (fun _ ht => (hasDerivAt_i8F2 (zero_lt_one.trans ht)).sub
      (hasDerivAt_i8Prim2 (zero_lt_one.trans ht)))
    integrableOn_i8P2_sub tendsto_i8F2_sub_prim2

/-- **The coefficient `c₂ = 491/8 - 13π²/3 + 2ζ(3)`.** -/
theorem i8RemCoeff_two :
    i8RemCoeff 2 = -13 / 3 * (π : ℂ) ^ 2 + 2 * (zeta3 : ℂ) + 491 / 8 := by
  unfold i8RemCoeff
  rw [setIntegral_congr_fun measurableSet_Ioo fun t ht => i8Dsl_remInt1_two ht.1,
    setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) =>
      i8Dsl_remInt2_two (zero_lt_one.trans ht),
    integral_complex_ofReal, integral_complex_ofReal, integral_i8P2, integral_i8P2_sub,
    i8Prim2_one]
  push_cast
  ring

end QED.ThreeLoopD
