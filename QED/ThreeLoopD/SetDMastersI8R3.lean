/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R3L

/-!
# Set (d), master `I₈`: the coefficient `c₃` of `Rem`

`F₃ = Ψ₃ ∘ ξ` is a primitive of `p₃` on `t > 0`, continuous on `[0, ∞)`
(`QED.ThreeLoopD.hasDerivAt_i8F3`, `QED.ThreeLoopD.continuousOn_i8F3`), and `A₃` a primitive of
`a₃` (`QED.ThreeLoopD.hasDerivAt_i8Prim3`). With
`F₃(0) = -16π² log 2 + 25π⁴/72 + 163π²/6 + 68ζ(3) - 90`,
`F₃ - A₃ → 2003/16 - 25π²/12 - 8ζ(3)` and `A₃(1) = 131 - 7π²/3 - 4ζ(3)`,

  `c₃ = -F₃(0) + lim (F₃ - A₃) + A₃(1)
    = -25π⁴/72 + 16π² log 2 - 379π²/12 - 80ζ(3) + 5539/16`.

## Main results

* `QED.ThreeLoopD.i8RemCoeff_three`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

theorem integrableOn_i8P3 : IntegrableOn i8P3 (Ioo (0 : ℝ) 1) := by
  have h := (integrableOn_i8Dsl_remInt1 3).re
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioo
  simp [i8Dsl_remInt1_three ht.1]

theorem integrableOn_i8P3_sub : IntegrableOn (fun t => i8P3 t - i8A3r t) (Ioi (1 : ℝ)) := by
  have h := (integrableOn_i8Dsl_remInt2 3).re
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [i8Dsl_remInt2_three (zero_lt_one.trans ht)]
  simp

theorem integral_i8P3 :
    ∫ t in Ioo (0 : ℝ) 1, i8P3 t = i8F3 1 -
      (-16 * π ^ 2 * Real.log 2 + 25 * π ^ 4 / 72 + 163 * π ^ 2 / 6 + 68 * zeta3 - 90) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      (continuousOn_i8F3.mono Icc_subset_Ici_self) (fun t ht => hasDerivAt_i8F3 ht.1)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
        (by rw [integrableOn_Ioc_iff_integrableOn_Ioo]; exact integrableOn_i8P3)), i8F3_zero]

theorem integral_i8P3_sub :
    ∫ t in Ioi (1 : ℝ), (i8P3 t - i8A3r t) =
      2003 / 16 - 8 * zeta3 - 25 / 12 * π ^ 2 - (i8F3 1 - i8Prim3 1) :=
  integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t => i8F3 t - i8Prim3 t)
    (((hasDerivAt_i8F3 one_pos).sub (hasDerivAt_i8Prim3 one_pos)).continuousAt
      |>.continuousWithinAt)
    (fun _ ht => (hasDerivAt_i8F3 (zero_lt_one.trans ht)).sub
      (hasDerivAt_i8Prim3 (zero_lt_one.trans ht)))
    integrableOn_i8P3_sub tendsto_i8F3_sub_prim3

/-- **The coefficient `c₃ = -25π⁴/72 + 16π² log 2 - 379π²/12 - 80ζ(3) + 5539/16`.** -/
theorem i8RemCoeff_three :
    i8RemCoeff 3 = -25 / 72 * (π : ℂ) ^ 4 + 16 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ)
      - 379 / 12 * (π : ℂ) ^ 2 - 80 * (zeta3 : ℂ) + 5539 / 16 := by
  unfold i8RemCoeff
  rw [setIntegral_congr_fun measurableSet_Ioo fun t ht => i8Dsl_remInt1_three ht.1,
    setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) =>
      i8Dsl_remInt2_three (zero_lt_one.trans ht),
    integral_complex_ofReal, integral_complex_ofReal, integral_i8P3, integral_i8P3_sub,
    i8Prim3_one]
  push_cast
  ring

end QED.ThreeLoopD
