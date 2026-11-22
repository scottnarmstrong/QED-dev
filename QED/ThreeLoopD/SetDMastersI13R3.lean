/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13R3L

/-!
# Set (d), master `I₁₃`: the coefficient `c₃ = -π⁴/90 - 47π²/12 + 12ζ(3) - 97/16` of `Rem`

The third Taylor coefficients of the integrands of `Rem` are `p₃` on `(0, 1)` and `p₃ - a₃` on
`(1, ∞)` (`QED.ThreeLoopD.i13Dsl_remInt1_three`, `QED.ThreeLoopD.i13Dsl_remInt2_three`), with
primitives `F₃` of `p₃` and `A₃` of `a₃`. As for `c₁` and `c₂`,

  `c₃ = (F₃(1) - F₃(0)) + (lim_{t→∞} (F₃ - A₃) - F₃(1) + A₃(1))`,

and `F₃(1)` cancels. With `F₃(0) = π⁴/90 - 26ζ(3) - 33/8` (`QED.ThreeLoopD.i13F3_zero`), the limit
`π²/3 - 4ζ(3) - 843/8` (`QED.ThreeLoopD.tendsto_i13F3_sub_prim3`) and
`A₃(1) = 1523/16 - 17π²/4 - 10ζ(3)` (`QED.ThreeLoopD.i13Prim3_one`),

  `c₃ = -π⁴/90 - 47π²/12 + 12ζ(3) - 97/16`.

## Main results

* `QED.ThreeLoopD.i13RemCoeff_three`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

theorem integrableOn_i13P3 : IntegrableOn i13P3 (Ioo (0 : ℝ) 1) := by
  have h := (integrableOn_i13Dsl_remInt1 3).re
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioo
  simp [i13Dsl_remInt1_three ht.1]

theorem integrableOn_i13P3_sub : IntegrableOn (fun t => i13P3 t - i13A3r t) (Ioi (1 : ℝ)) := by
  have h := (integrableOn_i13Dsl_remInt2 3).re
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [i13Dsl_remInt2_three (zero_lt_one.trans ht)]
  simp

theorem integral_i13P3 :
    ∫ t in Ioo (0 : ℝ) 1, i13P3 t = i13F3 1 - (π ^ 4 / 90 - 26 * zeta3 - 33 / 8) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      (continuousOn_i13F3.mono Icc_subset_Ici_self) (fun t ht => hasDerivAt_i13F3 ht.1)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
        (by rw [integrableOn_Ioc_iff_integrableOn_Ioo]; exact integrableOn_i13P3)), i13F3_zero]

theorem integral_i13P3_sub :
    ∫ t in Ioi (1 : ℝ), (i13P3 t - i13A3r t) =
      -843 / 8 - 4 * zeta3 + π ^ 2 / 3 - (i13F3 1 - i13Prim3 1) :=
  integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t => i13F3 t - i13Prim3 t)
    (((hasDerivAt_i13F3 one_pos).sub (hasDerivAt_i13Prim3 one_pos)).continuousAt
      |>.continuousWithinAt)
    (fun _ ht => (hasDerivAt_i13F3 (zero_lt_one.trans ht)).sub
      (hasDerivAt_i13Prim3 (zero_lt_one.trans ht)))
    integrableOn_i13P3_sub tendsto_i13F3_sub_prim3

/-- **The coefficient `c₃ = -π⁴/90 - 47π²/12 + 12ζ(3) - 97/16`.** -/
theorem i13RemCoeff_three :
    i13RemCoeff 3 = -1 / 90 * (π : ℂ) ^ 4 - 47 / 12 * (π : ℂ) ^ 2 + 12 * (zeta3 : ℂ) - 97 / 16 := by
  unfold i13RemCoeff
  rw [setIntegral_congr_fun measurableSet_Ioo fun t ht => i13Dsl_remInt1_three ht.1,
    setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) =>
      i13Dsl_remInt2_three (zero_lt_one.trans ht),
    integral_complex_ofReal, integral_complex_ofReal, integral_i13P3, integral_i13P3_sub,
    i13Prim3_one]
  push_cast
  ring

end QED.ThreeLoopD
