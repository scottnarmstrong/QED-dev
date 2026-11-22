/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13R2L

/-!
# Set (d), master `I₁₃`: the coefficient `c₂ = -7π²/6 - 4ζ(3) - 47/8` of `Rem`

The second Taylor coefficients of the integrands of `Rem` are `p₂` on `(0, 1)` and `p₂ - a₂` on
`(1, ∞)` (`QED.ThreeLoopD.i13Dsl_remInt1_two`, `QED.ThreeLoopD.i13Dsl_remInt2_two`), with
primitives `F₂` of `p₂` and `A₂` of `a₂`. As for `c₁`,

  `c₂ = (F₂(1) - F₂(0)) + (lim_{t→∞} (F₂ - A₂) - F₂(1) + A₂(1))`,

and `F₂(1)` cancels. With `F₂(0) = 4ζ(3) + 16` (`QED.ThreeLoopD.i13F2_zero`), the limit
`-8 - π²/3` (`QED.ThreeLoopD.tendsto_i13F2_sub_prim2`) and `A₂(1) = 145/8 - 5π²/6`,

  `c₂ = -4ζ(3) - 16 - 8 - π²/3 + 145/8 - 5π²/6 = -7π²/6 - 4ζ(3) - 47/8`.

## Main results

* `QED.ThreeLoopD.i13RemCoeff_two`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

theorem integrableOn_i13P2 : IntegrableOn i13P2 (Ioo (0 : ℝ) 1) := by
  have h := (integrableOn_i13Dsl_remInt1 2).re
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioo
  simp [i13Dsl_remInt1_two ht.1]

theorem integrableOn_i13P2_sub : IntegrableOn (fun t => i13P2 t - i13A2r t) (Ioi (1 : ℝ)) := by
  have h := (integrableOn_i13Dsl_remInt2 2).re
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [i13Dsl_remInt2_two (zero_lt_one.trans ht)]
  simp

theorem integral_i13P2 : ∫ t in Ioo (0 : ℝ) 1, i13P2 t = i13F2 1 - (4 * zeta3 + 16) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      (continuousOn_i13F2.mono Icc_subset_Ici_self) (fun t ht => hasDerivAt_i13F2 ht.1)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
        (by rw [integrableOn_Ioc_iff_integrableOn_Ioo]; exact integrableOn_i13P2)), i13F2_zero]

theorem integral_i13P2_sub :
    ∫ t in Ioi (1 : ℝ), (i13P2 t - i13A2r t) = -8 - π ^ 2 / 3 - (i13F2 1 - i13Prim2 1) :=
  integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t => i13F2 t - i13Prim2 t)
    (((hasDerivAt_i13F2 one_pos).sub (hasDerivAt_i13Prim2 one_pos)).continuousAt
      |>.continuousWithinAt)
    (fun _ ht => (hasDerivAt_i13F2 (zero_lt_one.trans ht)).sub
      (hasDerivAt_i13Prim2 (zero_lt_one.trans ht)))
    integrableOn_i13P2_sub tendsto_i13F2_sub_prim2

theorem i13Prim2_one : i13Prim2 1 = 145 / 8 - 5 * π ^ 2 / 6 := by
  unfold i13Prim2
  norm_num
  ring

/-- **The coefficient `c₂ = -7π²/6 - 4ζ(3) - 47/8`.** -/
theorem i13RemCoeff_two : i13RemCoeff 2 = -7 / 6 * (π : ℂ) ^ 2 - 4 * (zeta3 : ℂ) - 47 / 8 := by
  unfold i13RemCoeff
  rw [setIntegral_congr_fun measurableSet_Ioo fun t ht => i13Dsl_remInt1_two ht.1,
    setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) =>
      i13Dsl_remInt2_two (zero_lt_one.trans ht),
    integral_complex_ofReal, integral_complex_ofReal, integral_i13P2, integral_i13P2_sub,
    i13Prim2_one]
  push_cast
  ring

end QED.ThreeLoopD
