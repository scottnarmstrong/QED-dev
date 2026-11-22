/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13R4L
public import QED.ThreeLoopD.SetDMastersI13RemCoeff

/-!
# Set (d), master `I₁₃`: the coefficient `c₄` of `Rem` and the expansion of the master

The fourth Taylor coefficients of the integrands of `Rem` are `p₄` on `(0, 1)` and `p₄ - a₄` on
`(1, ∞)` (`QED.ThreeLoopD.i13Dsl_remInt1_four`, `QED.ThreeLoopD.i13Dsl_remInt2_four`), with
primitives `F₄` of `p₄` and `A₄` of `a₄`. As for `c₁, c₂, c₃`,

  `c₄ = (F₄(1) - F₄(0)) + (lim_{t→∞} (F₄ - A₄) - F₄(1) + A₄(1))`,

and `F₄(1)` cancels. With `F₄(0)` (`QED.ThreeLoopD.i13F4_zero`), the limit
`4π⁴/45 - 5π²/12 + 4ζ(3) - 1771/16` (`QED.ThreeLoopD.tendsto_i13F4_sub_prim4`) and
`A₄(1) = 13273/32 - 139π²/8 - 51ζ(3)` (`QED.ThreeLoopD.i13Prim4_one`),

  `c₄ = -133π⁴/45 + 2π²ζ(3)/3 - 32π² log² 2/3 - 427π²/24 + 176ζ(3) - 12ζ(5) + 32 log⁴ 2/3
    + 256 Li₄(1/2) + 841/32`

(`QED.ThreeLoopD.i13RemCoeff_four`). With `c₁, c₂, c₃` this gives the expansion of the master
`I₁₃` through `ε³` (`QED.ThreeLoopD.hasTruncLaurent_setDMasterI13`).

## Main results

* `QED.ThreeLoopD.i13RemCoeff_four`.
* `QED.ThreeLoopD.hasTruncLaurent_setDMasterI13`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

theorem integrableOn_i13P4 : IntegrableOn i13P4 (Ioo (0 : ℝ) 1) := by
  have h := (integrableOn_i13Dsl_remInt1 4).re
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioo
  simp [i13Dsl_remInt1_four ht.1]

theorem integrableOn_i13P4_sub : IntegrableOn (fun t => i13P4 t - i13A4r t) (Ioi (1 : ℝ)) := by
  have h := (integrableOn_i13Dsl_remInt2 4).re
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [i13Dsl_remInt2_four (zero_lt_one.trans ht)]
  simp

theorem integral_i13P4 :
    ∫ t in Ioo (0 : ℝ) 1, i13P4 t = i13F4 1 - (4445 / 16 - 256 * Li 4 (1 / 2) - 223 * zeta3 +
      12 * zeta5 - 32 / 3 * Real.log 2 ^ 4 + 137 / 45 * π ^ 4 - 2 / 3 * π ^ 2 * zeta3 +
      32 / 3 * π ^ 2 * Real.log 2 ^ 2) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      (continuousOn_i13F4.mono Icc_subset_Ici_self) (fun t ht => hasDerivAt_i13F4 ht.1)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
        (by rw [integrableOn_Ioc_iff_integrableOn_Ioo]; exact integrableOn_i13P4)), i13F4_zero]

theorem integral_i13P4_sub :
    ∫ t in Ioi (1 : ℝ), (i13P4 t - i13A4r t) =
      -1771 / 16 + 4 * zeta3 - 5 * π ^ 2 / 12 + 4 * π ^ 4 / 45 - (i13F4 1 - i13Prim4 1) :=
  integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t => i13F4 t - i13Prim4 t)
    (((hasDerivAt_i13F4 one_pos).sub (hasDerivAt_i13Prim4 one_pos)).continuousAt
      |>.continuousWithinAt)
    (fun _ ht => (hasDerivAt_i13F4 (zero_lt_one.trans ht)).sub
      (hasDerivAt_i13Prim4 (zero_lt_one.trans ht)))
    integrableOn_i13P4_sub tendsto_i13F4_sub_prim4

/-- **The coefficient `c₄`** of `Rem`. -/
theorem i13RemCoeff_four :
    i13RemCoeff 4 = -133 / 45 * (π : ℂ) ^ 4 + 2 / 3 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
      - 32 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 - 427 / 24 * (π : ℂ) ^ 2 + 176 * (zeta3 : ℂ)
      - 12 * (zeta5 : ℂ) + 32 / 3 * (Real.log 2 : ℂ) ^ 4 + 256 * (Li 4 (1 / 2) : ℂ) + 841 / 32 := by
  unfold i13RemCoeff
  rw [setIntegral_congr_fun measurableSet_Ioo fun t ht => i13Dsl_remInt1_four ht.1,
    setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) =>
      i13Dsl_remInt2_four (zero_lt_one.trans ht),
    integral_complex_ofReal, integral_complex_ofReal, integral_i13P4, integral_i13P4_sub,
    i13Prim4_one]
  push_cast
  ring

/-- **The master `I₁₃`**: `I₁₃ C⁻¹` has the LR96 expansion through `ε³`. -/
theorem hasTruncLaurent_setDMasterI13 : HasTruncLaurent setDMasterI13 setDLaurentI13 3 :=
  hasTruncLaurent_setDMasterI13_of_coeff i13RemCoeff_one i13RemCoeff_two i13RemCoeff_three
    i13RemCoeff_four

end QED.ThreeLoopD
