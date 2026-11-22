/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4L
public import QED.ThreeLoopD.SetDMastersI8RemCoeff

/-!
# Set (d), master `I₈`: the coefficient `c₄` of `Rem`, and the expansion of `I₈`

`F₄ = Ψ₄ ∘ ξ` is a primitive of `p₄` on `t > 0`, continuous on `[0, ∞)`
(`QED.ThreeLoopD.hasDerivAt_i8F4`, `QED.ThreeLoopD.continuousOn_i8F4`), and `A₄` a primitive of
`a₄` (`QED.ThreeLoopD.hasDerivAt_i8Prim4`). With `F₄(0)` from the values of the harmonic
polylogarithms at `1` (`QED.ThreeLoopD.i8F4_zero`), `F₄ - A₄ → 8339/32 - 2π⁴/45 - 59π²/24 - 25ζ(3)`
and `A₄(1) = 473 - 11π² - 28ζ(3) - π⁴/45`,

  `c₄ = -F₄(0) + lim (F₄ - A₄) + A₄(1)
    = 323π⁴/120 + 62π²ζ(3)/3 - 80π² log² 2/3 + 152π² log 2 - 4259π²/24 - 763ζ(3) - 126ζ(5)
      - 64 log⁴ 2/3 - 512 Li₄(1/2) + 56307/32`.

With `c₁, c₂, c₃` this gives the expansion of the master `I₈`
(`QED.ThreeLoopD.hasTruncLaurent_setDMasterI8`).

## Main results

* `QED.ThreeLoopD.i8RemCoeff_four`.
* `QED.ThreeLoopD.hasTruncLaurent_setDMasterI8`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

theorem integrableOn_i8P4 : IntegrableOn i8P4 (Ioo (0 : ℝ) 1) := by
  have h := (integrableOn_i8Dsl_remInt1 4).re
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioo
  simp [i8Dsl_remInt1_four ht.1]

theorem integrableOn_i8P4_sub : IntegrableOn (fun t => i8P4 t - i8A4r t) (Ioi (1 : ℝ)) := by
  have h := (integrableOn_i8Dsl_remInt2 4).re
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [i8Dsl_remInt2_four (zero_lt_one.trans ht)]
  simp

theorem integral_i8P4 :
    ∫ t in Ioo (0 : ℝ) 1, i8P4 t = i8F4 1 -
      (-1026 + 126 * zeta5 + 164 * π ^ 2 + 512 * Li 4 (1 / 2) + 710 * zeta3 - 331 / 120 * π ^ 4 +
        64 / 3 * Real.log 2 ^ 4 - 152 * Real.log 2 * π ^ 2 - 62 / 3 * π ^ 2 * zeta3 +
        80 / 3 * π ^ 2 * Real.log 2 ^ 2) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      (continuousOn_i8F4.mono Icc_subset_Ici_self) (fun t ht => hasDerivAt_i8F4 ht.1)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
        (by rw [integrableOn_Ioc_iff_integrableOn_Ioo]; exact integrableOn_i8P4)), i8F4_zero]

theorem integral_i8P4_sub :
    ∫ t in Ioi (1 : ℝ), (i8P4 t - i8A4r t) =
      8339 / 32 - 25 * zeta3 - 59 / 24 * π ^ 2 - 2 / 45 * π ^ 4 - (i8F4 1 - i8Prim4 1) :=
  integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t => i8F4 t - i8Prim4 t)
    (((hasDerivAt_i8F4 one_pos).sub (hasDerivAt_i8Prim4 one_pos)).continuousAt
      |>.continuousWithinAt)
    (fun _ ht => (hasDerivAt_i8F4 (zero_lt_one.trans ht)).sub
      (hasDerivAt_i8Prim4 (zero_lt_one.trans ht)))
    integrableOn_i8P4_sub tendsto_i8F4_sub_prim4

/-- **The coefficient `c₄`.** -/
theorem i8RemCoeff_four :
    i8RemCoeff 4 = 323 / 120 * (π : ℂ) ^ 4 + 62 / 3 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
      - 80 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 + 152 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ)
      - 4259 / 24 * (π : ℂ) ^ 2 - 763 * (zeta3 : ℂ) - 126 * (zeta5 : ℂ)
      - 64 / 3 * (Real.log 2 : ℂ) ^ 4 - 512 * (Li 4 (1 / 2) : ℂ) + 56307 / 32 := by
  unfold i8RemCoeff
  rw [setIntegral_congr_fun measurableSet_Ioo fun t ht => i8Dsl_remInt1_four ht.1,
    setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) =>
      i8Dsl_remInt2_four (zero_lt_one.trans ht),
    integral_complex_ofReal, integral_complex_ofReal, integral_i8P4, integral_i8P4_sub,
    i8Prim4_one]
  push_cast
  ring

/-- **The expansion of the master `I₈`** to order `ε³`. -/
theorem hasTruncLaurent_setDMasterI8 : HasTruncLaurent setDMasterI8 setDLaurentI8 3 :=
  hasTruncLaurent_setDMasterI8_of_coeff i8RemCoeff_one i8RemCoeff_two i8RemCoeff_three
    i8RemCoeff_four

end QED.ThreeLoopD
