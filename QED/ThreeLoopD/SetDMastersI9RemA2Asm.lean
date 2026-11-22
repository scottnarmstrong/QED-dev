/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9RemA2JV
public import QED.ThreeLoopD.SetDMastersI9RemA2Wire

/-!
# Set (d), master `I₉`: `∫ F₂` up to the `K_u` integral

`QED.ThreeLoopD.integral_i9RemF2_eq` writes `∫ F₂` as the integral of
`QED.ThreeLoopD.i9A2Dens` over the `(x, w)`-square, `QED.ThreeLoopD.integral_i9A2Dens_split`
splits it into `∫₀¹ j` and `-4 ∫∫ log (1 - w) · i9A1Dens`, and
`QED.ThreeLoopD.integral_i9A2j` evaluates `∫₀¹ j`. What remains of the expansion of `Rem` is
the single value `∫∫ log (1 - w) · i9A1Dens = (9π² + 12 ζ(3) + 17π⁴/20 - 24π² log 2)/4`.

## Main results

* `QED.ThreeLoopD.integral_i9RemF2_eq_split`: `∫ F₂ = π²/2 + 45 ζ(3) - 11π⁴/30 - 4 K`.
* `QED.ThreeLoopD.hasTruncLaurent_i9Rem_of_Ku`: the expansion of `Rem` from the value of `K`.
-/

@[expose] public section

open MeasureTheory Set Real QED.Polylog

namespace QED.ThreeLoopD

/-- **`∫ F₂ = ∫₀¹ j - 4 ∫∫ log (1 - w) · i9A1Dens`**, with `∫₀¹ j` evaluated. -/
theorem integral_i9RemF2_eq_split :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), i9RemF2 z =
      π ^ 2 / 2 + 45 * zeta3 - 11 / 30 * π ^ 4 -
        4 * ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, Real.log (1 - z.2) * i9A1Dens z := by
  have hD := integrableOn_i9A2Dens
  rw [IntegrableOn, Measure.volume_eq_prod] at hD
  rw [integral_i9RemF2_eq, ← integral_i9A2j, ← integral_i9A2Dens_split, Measure.volume_eq_prod,
    setIntegral_prod _ hD]

/-- **The expansion of `Rem` from the `K_u` integral.** -/
theorem hasTruncLaurent_i9Rem_of_Ku
    (hK : ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, Real.log (1 - z.2) * i9A1Dens z =
      (9 * π ^ 2 + 12 * zeta3 + 17 / 20 * π ^ 4 - 24 * π ^ 2 * Real.log 2) / 4) :
    HasTruncLaurent i9Rem i9RemLaurent 3 := by
  refine hasTruncLaurent_i9Rem_of_F2 ?_
  rw [integral_i9RemF2_eq_split, hK]
  ring

end QED.ThreeLoopD
