/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXXiDilog
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The `ξ`-integration of the crossed-ladder unit, and the X link

Step 4.5.2 of `docs/TWO-LOOP-UNITS.md`, proved: for almost every `Y ∈ (0, 1)`,

`∫₀¹ Y Φ_X(Y ξ, Y (1 - ξ)) dξ = K_X(Y)` (`ae_integral_xi_eq_crossedKernel`),

with `K_X = QED.TwoLoop.Units.crossedKernel` (eq. (4.7)). Hence, by
`QED.TwoLoop.UnitXClose.xUnitLimit_of_kernel`, **the X link `XUnitLimit` holds**
(`xUnitLimit`).

## Proof

Fix `Y ∈ (0, 1)`, `Y ≠ 1/2`. The antiderivative `xiF(Y, ·)` of `QED.TwoLoop.UnitXXiDefs` has
derivative `Y Φ_X(Y ξ, Y (1 - ξ))` on `(0, 1) \ {1/2}` (`hasDerivAt_xiF`), is continuous at `1/2`
(`continuousAt_xiF`) and has the limits `xiL0 Y` at `0⁺` and `xiL1 Y` at `1⁻`
(`tendsto_xiF_zero`, `tendsto_xiF_one`). If the integrand is integrable on `(0, 1)`, which holds
for almost every `Y` by Fubini (`QED.TwoLoop.UnitXClose.integrableOn_crossedPhi`), the fundamental
theorem of calculus on `(0, 1/2)` and `(1/2, 1)` gives `∫₀¹ = xiL1 Y - xiL0 Y`
(`integral_xi_eq`). The endpoint values contain `Li` at `-Y/(1 - Y)`, `(1 - 2Y)/(1 - Y)` and
`(2Y - 1)/Y`; by the identities (4.6) of `QED.TwoLoop.UnitXXiDilog`,
`xiL1 Y - xiL0 Y = K_X(Y)` (`xiL1_sub_xiL0`), an identity checked by `field_simp` and `ring`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog

namespace QED.TwoLoop.UnitXXi

open QED.TwoLoop.UnitXClose

/-! ### The endpoint values -/

section Values

variable {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2)
include hY hY2

theorem xiU0_zero : xiU0 Y 0 = (4 * Y ^ 3 - 7 * Y ^ 2 - 3) / (12 * Y * (Y - 1) ^ 2) := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', -, -, -⟩ := xi_ne_zero_facts hY hY2 ⟨one_half_pos,
    one_half_lt_one⟩
  unfold xiU0
  field_simp
  ring

theorem xiW0_zero : xiW0 Y 0 = (52 * Y ^ 6 - 94 * Y ^ 5 - 163 * Y ^ 4 + 319 * Y ^ 3 - 133 * Y ^ 2 -
    9 * Y + 10) / (24 * Y * (Y - 1) ^ 3 * (2 * Y - 1)) := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', -, -, -⟩ := xi_ne_zero_facts hY hY2 ⟨one_half_pos,
    one_half_lt_one⟩
  unfold xiW0
  field_simp
  ring

theorem xiU1_one : xiU1 Y 1 = (-34 * Y ^ 4 + 77 * Y ^ 3 - 25 * Y ^ 2 - 9 * Y + 3) /
    (24 * Y * (Y - 1) ^ 2) := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', -, -, -⟩ := xi_ne_zero_facts hY hY2 ⟨one_half_pos,
    one_half_lt_one⟩
  unfold xiU1
  field_simp
  ring

theorem xiW1Y_one : xiW1Y Y 1 = Y * (2 * Y ^ 3 + Y ^ 2 - 32 * Y + 8) / (12 * (Y - 1) ^ 3) := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', -, -, -⟩ := xi_ne_zero_facts hY hY2 ⟨one_half_pos,
    one_half_lt_one⟩
  unfold xiW1Y
  field_simp
  ring

theorem xiW1_one : xiW1 Y 1 = (44 * Y ^ 6 - 162 * Y ^ 5 + 245 * Y ^ 4 - 274 * Y ^ 3 +
    154 * Y ^ 2 - 32 * Y + 1) / (24 * Y ^ 2 * (Y - 1) ^ 2 * (2 * Y - 1)) := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', -, -, -⟩ := xi_ne_zero_facts hY hY2 ⟨one_half_pos,
    one_half_lt_one⟩
  unfold xiW1
  field_simp
  ring

end Values

/-- **`xiL1 Y - xiL0 Y = K_X(Y)`** (eq. (4.7)), by the identities (4.6). -/
theorem xiL1_sub_xiL0 {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2) :
    xiL1 Y - xiL0 Y = QED.TwoLoop.Units.crossedKernel Y := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', -, -, -⟩ := xi_ne_zero_facts hY hY2 ⟨one_half_pos,
    one_half_lt_one⟩
  have i1 := dilogI_neg_div_one_sub hY
  have i2 := dilogI_two_mul_sub_one_div hY
  have i3 := dilogI_one_sub_two_mul_div hY
  have eD := crossedD_eq hY
  unfold xiL1 xiL0 xiDil
  rw [xiU0_zero hY hY2, xiW0_zero hY hY2, xiU1_one hY hY2, xiW1Y_one hY hY2, xiW1_one hY hY2]
  simp only [mul_zero, mul_one, sub_zero, sub_self, zero_div, neg_zero, Li₂_zero, dilogI_zero]
  rw [show (1 : ℝ) - 2 = -1 by norm_num, show (1 - 2 * Y) * -1 = 2 * Y - 1 by ring,
    Li₂_one, Li₂_neg_one, i1, i2, i3]
  unfold QED.TwoLoop.Units.crossedKernel QED.TwoLoop.Units.crossedRho
  rw [eD]
  unfold xiCL xiCq xiCD
  field_simp
  ring

/-! ### The fundamental theorem of calculus in `ξ` -/

/-- **The `ξ`-integral**, for `Y ∈ (0, 1) \ {1/2}` with an integrable integrand. -/
theorem integral_xi_eq {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2)
    (hI : IntegrableOn (fun ξ => Y * crossedPhi (Y * ξ) (Y * (1 - ξ))) (Ioo 0 1)) :
    ∫ ξ in Ioo (0 : ℝ) 1, Y * crossedPhi (Y * ξ) (Y * (1 - ξ)) = xiL1 Y - xiL0 Y := by
  set f := fun ξ => Y * crossedPhi (Y * ξ) (Y * (1 - ξ)) with hf
  have hi1 : IntervalIntegrable f volume 0 (1 / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact hI.mono_set fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  have hi2 : IntervalIntegrable f volume (1 / 2) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num),
      integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hI.mono_set fun x hx => ⟨by linarith [hx.1], hx.2⟩
  have hhalf : ContinuousAt (xiF Y) (1 / 2) := continuousAt_xiF hY ⟨by norm_num, by norm_num⟩
  have e1 : ∫ ξ in (0 : ℝ)..(1 / 2), f ξ = xiF Y (1 / 2) - xiL0 Y :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by norm_num)
      (fun ξ hξ => hasDerivAt_xiF hY hY2 ⟨hξ.1, by linarith [hξ.2]⟩ hξ.2.ne) hi1
      (tendsto_xiF_zero hY hY2) (hhalf.tendsto.mono_left nhdsWithin_le_nhds)
  have e2 : ∫ ξ in (1 / 2 : ℝ)..1, f ξ = xiL1 Y - xiF Y (1 / 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by norm_num)
      (fun ξ hξ => hasDerivAt_xiF hY hY2 ⟨by linarith [hξ.1], hξ.2⟩ hξ.1.ne') hi2
      (hhalf.tendsto.mono_left nhdsWithin_le_nhds) (tendsto_xiF_one hY hY2)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, e1, e2]
  ring

/-! ### Almost every `Y`, and the X link -/

/-- For almost every `Y ∈ (0, 1)` the integrand is integrable in `ξ` on `(0, 1)` (Fubini). -/
theorem ae_integrableOn_xi :
    ∀ᵐ Y ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      IntegrableOn (fun ξ => Y * crossedPhi (Y * ξ) (Y * (1 - ξ))) (Ioo 0 1) := by
  have h := (integrableOn_triangle_iff (fun p : ℝ × ℝ => crossedPhi p.1 p.2)).mp
    integrableOn_crossedPhi
  rw [unitSquare, Measure.volume_eq_prod, IntegrableOn, ← Measure.prod_restrict] at h
  filter_upwards [h.prod_right_ae] with Y hY
  refine hY.congr (Eventually.of_forall fun ξ => ?_)
  simp only [yxiMap]
  ring_nf

/-- **The `ξ`-integration (step 4.5.2)**: for almost every `Y ∈ (0, 1)`,
`∫₀¹ Y Φ_X(Y ξ, Y (1 - ξ)) dξ = K_X(Y)`. -/
theorem ae_integral_xi_eq_crossedKernel :
    ∀ᵐ Y ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ∫ ξ in Ioo (0 : ℝ) 1, Y * crossedPhi (Y * ξ) (Y * (1 - ξ)) =
        QED.TwoLoop.Units.crossedKernel Y := by
  have hne : ∀ᵐ Y ∂(volume.restrict (Ioo (0 : ℝ) 1)), Y ≠ 1 / 2 :=
    ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton (1 / 2 : ℝ)))
  filter_upwards [ae_integrableOn_xi, hne, ae_restrict_mem measurableSet_Ioo] with Y hI hY2 hY
  rw [integral_xi_eq hY hY2 hI, xiL1_sub_xiL0 hY hY2]

/-- **The X link**: `XUnitLimit` holds. -/
theorem xUnitLimit : QED.TwoLoop.HeadlineAssembly.XUnitLimit :=
  xUnitLimit_of_kernel ae_integral_xi_eq_crossedKernel

end QED.TwoLoop.UnitXXi

end
