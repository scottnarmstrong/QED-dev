/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCornerXiLimits
public import QED.TwoLoop.UnitXXiDilog
public import QED.TwoLoop.UnitC
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The `ξ`-integration of the corner unit

Step 6.6.2 of `docs/TWO-LOOP-UNITS.md`: for `Y ∈ (0, 1)`, `Y ≠ 1/2`, if `ξ ↦ Y Φ_C(Y, ξ)` is
integrable on `(0, 1)` then

`∫₀¹ Y Φ_C(Y, ξ) dξ = K_C(Y)` (`integral_cornerPhi_eq_cornerKernel`),

with `Φ_C = QED.TwoLoop.UnitSCCorner.cornerPhi` (eq. (6.7)) and `K_C =
QED.TwoLoop.Units.cornerKernel`
(eq. (6.10)). As for X (`QED.TwoLoop.UnitXXiKernel`): the antiderivative `cxiF(Y, ·)` has derivative
`Y Φ_C(Y, ·)` off `ξ = 1/2`, is continuous at `1/2` and has the limits `cxiL0 Y`, `cxiL1 Y` at the
endpoints; by the identities (4.6) (`QED.TwoLoop.UnitXXiDilog`), `cxiL1 Y - cxiL0 Y = K_C(Y)`
(`cxiL1_sub_cxiL0`), checked by `field_simp` and `ring`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog

namespace QED.TwoLoop.UnitSCCornerXi

open QED.TwoLoop.UnitXClose QED.TwoLoop.UnitXXi QED.TwoLoop.UnitSCCorner

/-! ### The endpoint values -/

section Values

variable {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2)
include hY hY2

theorem cxiU0_zero : cxiU0 Y 0 = (-(4 * Y ^ 2 - 9 * Y - 2)) / (12 * Y) := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', -, -, -⟩ := xi_ne_zero_facts hY hY2 ⟨one_half_pos,
    one_half_lt_one⟩
  unfold cxiU0
  field_simp
  ring

theorem cxiW0_zero : cxiW0 Y 0 = (-(7 * Y ^ 4 - 20 * Y ^ 3 + 15 * Y ^ 2 - 10 * Y + 6)) / (12 * Y *
    (Y - 1) ^ 2) := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', -, -, -⟩ := xi_ne_zero_facts hY hY2 ⟨one_half_pos,
    one_half_lt_one⟩
  unfold cxiW0
  field_simp
  ring

theorem cxiU1_one : cxiU1 Y 1 = (23 * Y ^ 2 - 10 * Y - 4) / (24 * Y) := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', -, -, -⟩ := xi_ne_zero_facts hY hY2 ⟨one_half_pos,
    one_half_lt_one⟩
  unfold cxiU1
  field_simp
  ring

theorem cxiW1Y_one : cxiW1Y Y 1 = (-(Y * (Y - 2) * (5 * Y - 3))) / (12 * (Y - 1) ^ 2) := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', -, -, -⟩ := xi_ne_zero_facts hY hY2 ⟨one_half_pos,
    one_half_lt_one⟩
  unfold cxiW1Y
  field_simp
  ring

theorem cxiW1_one : cxiW1 Y 1 = (-((Y - 1) * (2 * Y - 1) ^ 2)) / (6 * Y ^ 2) := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', -, -, -⟩ := xi_ne_zero_facts hY hY2 ⟨one_half_pos,
    one_half_lt_one⟩
  unfold cxiW1
  field_simp
  ring

end Values

/-- **`cxiL1 Y - cxiL0 Y = K_C(Y)`** (eq. (6.10)), by the identities (4.6). -/
theorem cxiL1_sub_cxiL0 {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2) :
    cxiL1 Y - cxiL0 Y = QED.TwoLoop.Units.cornerKernel Y := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', -, -, -⟩ := xi_ne_zero_facts hY hY2 ⟨one_half_pos,
    one_half_lt_one⟩
  have i1 := dilogI_neg_div_one_sub hY
  have i2 := dilogI_two_mul_sub_one_div hY
  have i3 := dilogI_one_sub_two_mul_div hY
  have eD := crossedD_eq hY
  unfold cxiL1 cxiL0 cxiDil
  rw [cxiU0_zero hY hY2, cxiW0_zero hY hY2, cxiU1_one hY hY2, cxiW1Y_one hY hY2, cxiW1_one hY hY2]
  simp only [mul_zero, mul_one, sub_zero, sub_self, zero_div, neg_zero, Li₂_zero, dilogI_zero]
  rw [show (1 : ℝ) - 2 = -1 by norm_num, show (1 - 2 * Y) * -1 = 2 * Y - 1 by ring,
    Li₂_one, Li₂_neg_one, i1, i2, i3]
  rw [QED.TwoLoop.Units.cornerKernel_eq_decomp hY]
  rw [eD]
  unfold cxiCL cxiCq cxiCD
  field_simp
  ring

/-! ### The fundamental theorem of calculus in `ξ` -/

/-- **The `ξ`-integral**, for `Y ∈ (0, 1) \ {1/2}` with an integrable integrand. -/
theorem integral_cxi_eq {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2)
    (hI : IntegrableOn (fun ξ => Y * cornerPhi Y ξ) (Ioo 0 1)) :
    ∫ ξ in Ioo (0 : ℝ) 1, Y * cornerPhi Y ξ = cxiL1 Y - cxiL0 Y := by
  set f := fun ξ => Y * cornerPhi Y ξ with hf
  have hi1 : IntervalIntegrable f volume 0 (1 / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact hI.mono_set fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  have hi2 : IntervalIntegrable f volume (1 / 2) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num),
      integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hI.mono_set fun x hx => ⟨by linarith [hx.1], hx.2⟩
  have hhalf : ContinuousAt (cxiF Y) (1 / 2) := continuousAt_cxiF hY ⟨by norm_num, by norm_num⟩
  have e1 : ∫ ξ in (0 : ℝ)..(1 / 2), f ξ = cxiF Y (1 / 2) - cxiL0 Y :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by norm_num)
      (fun ξ hξ => hasDerivAt_cxiF hY hY2 ⟨hξ.1, by linarith [hξ.2]⟩ hξ.2.ne) hi1
      (tendsto_cxiF_zero hY hY2) (hhalf.tendsto.mono_left nhdsWithin_le_nhds)
  have e2 : ∫ ξ in (1 / 2 : ℝ)..1, f ξ = cxiL1 Y - cxiF Y (1 / 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by norm_num)
      (fun ξ hξ => hasDerivAt_cxiF hY hY2 ⟨by linarith [hξ.1], hξ.2⟩ hξ.1.ne') hi2
      (hhalf.tendsto.mono_left nhdsWithin_le_nhds) (tendsto_cxiF_one hY hY2)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, e1, e2]
  ring

/-- **The `ξ`-integration (step 6.6.2)**: for `Y ∈ (0, 1) \ {1/2}` with an integrable integrand,
`∫₀¹ Y Φ_C(Y, ξ) dξ = K_C(Y)`. -/
theorem integral_cornerPhi_eq_cornerKernel {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2)
    (hI : IntegrableOn (fun ξ => Y * cornerPhi Y ξ) (Ioo 0 1)) :
    ∫ ξ in Ioo (0 : ℝ) 1, Y * cornerPhi Y ξ = QED.TwoLoop.Units.cornerKernel Y := by
  rw [integral_cxi_eq hY hY2 hI, cxiL1_sub_cxiL0 hY hY2]

end QED.TwoLoop.UnitSCCornerXi

end
