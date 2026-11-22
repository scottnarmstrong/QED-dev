/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondDy
public import QED.ThreeLoopD.SetDMastersI12RSecondEx
public import QED.ThreeLoopD.SetDMastersI12RSecondElem
public import QED.ThreeLoopD.SetDMastersI12RSecondI2
import QED.ThreeLoopD.SetDMastersI12RSecondPt
import QED.ThreeLoopD.SetDMastersI9Analytic

/-!
# Set (d), master `I₁₂`: the value of `R₁'(0) + B₃ᵇ`, given the closed form of `E`

By `QED.ThreeLoopD.deriv_i12R1_add_i12B3bad`,
`R₁'(0) + B₃ᵇ = 2 ∫₀^{1/2} (i12R1Elem y + K(y)/y) dy`. For almost every `y` the function
`E(y (1 - y))` inside `i12R1Elem` is `∫₀¹ i12REx (y (1 - y)) x dx` (`QED.ThreeLoopD.i12RE_eq`), and
`K = QED.ThreeLoopD.i12RKcl` on `(0, 1)` (`QED.ThreeLoopD.i12RK_eq`). Given the closed form
`∫₀¹ i12REx (y (1 - y)) x dx = QED.ThreeLoopD.i12REcl y` on `(0, 1/2]`, the integrand is
`i12R1Pcl y + i12RKcl y / y` almost everywhere, with the antiderivative
`i12R1PPrim + i12RKclPrim`, whose limits at `0⁺` and `1/2` give

  `R₁'(0) + B₃ᵇ = 1475/36 - 3π²/4 + 6ℓ - 6ℓ² + π²ℓ + 2ℓ³ - 21 ζ(3)`,   `ℓ = log 2`.

## Main results

* `QED.ThreeLoopD.deriv_i12R1_add_i12B3bad_eq_of_E`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- **`R₁'(0) + B₃ᵇ` in closed form**, from the closed form of `E` on `(0, 1/2]`. -/
theorem deriv_i12R1_add_i12B3bad_eq_of_E
    (hE : ∀ y ∈ Ioc (0 : ℝ) (1 / 2), ∫ x in Ioo (0 : ℝ) 1, i12REx (y * (1 - y)) x = i12REcl y) :
    deriv i12R1 0 + ((∫ x in Ioo (0 : ℝ) 1, i12B3bad x : ℝ) : ℂ) =
      ((1475 / 36 - 3 * π ^ 2 / 4 + 6 * log 2 - 6 * log 2 ^ 2 + π ^ 2 * log 2 +
        2 * log 2 ^ 3 - 21 * zeta3 : ℝ) : ℂ) := by
  obtain ⟨hint, hD⟩ := deriv_i12R1_add_i12B3bad
  obtain ⟨hi, -⟩ := hasDerivAt_i12R1_zero
  have hiR : Integrable (fun z : ℝ × ℝ × ℝ => i12R1d (z.1 * (1 - z.1)) z.2.1 z.2.2)
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))) :=
    hi.re.congr (ae_of_all _ fun z => Complex.ofReal_re _)
  rw [volume_restrict_prod3] at hiR
  have hae := (ae_restrict_iff' measurableSet_Ioo).1 hiR.prod_right_ae
  have hpt : ∀ᵐ y ∂volume, y ∈ uIoc (0 : ℝ) (1 / 2) →
      i12R1Elem y + i12RK y / y = i12R1Pcl y + i12RKcl y / y := by
    filter_upwards [hae] with y hy hy'
    rw [uIoc_of_le (by norm_num)] at hy'
    have hy1 : y ∈ Ioo (0 : ℝ) 1 := ⟨hy'.1, by linarith [hy'.2]⟩
    have hc : 0 < y * (1 - y) := mul_pos hy1.1 (by linarith [hy1.2])
    have hEy : i12RE (y * (1 - y)) = i12REcl y := by
      rw [(i12RE_eq hc (hy hy1)).2, hE y hy']
    rw [i12RK_eq hy1]
    simp only [i12R1Elem, i12R1Pcl, hEy]
  have hint' : IntervalIntegrable (fun y => i12R1Pcl y + i12RKcl y / y) volume 0 (1 / 2) :=
    hint.congr_ae ((ae_restrict_iff' measurableSet_uIoc).2 hpt)
  have hderiv : ∀ y ∈ Ioo (0 : ℝ) (1 / 2), HasDerivAt (fun y => i12R1PPrim y + i12RKclPrim y)
      (i12R1Pcl y + i12RKcl y / y) y := fun y hy =>
    (hasDerivAt_i12R1PPrim ⟨hy.1, by linarith [hy.2]⟩).add
      (hasDerivAt_i12RKclPrim ⟨hy.1, by linarith [hy.2]⟩)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by norm_num) hderiv
    hint' (tendsto_i12R1PPrim_zero.add tendsto_i12RKclPrim_zero)
    (tendsto_i12R1PPrim_half.add tendsto_i12RKclPrim_half)
  rw [hD, intervalIntegral.integral_congr_ae hpt, hFTC]
  congr 1
  ring

end QED.ThreeLoopD
