/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1Gr0
public import QED.ThreeLoopD.SetDMastersI5C1GrY
public import QED.ThreeLoopD.SetDMastersI5C1Int

/-!
# Set (d), master `I₅`: the first Taylor coefficient of the remainder

The primitive `QED.ThreeLoopD.i5C1PB` of `I(x)` has the limits `QED.ThreeLoopD.i5C1E_V0` at
`x = 0⁺` and `QED.ThreeLoopD.i5C1E_Vy` at `x = (1 - ξ)⁻`; their difference is the trilogarithm
form of `K(ξ)` (`QED.ThreeLoopD.i5C1E_Vy_sub_V0`, `QED.ThreeLoopD.i5K1x_eq_li`). The
fundamental theorem of calculus gives `∫₀^{1-ξ} I = K(ξ)` (`QED.ThreeLoopD.integral_i5K1I`), and
with `QED.ThreeLoopD.i5RemCoeff_one_of_intI` the first coefficient of the remainder,
`c₁ = -4π⁴/45 - 5π²/3 - 5ζ(3) + 25` (`QED.ThreeLoopD.i5RemCoeff_one`).

## Main results

* `QED.ThreeLoopD.i5C1E_Vy_sub_V0`, `QED.ThreeLoopD.integral_i5K1I`.
* `QED.ThreeLoopD.i5RemCoeff_one`.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology QED.Polylog

namespace QED.ThreeLoopD

/-- The difference of the endpoint limits of the primitive. -/
theorem i5C1E_Vy_sub_V0 (ξ : ℝ) :
    i5C1E_Vy ξ - i5C1E_V0 ξ = Li₂ (-ξ) * log ξ - 2 * Li₂ (-ξ) * log (1 - ξ) - 8 * Li₂ ξ *
        log (1 + ξ) +
      2 * Li₂ ξ * log ξ - 2 * Li₂ ξ * log (1 - ξ) + 2 * Li₂ ξ - 10 * Li₃ (ξ / (1 + ξ)) -
      2 * Li₃ (1 / (1 + ξ)) - 30 * Li₃ (-ξ) + 6 * Li₃ (1 - ξ) - 4 * Li₃ (1 - ξ ^ 2) -
      18 * Li₃ ξ + 4 * Li₃ (ξ ^ 2) + π ^ 2 * log (1 + ξ) / 3 - π ^ 2 * log (1 - ξ) / 2 +
      2 * log (1 + ξ) ^ 3 - 5 * log (1 + ξ) ^ 2 * log ξ - 8 * log (1 + ξ) * log ξ * log (1 - ξ) +
      log ξ ^ 2 * log (1 - ξ) / 2 - log ξ * log (1 - ξ) ^ 2 + log ξ * log (1 - ξ) := by
  simp only [i5C1E_Vy, i5C1E_Vya, i5C1E_Vyb, i5C1E_Vyc, i5C1E_Vyd, i5C1E_Vye, i5C1E_Vyf, i5C1E_Vyg,
      i5C1E_Vyh, i5C1E_V0, i5C1E_V0a, i5C1E_V0b, i5C1E_V0c, i5C1E_V0d, i5C1E_V0e, i5C1E_V0f,
      i5C1E_V0g, i5C1E_V0h]
  ring

/-- **`∫₀^{1-ξ} I(x) dx = K(ξ)`** for `0 < ξ < 1`. -/
theorem integral_i5K1I {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ∫ x in Ioo 0 (1 - ξ), i5K1I ξ x = i5K1x ξ := by
  have hy : 0 < 1 - ξ := by linarith [hξ.2]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hy
    (fun x hx => hasDerivAt_i5C1PB hξ hx.1 hx.2) (intervalIntegrable_i5K1I hξ)
    (tendsto_i5C1PB_zero hξ) (tendsto_i5C1PB_sub hξ)
  rw [intervalIntegral.integral_of_le hy.le, integral_Ioc_eq_integral_Ioo] at h
  rw [h, i5C1E_Vy_sub_V0, i5K1x_eq_li hξ]

/-- **The first Taylor coefficient of the remainder of `I₅`**:
`c₁ = -4π⁴/45 - 5π²/3 - 5ζ(3) + 25`. -/
theorem i5RemCoeff_one :
    i5RemCoeff 1 = -4 / 45 * (π : ℂ) ^ 4 - 5 / 3 * (π : ℂ) ^ 2 - 5 * (zeta3 : ℂ) + 25 :=
  i5RemCoeff_one_of_intI fun _ hξ => integral_i5K1I hξ

end QED.ThreeLoopD
