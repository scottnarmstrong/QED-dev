/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXKernelBasic
import QED.Polylog.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The integration by parts `K_X = G' + p + K_m` (helper level, O2-25)

Eq. (4.8) of `docs/TWO-LOOP-UNITS.md`: on `(0, 1) \ {1/2}` the derivative of the boundary function
`G` (`crossedBoundary`) is `K_X - p - K_m` (`crossedKernel`, `crossedPoly`,
`crossedMasterKernel`).

## Main statements

* `QED.TwoLoop.Units.hasDerivAt_crossedBoundary`: `G' = K_X - p - K_m` on `(0, 1) \ {1/2}`.

Every coefficient of `G` has the form `a Y² + b Y + c + d/Y + e/(Y-1) + f/(Y-1)² + g/(Y-1)³`
(`crossedBoundary_eq_coef`); the derivative is assembled from `hasDerivAt_coefX`, the derivatives
of `Li₂`, `D`, `log Y` and `log (1 - Y)`, and checked by `field_simp` and `ring`.
-/

public section

open Real Set Filter Topology QED.Polylog

namespace QED.TwoLoop.Units

/-- The derivative of `a y² + b y + c + d/y + e/(y-1) + f/(y-1)² + g/(y-1)³`. -/
theorem hasDerivAt_coefX (a b c d e f g : ℝ) {Y : ℝ} (h0 : Y ≠ 0) (h1 : Y - 1 ≠ 0) :
    HasDerivAt (fun y => a * y ^ 2 + b * y + c + d / y + e / (y - 1) + f / (y - 1) ^ 2 +
        g / (y - 1) ^ 3)
      (2 * a * Y + b - d / Y ^ 2 - e / (Y - 1) ^ 2 - 2 * f / (Y - 1) ^ 3 -
        3 * g / (Y - 1) ^ 4) Y := by
  have hs : HasDerivAt (fun y : ℝ => y - 1) 1 Y := (hasDerivAt_id' Y).sub_const 1
  have h := ((((((((hasDerivAt_pow 2 Y).const_mul a).add ((hasDerivAt_id' Y).const_mul b)).add_const
    c).add ((hasDerivAt_const Y d).div (hasDerivAt_id' Y) h0)).add
    ((hasDerivAt_const Y e).div hs h1)).add
    ((hasDerivAt_const Y f).div (hs.pow 2) (pow_ne_zero 2 h1))).add
    ((hasDerivAt_const Y g).div (hs.pow 3) (pow_ne_zero 3 h1)))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => rfl)
  simp only [Pi.pow_apply]
  push_cast
  field_simp
  ring

theorem crossedBoundary_eq_coef (Y : ℝ) :
    crossedBoundary Y =
      (-(5 / 4) * Y ^ 2 + -(5 / 4) * Y + 0 + 7 / 12 / Y + 3 / 2 / (Y - 1) + 8 / 3 / (Y - 1) ^ 2 +
          2 / 3 / (Y - 1) ^ 3) * Li₂ Y +
        (-(7 / 12) * Y ^ 2 + -(11 / 12) * Y + 0 + 1 / 12 / Y + 3 / 4 / (Y - 1) +
          4 / 3 / (Y - 1) ^ 2 + 1 / 3 / (Y - 1) ^ 3) * crossedD Y +
        (1 / 24 * Y ^ 2 + -(7 / 24) * Y + -(1 / 8) + 0 / Y + 3 / 8 / (Y - 1) + 2 / 3 / (Y - 1) ^ 2 +
          1 / 6 / (Y - 1) ^ 3) * log Y ^ 2 +
        (-(2 / 3) * Y ^ 2 + -(1 / 3) * Y + 0 + 7 / 12 / Y + 0 / (Y - 1) + 0 / (Y - 1) ^ 2 +
          0 / (Y - 1) ^ 3) * (log Y * log (1 - Y)) +
        (-(11 / 24) * Y ^ 2 + -(7 / 8) * Y + 5 / 12 + 0 / Y + 1 / 3 / (Y - 1) +
          1 / 3 / (Y - 1) ^ 2 + 0 / (Y - 1) ^ 3) * log Y +
        (11 / 24 * Y ^ 2 + -(19 / 24) * Y + 23 / 24 + 1 / 24 / Y + 1 / 3 / (Y - 1) +
          0 / (Y - 1) ^ 2 + 0 / (Y - 1) ^ 3) * log (1 - Y) +
        (0 * Y ^ 2 + 0 * Y + 0 + -(π ^ 2 / 48) / Y + (-(π ^ 2 / 16) - 1 / 3) / (Y - 1) +
          -(π ^ 2 / 9) / (Y - 1) ^ 2 + -(π ^ 2 / 36) / (Y - 1) ^ 3) := by
  unfold crossedBoundary
  simp only [← div_div]
  ring

/-- **`G' = K_X - p - K_m`** on `(0, 1) \ {1/2}` (eq. (4.8)). -/
theorem hasDerivAt_crossedBoundary {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hh : Y ≠ 1 / 2) :
    HasDerivAt crossedBoundary (crossedKernel Y - crossedPoly Y - crossedMasterKernel Y) Y := by
  have hY0 : Y ≠ 0 := hY.1.ne'
  have hY1 : Y - 1 ≠ 0 := by linarith [hY.2]
  have hY1' : (1 : ℝ) - Y ≠ 0 := by linarith [hY.2]
  have hY2 : (1 : ℝ) - 2 * Y ≠ 0 := fun h => hh (by linarith)
  have hY2' : (2 : ℝ) * Y - 1 ≠ 0 := fun h => hh (by linarith)
  have hL := hasDerivAt_Li₂' hY
  have hD := hasDerivAt_crossedD hY hh
  have ha := hasDerivAt_log hY0
  have hb := hasDerivAt_log_one_sub hY.2
  have q := fun a b c d e f g => hasDerivAt_coefX a b c d e f g hY0 hY1
  have h := (((((((q (-(5 / 4)) (-(5 / 4)) 0 (7 / 12) (3 / 2) (8 / 3) (2 / 3)).mul hL).add
    ((q (-(7 / 12)) (-(11 / 12)) 0 (1 / 12) (3 / 4) (4 / 3) (1 / 3)).mul hD)).add
    ((q (1 / 24) (-(7 / 24)) (-(1 / 8)) 0 (3 / 8) (2 / 3) (1 / 6)).mul (ha.pow 2))).add
    ((q (-(2 / 3)) (-(1 / 3)) 0 (7 / 12) 0 0 0).mul (ha.mul hb))).add
    ((q (-(11 / 24)) (-(7 / 8)) (5 / 12) 0 (1 / 3) (1 / 3) 0).mul ha)).add
    ((q (11 / 24) (-(19 / 24)) (23 / 24) (1 / 24) (1 / 3) 0 0).mul hb)).add
    (q 0 0 0 (-(π ^ 2 / 48)) (-(π ^ 2 / 16) - 1 / 3) (-(π ^ 2 / 9)) (-(π ^ 2 / 36)))
  rw [show crossedBoundary = _ from funext crossedBoundary_eq_coef]
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  unfold crossedKernel crossedPoly crossedMasterKernel crossedRho
  field_simp
  ring

end QED.TwoLoop.Units
