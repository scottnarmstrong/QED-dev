/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.A1Four
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import QED.TwoLoop.A1FourNumerics

/-!
# Provider for `QED.TwoLoop.a1Four_bounds`

Proves packet T2's theorem goal (U₂) (decision D-39) as `QED.Provider.TwoLoop.a1Four_bounds`,
with the binder convention of decision D-13: `-0.3285 < A₁⁽⁴⁾ < -0.3284`. The content is the
rational enclosures of `QED.TwoLoop.Numerics`: `1.202042 < ζ(3) < 1.202057`, with the
telescoping tail bounds after forty terms, and Mathlib's bounds on `π` and `ln 2` for
`π²/12 - (π²/2) ln 2`. This module must never import the frozen anchor.
-/

public section

namespace QED.Provider.TwoLoop

open QED.TwoLoop.Numerics in
/-- (U₂) **A₁⁽⁴⁾ to four decimal places**: `-0.3285 < A₁⁽⁴⁾ < -0.3284`. -/
theorem a1Four_bounds : -0.3285 < QED.TwoLoop.a1Four ∧ QED.TwoLoop.a1Four < -0.3284 := by
  have z1 := zeta_three_gt
  have z2 := zeta_three_lt
  have p1 := pi_sq_log_two_gt
  have p2 := pi_sq_log_two_lt
  unfold QED.TwoLoop.a1Four
  constructor <;> linarith

end QED.Provider.TwoLoop

end
