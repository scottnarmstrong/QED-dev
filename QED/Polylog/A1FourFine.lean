/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.A1Four
public import QED.Polylog.ConstBounds

/-!
# A fine enclosure of the two-loop coefficient `A₁⁽⁴⁾`

`A₁⁽⁴⁾ = 197/144 + π²/12 - (π²/2) ln 2 + (3/4) ζ(3) = -0.328 478 965 579 193 784 58…`
(the frozen definition `QED.TwoLoop.a1Four`), enclosed with the certified bounds of
`QED.Polylog.ConstBounds`: `ζ(3)` and `ln 2` to `10⁻¹⁸`, `π` from Mathlib's twenty-digit bounds.

## Main results

* `QED.Polylog.a1Four_bounds_fine`: `-0.328478965580 < A₁⁽⁴⁾ < -0.328478965579`.
* `QED.Polylog.a1Four_bounds_finer`:
  `-0.32847896557919380 < A₁⁽⁴⁾ < -0.32847896557919376`.
-/

public section

open Real

namespace QED.Polylog

/-- `-0.32847896557919380 < A₁⁽⁴⁾ < -0.32847896557919376`
(true value `-0.32847896557919378458…`). -/
theorem a1Four_bounds_finer :
    -0.32847896557919380 < QED.TwoLoop.a1Four ∧ QED.TwoLoop.a1Four < -0.32847896557919376 := by
  have hp := pi_sq_bounds
  have hl := log_two_bounds
  have hz1 := zeta3_gt_d18
  have hz2 := zeta3_lt_d18
  have hpl := mul_bounds (by norm_num) (by norm_num) hp hl
  have e : QED.TwoLoop.a1Four = 197 / 144 + π ^ 2 / 12 - (π ^ 2 * log 2) / 2 + 3 / 4 * zeta3 := by
    unfold QED.TwoLoop.a1Four zeta3; ring
  rw [e]
  norm_num at hp hpl ⊢
  constructor <;> linarith [hp.1, hp.2, hpl.1, hpl.2]

/-- **`A₁⁽⁴⁾` to twelve decimals**: `-0.328478965580 < A₁⁽⁴⁾ < -0.328478965579`. -/
theorem a1Four_bounds_fine :
    -0.328478965580 < QED.TwoLoop.a1Four ∧ QED.TwoLoop.a1Four < -0.328478965579 := by
  have h := a1Four_bounds_finer
  constructor <;> linarith [h.1, h.2]

end QED.Polylog
