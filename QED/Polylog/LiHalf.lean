/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.LiN
import QED.Polylog.Landen
import QED.Polylog.Reflection

/-!
# Polylogarithms at `1 / 2`

The closed forms of `Li 1`, `Li 2`, `Li 3` at `1 / 2`, in terms of the generic polylogarithm
`QED.Polylog.Li`. The trilogarithm value is Landen's identity
(`QED.Polylog.Li₃_one_half`), proved there from the dilogarithm reflection and Landen identities.

## Main results

* `QED.Polylog.Li_one_one_half`: `Li 1 (1 / 2) = log 2`.
* `QED.Polylog.Li_two_one_half`: `Li 2 (1 / 2) = π ^ 2 / 12 - (log 2) ^ 2 / 2`.
* `QED.Polylog.Li_three_one_half`:
  `Li 3 (1 / 2) = (7 / 8) ζ(3) - (π ^ 2 / 12) log 2 + (log 2) ^ 3 / 6`.
* `QED.Polylog.zeta3_eq_Li_three_one_half`: `ζ(3)` in terms of `Li 3 (1 / 2)`, `π` and `log 2`.
-/

@[expose] public section

open Real

namespace QED.Polylog

/-- `Li 1 (1 / 2) = log 2`. -/
theorem Li_one_one_half : Li 1 (1 / 2) = log 2 := by
  rw [Li_one (by rw [abs_of_pos (by norm_num)]; norm_num),
    show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv, neg_neg]

/-- `Li 2 (1 / 2) = π ^ 2 / 12 - (log 2) ^ 2 / 2`. -/
theorem Li_two_one_half : Li 2 (1 / 2) = π ^ 2 / 12 - log 2 ^ 2 / 2 := Li₂_one_half

/-- `Li 3 (1 / 2) = (7 / 8) ζ(3) - (π ^ 2 / 12) log 2 + (log 2) ^ 3 / 6`. -/
theorem Li_three_one_half :
    Li 3 (1 / 2) = 7 / 8 * zeta3 - π ^ 2 / 12 * log 2 + log 2 ^ 3 / 6 := Li₃_one_half

/-- `ζ(3) = (8 / 7) (Li 3 (1 / 2) + (π ^ 2 / 12) log 2 - (log 2) ^ 3 / 6)`. -/
theorem zeta3_eq_Li_three_one_half :
    zeta3 = 8 / 7 * (Li 3 (1 / 2) + π ^ 2 / 12 * log 2 - log 2 ^ 3 / 6) := by
  rw [Li_three_one_half]
  ring

end QED.Polylog
