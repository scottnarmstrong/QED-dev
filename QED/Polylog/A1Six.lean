/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.ConstBounds

/-!
# The Laporta–Remiddi value of `A₁⁽⁶⁾` and its enclosure

The mass-independent sixth-order coefficient of the electron anomaly, in the closed form of
Laporta and Remiddi (Phys. Lett. B 379 (1996) 283, arXiv:hep-ph/9602417, abstract; also
Passera (2007) eq. (14)), with `a₄ = Li₄(1/2)`:
`A₁⁽⁶⁾ = 83/72 π² ζ(3) - 215/24 ζ(5) + 100/3 [(a₄ + ln⁴2/24) - π² ln²2/24] - 239/2160 π⁴
  + 139/18 ζ(3) - 298/9 π² ln 2 + 17101/810 π² + 28259/5184 = 1.181 241 456 587 200 0…`.

This module only *defines* the closed-form expression and encloses it. It does not claim that
the expression equals any Feynman-diagram quantity.

## Main results

* `QED.Polylog.a1SixLR`: the closed-form expression.
* `QED.Polylog.a1SixLR_bounds`: `1.18124145658 < a1SixLR < 1.18124145659`.
* `QED.Polylog.a1SixLR_bounds_fine`: `1.1812414565871995 < a1SixLR < 1.1812414565872003`.
-/

@[expose] public section

open Real

namespace QED.Polylog

/-- The Laporta–Remiddi closed form of the three-loop coefficient `A₁⁽⁶⁾`. -/
noncomputable def a1SixLR : ℝ :=
  83 / 72 * π ^ 2 * zeta3 - 215 / 24 * zeta5 +
    100 / 3 * ((Li 4 (1 / 2) + log 2 ^ 4 / 24) - π ^ 2 * log 2 ^ 2 / 24) -
    239 / 2160 * π ^ 4 + 139 / 18 * zeta3 - 298 / 9 * π ^ 2 * log 2 +
    17101 / 810 * π ^ 2 + 28259 / 5184

/-- `1.1812414565871995 < A₁⁽⁶⁾ < 1.1812414565872003` (true value `1.18124145658720000627…`). -/
theorem a1SixLR_bounds_fine :
    1.1812414565871995 < a1SixLR ∧ a1SixLR < 1.1812414565872003 := by
  have hp := pi_sq_bounds
  have hl := log_two_bounds
  have hz : (1.202056903159594284 : ℝ) ≤ zeta3 ∧ zeta3 ≤ 1.202056903159594286 :=
    ⟨zeta3_gt_d18.le, zeta3_lt_d18.le⟩
  have h5l := zeta5_gt_d17
  have h5h := zeta5_lt_d17
  have hal := Li_four_one_half_gt
  have hah := Li_four_one_half_lt
  have hpz := mul_bounds (by norm_num) (by norm_num) hp hz
  have hpl := mul_bounds (by norm_num) (by norm_num) hp hl
  have hl2 := mul_bounds (by norm_num) (by norm_num) hl hl
  have hpl2 := mul_bounds (by norm_num) (by norm_num) hp hl2
  have hl4 := mul_bounds (by norm_num) (by norm_num) hl2 hl2
  have hp4 := mul_bounds (by norm_num) (by norm_num) hp hp
  have e : a1SixLR = 83 / 72 * (π ^ 2 * zeta3) - 215 / 24 * zeta5 +
      100 / 3 * ((Li 4 (1 / 2) + log 2 * log 2 * (log 2 * log 2) / 24) -
        π ^ 2 * (log 2 * log 2) / 24) -
      239 / 2160 * (π ^ 2 * π ^ 2) + 139 / 18 * zeta3 - 298 / 9 * (π ^ 2 * log 2) +
      17101 / 810 * π ^ 2 + 28259 / 5184 := by
    unfold a1SixLR; ring
  rw [e]
  norm_num at hp hpz hpl hpl2 hl4 hp4 ⊢
  constructor <;>
    linarith [hp.1, hp.2, hz.1, hz.2, hpz.1, hpz.2, hpl.1, hpl.2, hpl2.1, hpl2.2, hl4.1, hl4.2,
      hp4.1, hp4.2]

/-- **The Laporta–Remiddi constant to ten decimals**: `1.18124145658 < A₁⁽⁶⁾ < 1.18124145659`. -/
theorem a1SixLR_bounds : 1.18124145658 < a1SixLR ∧ a1SixLR < 1.18124145659 := by
  have h := a1SixLR_bounds_fine
  constructor <;> linarith [h.1, h.2]

end QED.Polylog
