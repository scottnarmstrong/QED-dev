/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCLimitCMasters
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The corner unit C: the closed form of the `b`-integral split by logarithms

Section 6.6.1 of `docs/TWO-LOOP-UNITS.md`. The closed form `cForm` of the `b`-integral of eq. (6.2)
(`QED.TwoLoop.UnitSCLimit.cornerGm`) contains the logarithms `A = log(M + β h)` and
`L = log(1 + M/(β h)) = A - log(β h)`. This file proves

* `cForm_eq_split`: `cForm = R + (K - c₀/h) A + K (L - A)`, with the rational part `R` (`cFormR`)
and
  the coefficient `K = a₁/M² - 2 a₂ h/M³ + c₁/M - c₂ h/M² + c₃ h²/M³` of `L` (`cFormKL`);
* `cornerGm_eq_split`: hence, for positive `M`, `β`, `h`,
  `cornerGm = R + (K - c₀/h) log(M + β h) - K log(β h)`.

It also introduces the polynomials `px` of degree at most six in one variable, with their
derivative (`hasDerivAt_px`), used for the antiderivatives in `x`.
-/

@[expose] public section

open Real Set Filter Topology

namespace QED.TwoLoop.UnitSCCorner

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-! ### Polynomials of degree at most six -/

/-- `c₀ + c₁ x + ⋯ + c₆ x⁶`. -/
noncomputable def px (c₀ c₁ c₂ c₃ c₄ c₅ c₆ x : ℝ) : ℝ :=
  c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 + c₄ * x ^ 4 + c₅ * x ^ 5 + c₆ * x ^ 6

/-- The derivative of `px`. -/
noncomputable def pxD (c₁ c₂ c₃ c₄ c₅ c₆ x : ℝ) : ℝ :=
  c₁ + 2 * c₂ * x + 3 * c₃ * x ^ 2 + 4 * c₄ * x ^ 3 + 5 * c₅ * x ^ 4 + 6 * c₆ * x ^ 5

theorem hasDerivAt_px (c₀ c₁ c₂ c₃ c₄ c₅ c₆ x : ℝ) :
    HasDerivAt (px c₀ c₁ c₂ c₃ c₄ c₅ c₆) (pxD c₁ c₂ c₃ c₄ c₅ c₆ x) x := by
  have h := ((((((hasDerivAt_const x c₀).add ((hasDerivAt_id' x).const_mul c₁)).add
    ((hasDerivAt_pow 2 x).const_mul c₂)).add ((hasDerivAt_pow 3 x).const_mul c₃)).add
    ((hasDerivAt_pow 4 x).const_mul c₄)).add ((hasDerivAt_pow 5 x).const_mul c₅)).add
    ((hasDerivAt_pow 6 x).const_mul c₆)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => rfl)
  unfold pxD
  push_cast
  ring

theorem continuous_px (c₀ c₁ c₂ c₃ c₄ c₅ c₆ : ℝ) : Continuous (px c₀ c₁ c₂ c₃ c₄ c₅ c₆) := by
  unfold px
  fun_prop

theorem px_zero (c₀ c₁ c₂ c₃ c₄ c₅ c₆ : ℝ) : px c₀ c₁ c₂ c₃ c₄ c₅ c₆ 0 = c₀ := by
  simp [px]

/-! ### The split of `cForm` -/

/-- The coefficient `K` of `L = log(1 + M/(β h))` in `cForm`. -/
noncomputable def cFormKL (a₁ a₂ c₁ c₂ c₃ h M : ℝ) : ℝ :=
  a₁ / M ^ 2 - 2 * a₂ * h / M ^ 3 + c₁ / M - c₂ * h / M ^ 2 + c₃ * h ^ 2 / M ^ 3

/-- The rational part of `cForm`. -/
noncomputable def cFormR (a₀ a₁ a₂ c₂ c₃ β h M : ℝ) : ℝ :=
  a₀ / (h * (M + β * h)) - a₁ / (M * (M + β * h)) +
    a₂ * (1 / (M ^ 2 * β) + h / (M ^ 2 * (M + β * h))) + c₂ / (M * β) +
    c₃ * (1 / (2 * M * β ^ 2) - h / (M ^ 2 * β))

/-- **The split of `cForm`** into a rational part and the two logarithms. -/
theorem cForm_eq_split (a₀ a₁ a₂ c₀ c₁ c₂ c₃ β h M A L : ℝ) :
    cForm a₀ a₁ a₂ c₀ c₁ c₂ c₃ β h M A L =
      cFormR a₀ a₁ a₂ c₂ c₃ β h M + (cFormKL a₁ a₂ c₁ c₂ c₃ h M - c₀ / h) * A +
        cFormKL a₁ a₂ c₁ c₂ c₃ h M * (L - A) := by
  unfold cForm cFormR cFormKL
  ring

theorem log_one_add_div_eq {M β h : ℝ} (hM : 0 < M) (hβh : 0 < β * h) :
    log (1 + M / (β * h)) = log (M + β * h) - log (β * h) := by
  rw [← log_div (by positivity) hβh.ne', add_div, div_self hβh.ne', add_comm]

/-- **`cornerGm` split by logarithms**: `R + (K - c₀/h) log(M + β h) - K log(β h)`. -/
theorem cornerGm_eq_split {la lb y3 y4 x : ℝ}
    (hM : 0 < cornerMass la lb y3 y4)
    (hβh : 0 < betaG (cornerG y3 y4) (y3 * y4) x * (ladderInnerMass 1 la x / x)) :
    cornerGm la lb y3 y4 x =
      cFormR (cornerA0 x y3 y4) (cornerA1 x y3 y4) (cornerA2 x y3 y4) (cornerC2 x y3 y4)
          (cornerC3 x y3 y4) (betaG (cornerG y3 y4) (y3 * y4) x) (ladderInnerMass 1 la x / x)
          (cornerMass la lb y3 y4) +
        (cFormKL (cornerA1 x y3 y4) (cornerA2 x y3 y4) (cornerC1 x y3 y4) (cornerC2 x y3 y4)
          (cornerC3 x y3 y4) (ladderInnerMass 1 la x / x) (cornerMass la lb y3 y4) -
          cornerC0 x / (ladderInnerMass 1 la x / x)) *
          log (cornerMass la lb y3 y4 +
            betaG (cornerG y3 y4) (y3 * y4) x * (ladderInnerMass 1 la x / x)) -
        cFormKL (cornerA1 x y3 y4) (cornerA2 x y3 y4) (cornerC1 x y3 y4) (cornerC2 x y3 y4)
          (cornerC3 x y3 y4) (ladderInnerMass 1 la x / x) (cornerMass la lb y3 y4) *
          log (betaG (cornerG y3 y4) (y3 * y4) x * (ladderInnerMass 1 la x / x)) := by
  unfold cornerGm
  rw [cForm_eq_split, log_one_add_div_eq hM hβh]
  ring

end QED.TwoLoop.UnitSCCorner

end
