/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXCloseYXi
public import QED.TwoLoop.UnitXCloseDilog
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The `ξ`-integration of the crossed-ladder unit: definitions

Step 4.5.2 of `docs/TWO-LOOP-UNITS.md`. In the variables `z₂ = Y ξ`, `z₃ = Y (1 - ξ)` the
integrand of eq. (4.4) is, by eq. (4.5),

`Y Φ_X(Y ξ, Y (1 - ξ)) = R₁ + R_Y log Y + R_ξ log ξ + R_A log (1 - Y ξ) + R_B log (ξ + Y - 2 Y ξ)`,

with rational coefficients `xiΦ1`, `xiΦY`, `xiΦx`, `xiΦA`, `xiΦB` (proved in
`QED.TwoLoop.UnitXXiPhi`). This file states an antiderivative in `ξ` at fixed `Y` (`xiF`):

`F = P₀ + P_ξ log ξ + P_A log (1 - Y ξ) + P_B log (ξ + Y - 2 Y ξ) + P_Y log Y + c_L Li₂ (Y ξ)
  + c_q (Li₂ (1 - ξ) + Li(-Y (1 - ξ)/(1 - Y)) - Li((1 - 2Y)(1 - ξ)/(1 - Y)))
  + (Li₂ (1 - 2ξ) - Li₂ ((1 - 2Y)(1 - 2ξ)))/(2 Y²) + c_D Li((2Y - 1) ξ/Y)`,

where `Li = dilogI` is the dilogarithm on `(-∞, 1)` (`QED.TwoLoop.UnitXClose.dilogI`; three of its
arguments leave `[-1, 1]`). Each `P` is a partial-fraction form `pfXi` in `ξ` with poles at
`ξ = 0, 1` only and coefficients rational in `Y`.

The coefficients were computed in exact rational arithmetic by
`scripts/numerics/crossed_graph/xi_integration.py`, which also checks every identity used below.

* `hasDerivAt_pfXi`: the derivative of a partial-fraction form.
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog

namespace QED.TwoLoop.UnitXXi

open QED.TwoLoop.UnitXClose

/-- A partial-fraction form in `ξ`:
`a₀ + a₁ ξ + a₂ ξ² + d₁/ξ + d₂/ξ² + e₁/(ξ-1) + e₂/(ξ-1)² + e₃/(ξ-1)³`. -/
noncomputable def pfXi (a₀ a₁ a₂ d₁ d₂ e₁ e₂ e₃ ξ : ℝ) : ℝ :=
  a₀ + a₁ * ξ + a₂ * ξ ^ 2 + d₁ / ξ + d₂ / ξ ^ 2 + e₁ / (ξ - 1) + e₂ / (ξ - 1) ^ 2 +
    e₃ / (ξ - 1) ^ 3

/-- The derivative of `pfXi`. -/
noncomputable def pfXiD (a₁ a₂ d₁ d₂ e₁ e₂ e₃ ξ : ℝ) : ℝ :=
  a₁ + 2 * a₂ * ξ - d₁ / ξ ^ 2 - 2 * d₂ / ξ ^ 3 - e₁ / (ξ - 1) ^ 2 - 2 * e₂ / (ξ - 1) ^ 3 -
    3 * e₃ / (ξ - 1) ^ 4

/-- **The derivative of a partial-fraction form.** -/
theorem hasDerivAt_pfXi (a₀ a₁ a₂ d₁ d₂ e₁ e₂ e₃ : ℝ) {ξ : ℝ} (h0 : ξ ≠ 0) (h1 : ξ - 1 ≠ 0) :
    HasDerivAt (pfXi a₀ a₁ a₂ d₁ d₂ e₁ e₂ e₃) (pfXiD a₁ a₂ d₁ d₂ e₁ e₂ e₃ ξ) ξ := by
  have hs : HasDerivAt (fun y : ℝ => y - 1) 1 ξ := (hasDerivAt_id' ξ).sub_const 1
  have h := (((((((hasDerivAt_const ξ a₀).add ((hasDerivAt_id' ξ).const_mul a₁)).add
    ((hasDerivAt_pow 2 ξ).const_mul a₂)).add
    ((hasDerivAt_const ξ d₁).div (hasDerivAt_id' ξ) h0)).add
    ((hasDerivAt_const ξ d₂).div (hasDerivAt_pow 2 ξ) (pow_ne_zero 2 h0))).add
    ((hasDerivAt_const ξ e₁).div hs h1)).add
    ((hasDerivAt_const ξ e₂).div (hs.pow 2) (pow_ne_zero 2 h1))).add
    ((hasDerivAt_const ξ e₃).div (hs.pow 3) (pow_ne_zero 3 h1))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => rfl)
  unfold pfXiD
  simp only [Pi.pow_apply]
  push_cast
  field_simp
  ring

/-- The rational part of the `ξ`-antiderivative. -/
noncomputable def xiR0 (Y ξ : ℝ) : ℝ :=
  pfXi
    0
    ((-(7 * Y - 4) * (2 * Y ^ 2 - 3 * Y - 1)) / (12 * (Y - 1) ^ 2))
    ((-Y) / 12)
    ((2 * Y - 1) / (4 * Y * (Y - 1)))
    0
    ((-Y + 1) / (6 * Y))
    0
    0
    ξ

/-- The `ξ`-derivative of `xiR0`. -/
noncomputable def xiR0D (Y ξ : ℝ) : ℝ :=
  pfXiD
    ((-(7 * Y - 4) * (2 * Y ^ 2 - 3 * Y - 1)) / (12 * (Y - 1) ^ 2))
    ((-Y) / 12)
    ((2 * Y - 1) / (4 * Y * (Y - 1)))
    0
    ((-Y + 1) / (6 * Y))
    0
    0
    ξ

theorem hasDerivAt_xiR0 (Y : ℝ) {ξ : ℝ} (h0 : ξ ≠ 0) (h1 : ξ - 1 ≠ 0) :
    HasDerivAt (xiR0 Y) (xiR0D Y ξ) ξ :=
  hasDerivAt_pfXi _ _ _ _ _ _ _ _ h0 h1

/-- The coefficient of `log ξ` in the `ξ`-antiderivative. -/
noncomputable def xiPx (Y ξ : ℝ) : ℝ :=
  pfXi
    ((-28 * Y ^ 3 + 11 * Y ^ 2 + 2 * Y + 9) / (24 * Y ^ 2))
    ((Y ^ 2 + Y - 1) / (3 * Y))
    ((-2 * Y - 1) / 12)
    0
    0
    ((-16 * Y ^ 3 + 13 * Y ^ 2 - 8 * Y + 6) / (12 * Y ^ 2))
    ((-4 * Y ^ 3 + 19 * Y ^ 2 - 26 * Y + 7) / (24 * Y ^ 2))
    (((Y - 1) ^ 2) / (6 * Y ^ 2))
    ξ

/-- The `ξ`-derivative of `xiPx`. -/
noncomputable def xiPxD (Y ξ : ℝ) : ℝ :=
  pfXiD
    ((Y ^ 2 + Y - 1) / (3 * Y))
    ((-2 * Y - 1) / 12)
    0
    0
    ((-16 * Y ^ 3 + 13 * Y ^ 2 - 8 * Y + 6) / (12 * Y ^ 2))
    ((-4 * Y ^ 3 + 19 * Y ^ 2 - 26 * Y + 7) / (24 * Y ^ 2))
    (((Y - 1) ^ 2) / (6 * Y ^ 2))
    ξ

theorem hasDerivAt_xiPx (Y : ℝ) {ξ : ℝ} (h0 : ξ ≠ 0) (h1 : ξ - 1 ≠ 0) :
    HasDerivAt (xiPx Y) (xiPxD Y ξ) ξ :=
  hasDerivAt_pfXi _ _ _ _ _ _ _ _ h0 h1

/-- The coefficient of `log (1 - Y ξ)` in the `ξ`-antiderivative. -/
noncomputable def xiPA (Y ξ : ℝ) : ℝ :=
  pfXi
    ((-(Y - 2) * (28 * Y ^ 4 + 17 * Y ^ 3 - 43 * Y ^ 2 + 9 * Y + 7)) / (24 * Y * (Y - 1) ^ 3))
    ((Y * (4 * Y ^ 4 - 12 * Y ^ 3 + 4 * Y ^ 2 - 5 * Y + 3)) / (12 * (Y - 1) ^ 4))
    ((-Y ^ 2 * (2 * Y - 3)) / (12 * (Y - 1) ^ 2))
    ((-42 * Y ^ 4 + 97 * Y ^ 3 - 62 * Y ^ 2 + 12 * Y + 1) / (12 * Y ^ 2 * (Y - 1) ^ 4))
    (((2 * Y - 1) * (2 * Y ^ 2 - 2 * Y + 1)) / (4 * Y ^ 2 * (Y - 1) ^ 3))
    ((-16 * Y ^ 3 + 13 * Y ^ 2 - 8 * Y + 6) / (12 * Y ^ 2))
    ((-4 * Y ^ 3 + 19 * Y ^ 2 - 26 * Y + 7) / (24 * Y ^ 2))
    (((Y - 1) ^ 2) / (6 * Y ^ 2))
    ξ

/-- The `ξ`-derivative of `xiPA`. -/
noncomputable def xiPAD (Y ξ : ℝ) : ℝ :=
  pfXiD
    ((Y * (4 * Y ^ 4 - 12 * Y ^ 3 + 4 * Y ^ 2 - 5 * Y + 3)) / (12 * (Y - 1) ^ 4))
    ((-Y ^ 2 * (2 * Y - 3)) / (12 * (Y - 1) ^ 2))
    ((-42 * Y ^ 4 + 97 * Y ^ 3 - 62 * Y ^ 2 + 12 * Y + 1) / (12 * Y ^ 2 * (Y - 1) ^ 4))
    (((2 * Y - 1) * (2 * Y ^ 2 - 2 * Y + 1)) / (4 * Y ^ 2 * (Y - 1) ^ 3))
    ((-16 * Y ^ 3 + 13 * Y ^ 2 - 8 * Y + 6) / (12 * Y ^ 2))
    ((-4 * Y ^ 3 + 19 * Y ^ 2 - 26 * Y + 7) / (24 * Y ^ 2))
    (((Y - 1) ^ 2) / (6 * Y ^ 2))
    ξ

theorem hasDerivAt_xiPA (Y : ℝ) {ξ : ℝ} (h0 : ξ ≠ 0) (h1 : ξ - 1 ≠ 0) :
    HasDerivAt (xiPA Y) (xiPAD Y ξ) ξ :=
  hasDerivAt_pfXi _ _ _ _ _ _ _ _ h0 h1

/-- The coefficient of `log (ξ + Y - 2 Y ξ)` in the `ξ`-antiderivative. -/
noncomputable def xiPB (Y ξ : ℝ) : ℝ :=
  pfXi
    ((108 * Y ^ 7 - 312 * Y ^ 6 + 162 * Y ^ 5 + 76 * Y ^ 4 - 5 * Y ^ 3 - 91 * Y ^ 2 + 53 * Y - 9) /
        (24 * Y ^ 2 * (Y - 1) ^ 3 * (2 * Y - 1)))
    ((-(2 * Y - 1) * (4 * Y ^ 5 - 10 * Y ^ 4 - Y ^ 3 + 9 * Y ^ 2 - 12 * Y + 4)) / (12 * Y * (Y -
        1) ^ 4))
    (((2 * Y - 1) * (2 * Y ^ 2 - 2 * Y - 1)) / (12 * (Y - 1) ^ 2))
    ((-Y * (4 * Y ^ 3 - 32 * Y ^ 2 + 45 * Y - 11)) / (12 * (Y - 1) ^ 4))
    ((-Y ^ 2) / (4 * (Y - 1) ^ 3))
    ((16 * Y ^ 3 - 13 * Y ^ 2 + 8 * Y - 6) / (12 * Y ^ 2))
    ((4 * Y ^ 3 - 19 * Y ^ 2 + 26 * Y - 7) / (24 * Y ^ 2))
    ((-(Y - 1) ^ 2) / (6 * Y ^ 2))
    ξ

/-- The `ξ`-derivative of `xiPB`. -/
noncomputable def xiPBD (Y ξ : ℝ) : ℝ :=
  pfXiD
    ((-(2 * Y - 1) * (4 * Y ^ 5 - 10 * Y ^ 4 - Y ^ 3 + 9 * Y ^ 2 - 12 * Y + 4)) / (12 * Y * (Y -
        1) ^ 4))
    (((2 * Y - 1) * (2 * Y ^ 2 - 2 * Y - 1)) / (12 * (Y - 1) ^ 2))
    ((-Y * (4 * Y ^ 3 - 32 * Y ^ 2 + 45 * Y - 11)) / (12 * (Y - 1) ^ 4))
    ((-Y ^ 2) / (4 * (Y - 1) ^ 3))
    ((16 * Y ^ 3 - 13 * Y ^ 2 + 8 * Y - 6) / (12 * Y ^ 2))
    ((4 * Y ^ 3 - 19 * Y ^ 2 + 26 * Y - 7) / (24 * Y ^ 2))
    ((-(Y - 1) ^ 2) / (6 * Y ^ 2))
    ξ

theorem hasDerivAt_xiPB (Y : ℝ) {ξ : ℝ} (h0 : ξ ≠ 0) (h1 : ξ - 1 ≠ 0) :
    HasDerivAt (xiPB Y) (xiPBD Y ξ) ξ :=
  hasDerivAt_pfXi _ _ _ _ _ _ _ _ h0 h1

/-- The coefficient of `log Y` in the `ξ`-antiderivative. -/
noncomputable def xiPY (Y ξ : ℝ) : ℝ :=
  pfXi
    0
    ((Y * (4 * Y ^ 4 - 12 * Y ^ 3 + 4 * Y ^ 2 - 5 * Y + 3)) / (12 * (Y - 1) ^ 4))
    ((-Y ^ 2 * (2 * Y - 3)) / (12 * (Y - 1) ^ 2))
    ((Y * (4 * Y ^ 3 - 32 * Y ^ 2 + 45 * Y - 11)) / (12 * (Y - 1) ^ 4))
    (Y ^ 2 / (4 * (Y - 1) ^ 3))
    0
    0
    0
    ξ

/-- The `ξ`-derivative of `xiPY`. -/
noncomputable def xiPYD (Y ξ : ℝ) : ℝ :=
  pfXiD
    ((Y * (4 * Y ^ 4 - 12 * Y ^ 3 + 4 * Y ^ 2 - 5 * Y + 3)) / (12 * (Y - 1) ^ 4))
    ((-Y ^ 2 * (2 * Y - 3)) / (12 * (Y - 1) ^ 2))
    ((Y * (4 * Y ^ 3 - 32 * Y ^ 2 + 45 * Y - 11)) / (12 * (Y - 1) ^ 4))
    (Y ^ 2 / (4 * (Y - 1) ^ 3))
    0
    0
    0
    ξ

theorem hasDerivAt_xiPY (Y : ℝ) {ξ : ℝ} (h0 : ξ ≠ 0) (h1 : ξ - 1 ≠ 0) :
    HasDerivAt (xiPY Y) (xiPYD Y ξ) ξ :=
  hasDerivAt_pfXi _ _ _ _ _ _ _ _ h0 h1

/-- The coefficient of `Li₂ (Y ξ)`. -/
noncomputable def xiCL (Y : ℝ) : ℝ :=
  ((8 * Y ^ 4 - 72 * Y ^ 3 + 83 * Y ^ 2 - 38 * Y + 7) / (12 * Y ^ 2 * (Y - 1) ^ 4))

/-- The coefficient of `Li₂ (1 - ξ) + Li(-Y (1 - ξ)/(1 - Y)) - Li((1 - 2Y)(1 - ξ)/(1 - Y))`. -/
noncomputable def xiCq (Y : ℝ) : ℝ :=
  ((-16 * Y ^ 3 - 4 * Y ^ 2 + 10 * Y - 7) / (12 * Y ^ 2))

/-- The coefficient of `Li((2Y - 1) ξ/Y)`. -/
noncomputable def xiCD (Y : ℝ) : ℝ :=
  ((-2 * Y ^ 5 + 15 * Y ^ 4 - 50 * Y ^ 3 + 89 * Y ^ 2 - 46 * Y + 6) / (12 * (Y - 1) ^ 4))

/-- The rational part of `Y Φ_X(Y ξ, Y (1 - ξ))`. -/
noncomputable def xiΦ1 (Y ξ : ℝ) : ℝ :=
  ((-2 * Y ^ 4 * ξ ^ 5 - 8 * Y ^ 4 * ξ ^ 4 + 18 * Y ^ 4 * ξ ^ 3 - 8 * Y ^ 4 * ξ ^ 2 + 4 * Y ^ 3 *
      ξ ^ 5 + 17 * Y ^ 3 * ξ ^ 4 - 39 * Y ^ 3 * ξ ^ 3 + 28 * Y ^ 3 * ξ ^ 2 - 4 * Y ^ 3 * ξ - 2 *
      Y ^ 2 * ξ ^ 5 + Y ^ 2 * ξ ^ 4 - 3 * Y ^ 2 * ξ ^ 3 - 34 * Y ^ 2 * ξ ^ 2 + 32 * Y ^ 2 * ξ - 12 *
      Y ^ 2 - 4 * Y * ξ ^ 4 + 8 * Y * ξ ^ 3 + 41 * Y * ξ ^ 2 - 45 * Y * ξ + 18 * Y - 2 * ξ ^ 3 - 9 *
      ξ ^ 2 + 11 * ξ - 6) / (12 * Y * ξ ^ 2 * (Y - 1) ^ 2 * (ξ - 1) ^ 2))

/-- The coefficient of `log Y` in `Y Φ_X(Y ξ, Y (1 - ξ))`. -/
noncomputable def xiΦY (Y ξ : ℝ) : ℝ :=
  ((-4 * Y ^ 5 * ξ ^ 4 + 4 * Y ^ 5 * ξ ^ 3 - 2 * Y ^ 5 * ξ ^ 2 + 14 * Y ^ 4 * ξ ^ 4 - 12 * Y ^ 4 *
      ξ ^ 3 + 15 * Y ^ 4 * ξ ^ 2 - 4 * Y ^ 4 * ξ - 16 * Y ^ 3 * ξ ^ 4 + 4 * Y ^ 3 * ξ ^ 3 - 50 *
      Y ^ 3 * ξ ^ 2 + 32 * Y ^ 3 * ξ - 6 * Y ^ 3 + 6 * Y ^ 2 * ξ ^ 4 - 5 * Y ^ 2 * ξ ^ 3 + 89 *
      Y ^ 2 * ξ ^ 2 - 45 * Y ^ 2 * ξ + 6 * Y ^ 2 + 3 * Y * ξ ^ 3 - 46 * Y * ξ ^ 2 + 11 * Y * ξ + 6 *
      ξ ^ 2) / (12 * ξ ^ 3 * (Y - 1) ^ 4))

/-- The coefficient of `log ξ` in `Y Φ_X(Y ξ, Y (1 - ξ))`. -/
noncomputable def xiΦx (Y ξ : ℝ) : ℝ :=
  ((-8 * Y ^ 3 * ξ ^ 6 + 44 * Y ^ 3 * ξ ^ 5 - 68 * Y ^ 3 * ξ ^ 4 + 40 * Y ^ 3 * ξ ^ 3 - 8 * Y ^ 3 *
      ξ ^ 2 - 4 * Y ^ 2 * ξ ^ 6 + 26 * Y ^ 2 * ξ ^ 5 - 60 * Y ^ 2 * ξ ^ 4 + 38 * Y ^ 2 * ξ ^ 3 - 5 *
      Y ^ 2 * ξ ^ 2 - Y ^ 2 * ξ - 8 * Y * ξ ^ 5 + 16 * Y * ξ ^ 4 + 22 * Y * ξ ^ 3 - 22 * Y * ξ ^ 2 +
      4 * Y * ξ + 2 * ξ ^ 4 - 13 * ξ ^ 3 + 7 * ξ ^ 2 - 2 * ξ) / (12 * Y ^ 2 * (ξ - 1) ^ 4 * (2 * ξ -
      1)))

/-- The coefficient of `log (1 - Y ξ)` in `Y Φ_X(Y ξ, Y (1 - ξ))`. -/
noncomputable def xiΦA (Y ξ : ℝ) : ℝ :=
  ((-4 * Y ^ 7 * ξ ^ 8 + 20 * Y ^ 7 * ξ ^ 7 - 24 * Y ^ 7 * ξ ^ 6 + 8 * Y ^ 7 * ξ ^ 5 + 14 * Y ^ 6 *
      ξ ^ 8 - 68 * Y ^ 6 * ξ ^ 7 + 72 * Y ^ 6 * ξ ^ 6 - 25 * Y ^ 6 * ξ ^ 5 + Y ^ 6 * ξ ^ 4 - 16 *
      Y ^ 5 * ξ ^ 8 + 68 * Y ^ 5 * ξ ^ 7 - 42 * Y ^ 5 * ξ ^ 6 + 34 * Y ^ 5 * ξ ^ 5 - 8 * Y ^ 5 *
      ξ ^ 4 + 6 * Y ^ 4 * ξ ^ 8 - 29 * Y ^ 4 * ξ ^ 7 + 55 * Y ^ 4 * ξ ^ 6 - 181 * Y ^ 4 * ξ ^ 5 -
      74 * Y ^ 4 * ξ ^ 4 + 339 * Y ^ 4 * ξ ^ 3 - 320 * Y ^ 4 * ξ ^ 2 + 138 * Y ^ 4 * ξ - 24 *
      Y ^ 4 + 3 * Y ^ 3 * ξ ^ 7 - 28 * Y ^ 3 * ξ ^ 6 + 37 * Y ^ 3 * ξ ^ 5 + 588 * Y ^ 3 * ξ ^ 4 -
      1023 * Y ^ 3 * ξ ^ 3 + 820 * Y ^ 3 * ξ ^ 2 - 337 * Y ^ 3 * ξ + 60 * Y ^ 3 + 3 * Y ^ 2 *
      ξ ^ 6 + 55 * Y ^ 2 * ξ ^ 5 - 551 * Y ^ 2 * ξ ^ 4 + 852 * Y ^ 2 * ξ ^ 3 - 691 * Y ^ 2 * ξ ^ 2 +
      302 * Y ^ 2 * ξ - 60 * Y ^ 2 - 18 * Y * ξ ^ 5 + 182 * Y * ξ ^ 4 - 292 * Y * ξ ^ 3 + 266 * Y *
      ξ ^ 2 - 132 * Y * ξ + 30 * Y - 18 * ξ ^ 4 + 34 * ξ ^ 3 - 39 * ξ ^ 2 + 23 * ξ - 6) / (12 *
      Y ^ 2 * ξ ^ 3 * (Y - 1) ^ 4 * (ξ - 1) ^ 4))

/-- The coefficient of `log (ξ + Y - 2 Y ξ)` in `Y Φ_X(Y ξ, Y (1 - ξ))`. -/
noncomputable def xiΦB (Y ξ : ℝ) : ℝ :=
  ((16 * Y ^ 7 * ξ ^ 9 - 88 * Y ^ 7 * ξ ^ 8 + 172 * Y ^ 7 * ξ ^ 7 - 178 * Y ^ 7 * ξ ^ 6 + 120 *
      Y ^ 7 * ξ ^ 5 - 56 * Y ^ 7 * ξ ^ 4 + 16 * Y ^ 7 * ξ ^ 3 - 2 * Y ^ 7 * ξ ^ 2 - 56 * Y ^ 6 *
      ξ ^ 9 + 300 * Y ^ 6 * ξ ^ 8 - 574 * Y ^ 6 * ξ ^ 7 + 653 * Y ^ 6 * ξ ^ 6 - 555 * Y ^ 6 *
      ξ ^ 5 + 361 * Y ^ 6 * ξ ^ 4 - 158 * Y ^ 6 * ξ ^ 3 + 39 * Y ^ 6 * ξ ^ 2 - 4 * Y ^ 6 * ξ + 64 *
      Y ^ 5 * ξ ^ 9 - 304 * Y ^ 5 * ξ ^ 8 + 544 * Y ^ 5 * ξ ^ 7 - 912 * Y ^ 5 * ξ ^ 6 + 1302 *
      Y ^ 5 * ξ ^ 5 - 1314 * Y ^ 5 * ξ ^ 4 + 848 * Y ^ 5 * ξ ^ 3 - 326 * Y ^ 5 * ξ ^ 2 + 68 *
      Y ^ 5 * ξ - 6 * Y ^ 5 - 20 * Y ^ 4 * ξ ^ 9 + 52 * Y ^ 4 * ξ ^ 8 - 169 * Y ^ 4 * ξ ^ 7 + 1088 *
      Y ^ 4 * ξ ^ 6 - 2044 * Y ^ 4 * ξ ^ 5 + 2080 * Y ^ 4 * ξ ^ 4 - 1265 * Y ^ 4 * ξ ^ 3 + 443 *
      Y ^ 4 * ξ ^ 2 - 81 * Y ^ 4 * ξ + 6 * Y ^ 4 - 8 * Y ^ 3 * ξ ^ 9 + 102 * Y ^ 3 * ξ ^ 8 - 141 *
      Y ^ 3 * ξ ^ 7 - 556 * Y ^ 3 * ξ ^ 6 + 1025 * Y ^ 3 * ξ ^ 5 - 874 * Y ^ 3 * ξ ^ 4 + 433 *
      Y ^ 3 * ξ ^ 3 - 112 * Y ^ 3 * ξ ^ 2 + 11 * Y ^ 3 * ξ + 4 * Y ^ 2 * ξ ^ 9 - 58 * Y ^ 2 *
      ξ ^ 8 + 100 * Y ^ 2 * ξ ^ 7 + 182 * Y ^ 2 * ξ ^ 6 - 221 * Y ^ 2 * ξ ^ 5 + 113 * Y ^ 2 *
      ξ ^ 4 - 36 * Y ^ 2 * ξ ^ 3 + 6 * Y ^ 2 * ξ ^ 2 + 8 * Y * ξ ^ 8 - 8 * Y * ξ ^ 7 - 74 * Y *
      ξ ^ 6 + 50 * Y * ξ ^ 5 - 12 * Y * ξ ^ 4 - 2 * ξ ^ 7 + 13 * ξ ^ 6 - 7 * ξ ^ 5 + 2 * ξ ^ 4) /
      (12 * Y ^ 2 * ξ ^ 3 * (Y - 1) ^ 4 * (ξ - 1) ^ 4 * (2 * ξ - 1)))

/-- **The `ξ`-antiderivative** of `Y Φ_X(Y ξ, Y (1 - ξ))` at fixed `Y`. -/
noncomputable def xiF (Y ξ : ℝ) : ℝ :=
  xiR0 Y ξ + xiPx Y ξ * log ξ + xiPA Y ξ * log (1 - Y * ξ) +
    xiPB Y ξ * log (ξ + Y - 2 * Y * ξ) + xiPY Y ξ * log Y + xiCL Y * Li₂ (Y * ξ) +
    xiCq Y * (Li₂ (1 - ξ) + dilogI (-(Y * (1 - ξ) / (1 - Y))) -
      dilogI ((1 - 2 * Y) * (1 - ξ) / (1 - Y))) +
    (Li₂ (1 - 2 * ξ) - Li₂ ((1 - 2 * Y) * (1 - 2 * ξ))) / (2 * Y ^ 2) +
    xiCD Y * dilogI ((2 * Y - 1) * ξ / Y)

end QED.TwoLoop.UnitXXi

end
