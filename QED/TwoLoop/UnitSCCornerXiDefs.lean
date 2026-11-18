/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXXiDefs
public import QED.TwoLoop.UnitSCCornerXDefs
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The `ξ`-integration of the corner unit: definitions

Step 6.6.2 of `docs/TWO-LOOP-UNITS.md`. In the variables `(Y, ξ)` the integrand of eq. (6.8) is

`Y Φ_C(Y, ξ) = R₁ + R_Y log Y + R_ξ log ξ + R_A log (1 - Y ξ) + R_B log (ξ + Y - 2 Y ξ)`,

with rational coefficients `cxiΦ1`, `cxiΦY`, `cxiΦx`, `cxiΦA`, `cxiΦB` (`Y` times the coefficients
of
`QED.TwoLoop.UnitSCCorner.cornerPhi`): the letters of `Φ_X`. This file states an antiderivative
in `ξ` at fixed `Y` (`cxiF`) of the same shape as `QED.TwoLoop.UnitXXi.xiF`:

`F = P₀ + P_ξ log ξ + P_A log (1 - Y ξ) + P_B log (ξ + Y - 2 Y ξ) + P_Y log Y + c_L Li₂ (Y ξ)
  + c_q (Li₂ (1 - ξ) + Li(-Y (1 - ξ)/(1 - Y)) - Li((1 - 2Y)(1 - ξ)/(1 - Y)))
  + (Li₂ ((1 - 2Y)(1 - 2ξ)) - Li₂ (1 - 2ξ))/(2 Y²) + c_D Li((2Y - 1) ξ/Y)`,

each `P` a partial-fraction form `QED.TwoLoop.UnitXXi.pfXi`. The coefficients were computed in exact
rational arithmetic by `scripts/numerics/sc_graph/corner_integration.py`, which also checks every
identity used below and that the endpoint values give `K_C` exactly.
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog

namespace QED.TwoLoop.UnitSCCornerXi

open QED.TwoLoop.UnitXClose QED.TwoLoop.UnitXXi QED.TwoLoop.UnitSCCorner

/-- The rational part of the `ξ`-antiderivative. -/
noncomputable def cxiR0 (Y ξ : ℝ) : ℝ :=
  pfXi
    0
    ((7 * Y) / 8)
    0
    ((2 * Y - 3) / (12 * Y))
    0
    ((Y - 1) / (6 * Y))
    0
    0
    ξ

/-- The `ξ`-derivative of `cxiR0`. -/
noncomputable def cxiR0D (Y ξ : ℝ) : ℝ :=
  pfXiD
    ((7 * Y) / 8)
    0
    ((2 * Y - 3) / (12 * Y))
    0
    ((Y - 1) / (6 * Y))
    0
    0
    ξ

theorem hasDerivAt_cxiR0 (Y : ℝ) {ξ : ℝ} (h0 : ξ ≠ 0) (h1 : ξ - 1 ≠ 0) :
    HasDerivAt (cxiR0 Y) (cxiR0D Y ξ) ξ :=
  hasDerivAt_pfXi _ _ _ _ _ _ _ _ h0 h1

/-- The coefficient of `log ξ` in the `ξ`-antiderivative. -/
noncomputable def cxiPx (Y ξ : ℝ) : ℝ :=
  pfXi
    ((5 * Y ^ 3 - 14 * Y ^ 2 + 5 * Y - 5) / (12 * Y ^ 2))
    ((-Y) / 4)
    0
    0
    0
    ((2 * Y ^ 3 - 8 * Y ^ 2 + 5 * Y - 2) / (4 * Y ^ 2))
    (((Y - 1) * (Y ^ 2 - 11 * Y + 3)) / (12 * Y ^ 2))
    ((-(Y - 1) ^ 2) / (6 * Y ^ 2))
    ξ

/-- The `ξ`-derivative of `cxiPx`. -/
noncomputable def cxiPxD (Y ξ : ℝ) : ℝ :=
  pfXiD
    ((-Y) / 4)
    0
    0
    0
    ((2 * Y ^ 3 - 8 * Y ^ 2 + 5 * Y - 2) / (4 * Y ^ 2))
    (((Y - 1) * (Y ^ 2 - 11 * Y + 3)) / (12 * Y ^ 2))
    ((-(Y - 1) ^ 2) / (6 * Y ^ 2))
    ξ

theorem hasDerivAt_cxiPx (Y : ℝ) {ξ : ℝ} (h0 : ξ ≠ 0) (h1 : ξ - 1 ≠ 0) :
    HasDerivAt (cxiPx Y) (cxiPxD Y ξ) ξ :=
  hasDerivAt_pfXi _ _ _ _ _ _ _ _ h0 h1

/-- The coefficient of `log (1 - Y ξ)` in the `ξ`-antiderivative. -/
noncomputable def cxiPA (Y ξ : ℝ) : ℝ :=
  pfXi
    (((Y - 2) * (5 * Y ^ 3 - Y ^ 2 + Y - 3)) / (12 * Y * (Y - 1) ^ 2))
    ((-Y) / 4)
    0
    ((10 * Y - 7) / (12 * Y * (Y - 1) ^ 2))
    ((-6 * Y ^ 2 + 8 * Y - 3) / (12 * Y ^ 2 * (Y - 1) ^ 2))
    ((2 * Y ^ 3 - 8 * Y ^ 2 + 5 * Y - 2) / (4 * Y ^ 2))
    (((Y - 1) * (Y ^ 2 - 11 * Y + 3)) / (12 * Y ^ 2))
    ((-(Y - 1) ^ 2) / (6 * Y ^ 2))
    ξ

/-- The `ξ`-derivative of `cxiPA`. -/
noncomputable def cxiPAD (Y ξ : ℝ) : ℝ :=
  pfXiD
    ((-Y) / 4)
    0
    ((10 * Y - 7) / (12 * Y * (Y - 1) ^ 2))
    ((-6 * Y ^ 2 + 8 * Y - 3) / (12 * Y ^ 2 * (Y - 1) ^ 2))
    ((2 * Y ^ 3 - 8 * Y ^ 2 + 5 * Y - 2) / (4 * Y ^ 2))
    (((Y - 1) * (Y ^ 2 - 11 * Y + 3)) / (12 * Y ^ 2))
    ((-(Y - 1) ^ 2) / (6 * Y ^ 2))
    ξ

theorem hasDerivAt_cxiPA (Y : ℝ) {ξ : ℝ} (h0 : ξ ≠ 0) (h1 : ξ - 1 ≠ 0) :
    HasDerivAt (cxiPA Y) (cxiPAD Y ξ) ξ :=
  hasDerivAt_pfXi _ _ _ _ _ _ _ _ h0 h1

/-- The coefficient of `log (ξ + Y - 2 Y ξ)` in the `ξ`-antiderivative. -/
noncomputable def cxiPB (Y ξ : ℝ) : ℝ :=
  pfXi
    ((-(2 * Y - 1) * (6 * Y ^ 4 - 19 * Y ^ 3 + 17 * Y ^ 2 - 11 * Y + 5)) / (12 * Y ^ 2 * (Y -
        1) ^ 2))
    0
    0
    ((Y * (2 * Y ^ 2 - 8 * Y + 3)) / (12 * (Y - 1) ^ 2))
    (Y ^ 2 / (12 * (Y - 1) ^ 2))
    ((-2 * Y ^ 3 + 8 * Y ^ 2 - 5 * Y + 2) / (4 * Y ^ 2))
    ((-(Y - 1) * (Y ^ 2 - 11 * Y + 3)) / (12 * Y ^ 2))
    (((Y - 1) ^ 2) / (6 * Y ^ 2))
    ξ

/-- The `ξ`-derivative of `cxiPB`. -/
noncomputable def cxiPBD (Y ξ : ℝ) : ℝ :=
  pfXiD
    0
    0
    ((Y * (2 * Y ^ 2 - 8 * Y + 3)) / (12 * (Y - 1) ^ 2))
    (Y ^ 2 / (12 * (Y - 1) ^ 2))
    ((-2 * Y ^ 3 + 8 * Y ^ 2 - 5 * Y + 2) / (4 * Y ^ 2))
    ((-(Y - 1) * (Y ^ 2 - 11 * Y + 3)) / (12 * Y ^ 2))
    (((Y - 1) ^ 2) / (6 * Y ^ 2))
    ξ

theorem hasDerivAt_cxiPB (Y : ℝ) {ξ : ℝ} (h0 : ξ ≠ 0) (h1 : ξ - 1 ≠ 0) :
    HasDerivAt (cxiPB Y) (cxiPBD Y ξ) ξ :=
  hasDerivAt_pfXi _ _ _ _ _ _ _ _ h0 h1

/-- The coefficient of `log Y` in the `ξ`-antiderivative. -/
noncomputable def cxiPY (Y ξ : ℝ) : ℝ :=
  pfXi
    0
    ((-Y) / 4)
    0
    ((-Y * (2 * Y ^ 2 - 8 * Y + 3)) / (12 * (Y - 1) ^ 2))
    ((-Y ^ 2) / (12 * (Y - 1) ^ 2))
    0
    0
    0
    ξ

/-- The `ξ`-derivative of `cxiPY`. -/
noncomputable def cxiPYD (Y ξ : ℝ) : ℝ :=
  pfXiD
    ((-Y) / 4)
    0
    ((-Y * (2 * Y ^ 2 - 8 * Y + 3)) / (12 * (Y - 1) ^ 2))
    ((-Y ^ 2) / (12 * (Y - 1) ^ 2))
    0
    0
    0
    ξ

theorem hasDerivAt_cxiPY (Y : ℝ) {ξ : ℝ} (h0 : ξ ≠ 0) (h1 : ξ - 1 ≠ 0) :
    HasDerivAt (cxiPY Y) (cxiPYD Y ξ) ξ :=
  hasDerivAt_pfXi _ _ _ _ _ _ _ _ h0 h1

/-- The coefficient of `Li₂ (Y ξ)`. -/
noncomputable def cxiCL (Y : ℝ) : ℝ :=
  ((-4 * Y + 3) / (6 * Y ^ 2 * (Y - 1)))

/-- The coefficient of `Li₂ (1 - ξ) + Li(-Y (1 - ξ)/(1 - Y)) - Li((1 - 2Y)(1 - ξ)/(1 - Y))`. -/
noncomputable def cxiCq (Y : ℝ) : ℝ :=
  ((2 * Y ^ 3 - Y ^ 2 - Y + 3) / (6 * Y ^ 2))

/-- The coefficient of `Li((2Y - 1) ξ/Y)`. -/
noncomputable def cxiCD (Y : ℝ) : ℝ :=
  ((-Y * (2 * Y - 3)) / (6 * Y - 6))

/-- The rational part of `Y Φ_C(Y, ξ)`. -/
noncomputable def cxiΦ1 (Y ξ : ℝ) : ℝ :=
  ((9 * Y ^ 2 * ξ ^ 4 - 22 * Y ^ 2 * ξ ^ 3 + 21 * Y ^ 2 * ξ ^ 2 - 8 * Y ^ 2 * ξ + 4 * Y * ξ ^ 3 -
      48 * Y * ξ ^ 2 + 40 * Y * ξ - 8 * Y + 24 * ξ ^ 2 - 24 * ξ + 12) / (24 * Y * ξ ^ 2 * (ξ -
      1) ^ 2))

/-- The coefficient of `log Y` in `Y Φ_C(Y, ξ)`. -/
noncomputable def cxiΦY (Y ξ : ℝ) : ℝ :=
  ((-3 * Y ^ 3 * ξ ^ 3 - 4 * Y ^ 3 * ξ ^ 2 + 2 * Y ^ 3 * ξ + 6 * Y ^ 2 * ξ ^ 3 + 10 * Y ^ 2 *
      ξ ^ 2 - 8 * Y ^ 2 * ξ + 2 * Y ^ 2 - 3 * Y * ξ ^ 3 - 6 * Y * ξ ^ 2 + 3 * Y * ξ) / (12 * ξ ^ 3 *
      (Y - 1) ^ 2))

/-- The coefficient of `log ξ` in `Y Φ_C(Y, ξ)`. -/
noncomputable def cxiΦx (Y ξ : ℝ) : ℝ :=
  ((-6 * Y ^ 3 * ξ ^ 5 + 19 * Y ^ 3 * ξ ^ 4 - 32 * Y ^ 3 * ξ ^ 3 + 32 * Y ^ 3 * ξ ^ 2 - 16 * Y ^ 3 *
      ξ + 3 * Y ^ 3 + 4 * Y ^ 2 * ξ ^ 4 + 34 * Y ^ 2 * ξ ^ 3 - 54 * Y ^ 2 * ξ ^ 2 + 26 * Y ^ 2 * ξ -
      4 * Y ^ 2 + 4 * Y * ξ ^ 4 - 44 * Y * ξ ^ 3 + 37 * Y * ξ ^ 2 - 10 * Y * ξ + Y + 6 * ξ ^ 3) /
      (12 * Y ^ 2 * (ξ - 1) ^ 4 * (2 * ξ - 1)))

/-- The coefficient of `log (1 - Y ξ)` in `Y Φ_C(Y, ξ)`. -/
noncomputable def cxiΦA (Y ξ : ℝ) : ℝ :=
  ((-3 * Y ^ 5 * ξ ^ 7 + 8 * Y ^ 5 * ξ ^ 6 - 12 * Y ^ 5 * ξ ^ 5 + 10 * Y ^ 5 * ξ ^ 4 - 3 * Y ^ 5 *
      ξ ^ 3 + 6 * Y ^ 4 * ξ ^ 7 - 14 * Y ^ 4 * ξ ^ 6 + 42 * Y ^ 4 * ξ ^ 5 - 38 * Y ^ 4 * ξ ^ 4 +
      10 * Y ^ 4 * ξ ^ 3 - 3 * Y ^ 3 * ξ ^ 7 + 6 * Y ^ 3 * ξ ^ 6 - 69 * Y ^ 3 * ξ ^ 5 + 54 * Y ^ 3 *
      ξ ^ 4 - 12 * Y ^ 3 * ξ ^ 3 + 42 * Y ^ 2 * ξ ^ 5 + 42 * Y ^ 2 * ξ ^ 4 - 122 * Y ^ 2 * ξ ^ 3 +
      120 * Y ^ 2 * ξ ^ 2 - 58 * Y ^ 2 * ξ + 12 * Y ^ 2 - 6 * Y * ξ ^ 5 - 72 * Y * ξ ^ 4 + 137 * Y *
      ξ ^ 3 - 138 * Y * ξ ^ 2 + 71 * Y * ξ - 16 * Y + 18 * ξ ^ 4 - 36 * ξ ^ 3 + 42 * ξ ^ 2 - 24 *
      ξ + 6) / (12 * Y ^ 2 * ξ ^ 3 * (Y - 1) ^ 2 * (ξ - 1) ^ 4))

/-- The coefficient of `log (ξ + Y - 2 Y ξ)` in `Y Φ_C(Y, ξ)`. -/
noncomputable def cxiΦB (Y ξ : ℝ) : ℝ :=
  ((16 * Y ^ 5 * ξ ^ 7 - 56 * Y ^ 5 * ξ ^ 6 + 92 * Y ^ 5 * ξ ^ 5 - 90 * Y ^ 5 * ξ ^ 4 + 52 * Y ^ 5 *
      ξ ^ 3 - 16 * Y ^ 5 * ξ ^ 2 + 2 * Y ^ 5 * ξ - 40 * Y ^ 4 * ξ ^ 7 + 104 * Y ^ 4 * ξ ^ 6 - 202 *
      Y ^ 4 * ξ ^ 5 + 264 * Y ^ 4 * ξ ^ 4 - 200 * Y ^ 4 * ξ ^ 3 + 86 * Y ^ 4 * ξ ^ 2 - 20 * Y ^ 4 *
      ξ + 2 * Y ^ 4 + 24 * Y ^ 3 * ξ ^ 7 + 36 * Y ^ 3 * ξ ^ 6 - 12 * Y ^ 3 * ξ ^ 5 - 72 * Y ^ 3 *
      ξ ^ 4 + 69 * Y ^ 3 * ξ ^ 3 - 24 * Y ^ 3 * ξ ^ 2 + 3 * Y ^ 3 * ξ + 4 * Y ^ 2 * ξ ^ 7 - 128 *
      Y ^ 2 * ξ ^ 6 + 128 * Y ^ 2 * ξ ^ 5 - 46 * Y ^ 2 * ξ ^ 4 + 6 * Y ^ 2 * ξ ^ 3 - 4 * Y * ξ ^ 7 +
      56 * Y * ξ ^ 6 - 37 * Y * ξ ^ 5 + 10 * Y * ξ ^ 4 - Y * ξ ^ 3 - 6 * ξ ^ 6) / (12 * Y ^ 2 *
      ξ ^ 3 * (Y - 1) ^ 2 * (ξ - 1) ^ 4 * (2 * ξ - 1)))

/-- **The `ξ`-antiderivative** of `Y Φ_C(Y, ξ)` at fixed `Y`. -/
noncomputable def cxiF (Y ξ : ℝ) : ℝ :=
  cxiR0 Y ξ + cxiPx Y ξ * log ξ + cxiPA Y ξ * log (1 - Y * ξ) +
    cxiPB Y ξ * log (ξ + Y - 2 * Y * ξ) + cxiPY Y ξ * log Y + cxiCL Y * Li₂ (Y * ξ) +
    cxiCq Y * (Li₂ (1 - ξ) + dilogI (-(Y * (1 - ξ) / (1 - Y))) -
      dilogI ((1 - 2 * Y) * (1 - ξ) / (1 - Y))) +
    (Li₂ ((1 - 2 * Y) * (1 - 2 * ξ)) - Li₂ (1 - 2 * ξ)) / (2 * Y ^ 2) +
    cxiCD Y * dilogI ((2 * Y - 1) * ξ / Y)

end QED.TwoLoop.UnitSCCornerXi

end
