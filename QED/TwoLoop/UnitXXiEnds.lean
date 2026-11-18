/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXXiRat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The `ξ`-antiderivative near `ξ = 0` and `ξ = 1`

The coefficients of `QED.TwoLoop.UnitXXi.xiF` have poles of order two at `ξ = 0` and of order three
at `ξ = 1`; the poles cancel against the Taylor polynomials of the logarithms. This file writes
`xiF` in two endpoint forms with coefficients regular at the endpoint:

* `xiF_eq_zero_form`, for `ξ ∈ (0, 1)`:
  `xiF = U₀ + W₀ log Y + V₀ (ξ log ξ) + A₀ lr2 (Y ξ)/ξ² + B₀ lr2 ((2Y - 1) ξ/Y)/ξ² + xiDil`;
* `xiF_eq_one_form`, for `ξ ∈ (0, 1)`, with `t = 1 - ξ`:
  `xiF = U₁ + W₁' log Y + W₁ log (1 - Y) + X₁ lr3 t/t³ + A₁ lr3 (-Y t/(1 - Y))/t³
    + B₁ lr3 ((1 - 2Y) t/(1 - Y))/t³ + xiDil`.

Here `lr2 z = log (1 - z) + z + z²/2` and `lr3 z = lr2 z + z³/3` are Taylor remainders, and
`xiDil` collects the dilogarithm terms of `xiF`. The coefficients are rational functions computed
by `scripts/numerics/crossed_graph/xi_integration.py`; the identities are checked by `field_simp`
and `ring`, one logarithm at a time.
-/

@[expose] public section

open Real Set QED.Polylog

namespace QED.TwoLoop.UnitXXi

open QED.TwoLoop.UnitXClose

/-- `log (1 - z) + z + z²/2`. -/
noncomputable def lr2 (z : ℝ) : ℝ := log (1 - z) + z + z ^ 2 / 2

/-- `log (1 - z) + z + z²/2 + z³/3`. -/
noncomputable def lr3 (z : ℝ) : ℝ := log (1 - z) + z + z ^ 2 / 2 + z ^ 3 / 3

/-- The dilogarithm terms of `xiF`. -/
noncomputable def xiDil (Y ξ : ℝ) : ℝ :=
  xiCL Y * Li₂ (Y * ξ) +
    xiCq Y * (Li₂ (1 - ξ) + dilogI (-(Y * (1 - ξ) / (1 - Y))) -
      dilogI ((1 - 2 * Y) * (1 - ξ) / (1 - Y))) +
    (Li₂ (1 - 2 * ξ) - Li₂ ((1 - 2 * Y) * (1 - 2 * ξ))) / (2 * Y ^ 2) +
    xiCD Y * dilogI ((2 * Y - 1) * ξ / Y)

/-- The rational part of `xiF` at `ξ → 0⁺`. -/
noncomputable def xiU0 (Y ξ : ℝ) : ℝ :=
  ((4 * Y ^ 9 * ξ ^ 7 - 20 * Y ^ 9 * ξ ^ 6 + 64 * Y ^ 9 * ξ ^ 5 - 80 * Y ^ 9 * ξ ^ 4 + 32 * Y ^ 9 *
      ξ ^ 3 - 6 * Y ^ 8 * ξ ^ 7 + 34 * Y ^ 8 * ξ ^ 6 - 93 * Y ^ 8 * ξ ^ 5 + 101 * Y ^ 8 * ξ ^ 4 -
      48 * Y ^ 8 * ξ ^ 3 + 8 * Y ^ 8 * ξ ^ 2 - 32 * Y ^ 7 * ξ ^ 7 + 132 * Y ^ 7 * ξ ^ 6 - 432 *
      Y ^ 7 * ξ ^ 5 + 502 * Y ^ 7 * ξ ^ 4 - 38 * Y ^ 7 * ξ ^ 3 - 172 * Y ^ 7 * ξ ^ 2 + 48 * Y ^ 7 *
      ξ + 80 * Y ^ 6 * ξ ^ 7 - 270 * Y ^ 6 * ξ ^ 6 + 797 * Y ^ 6 * ξ ^ 5 - 689 * Y ^ 6 * ξ ^ 4 -
      119 * Y ^ 6 * ξ ^ 3 + 261 * Y ^ 6 * ξ ^ 2 - 4 * Y ^ 6 * ξ - 16 * Y ^ 6 - 56 * Y ^ 5 * ξ ^ 7 +
      142 * Y ^ 5 * ξ ^ 6 - 246 * Y ^ 5 * ξ ^ 5 - 478 * Y ^ 5 * ξ ^ 4 + 510 * Y ^ 5 * ξ ^ 3 + 162 *
      Y ^ 5 * ξ ^ 2 - 246 * Y ^ 5 * ξ + 28 * Y ^ 5 + 4 * Y ^ 4 * ξ ^ 7 + 110 * Y ^ 4 * ξ ^ 6 - 366 *
      Y ^ 4 * ξ ^ 5 + 1196 * Y ^ 4 * ξ ^ 4 - 654 * Y ^ 4 * ξ ^ 3 - 98 * Y ^ 4 * ξ ^ 2 + 128 *
      Y ^ 4 * ξ + 8 * Y ^ 3 * ξ ^ 7 - 158 * Y ^ 3 * ξ ^ 6 + 304 * Y ^ 3 * ξ ^ 5 - 700 * Y ^ 3 *
      ξ ^ 4 + 328 * Y ^ 3 * ξ ^ 3 - 64 * Y ^ 3 * ξ ^ 2 - 26 * Y ^ 3 * ξ + 12 * Y ^ 3 - 2 * Y ^ 2 *
      ξ ^ 7 + 62 * Y ^ 2 * ξ ^ 6 - 23 * Y ^ 2 * ξ ^ 5 + 83 * Y ^ 2 * ξ ^ 4 - 29 * Y ^ 2 * ξ ^ 3 +
      81 * Y ^ 2 * ξ ^ 2 - 20 * Y ^ 2 * ξ - 8 * Y * ξ ^ 6 - 38 * Y * ξ ^ 5 + 56 * Y * ξ ^ 4 - 40 *
      Y * ξ ^ 3 - 10 * Y * ξ ^ 2 + 9 * ξ ^ 5 - 15 * ξ ^ 4 + 10 * ξ ^ 3) / (48 * Y ^ 4 * (Y -
      1) ^ 2 * (ξ - 1) ^ 3))

/-- The coefficient of `log Y` in `xiF` at `ξ → 0⁺`. -/
noncomputable def xiW0 (Y ξ : ℝ) : ℝ :=
  ((8 * Y ^ 7 * ξ ^ 5 - 40 * Y ^ 7 * ξ ^ 4 + 180 * Y ^ 7 * ξ ^ 3 - 316 * Y ^ 7 * ξ ^ 2 + 220 *
      Y ^ 7 * ξ - 52 * Y ^ 7 - 24 * Y ^ 6 * ξ ^ 5 + 112 * Y ^ 6 * ξ ^ 4 - 504 * Y ^ 6 * ξ ^ 3 +
      804 * Y ^ 6 * ξ ^ 2 - 490 * Y ^ 6 * ξ + 94 * Y ^ 6 + 22 * Y ^ 5 * ξ ^ 5 - 66 * Y ^ 5 * ξ ^ 4 +
      228 * Y ^ 5 * ξ ^ 3 - 6 * Y ^ 5 * ξ ^ 2 - 297 * Y ^ 5 * ξ + 163 * Y ^ 5 - 2 * Y ^ 4 * ξ ^ 5 -
      82 * Y ^ 4 * ξ ^ 4 + 334 * Y ^ 4 * ξ ^ 3 - 1020 * Y ^ 4 * ξ ^ 2 + 989 * Y ^ 4 * ξ - 319 *
      Y ^ 4 - 6 * Y ^ 3 * ξ ^ 5 + 122 * Y ^ 3 * ξ ^ 4 - 335 * Y ^ 3 * ξ ^ 3 + 723 * Y ^ 3 * ξ ^ 2 -
      517 * Y ^ 3 * ξ + 133 * Y ^ 3 + 2 * Y ^ 2 * ξ ^ 5 - 54 * Y ^ 2 * ξ ^ 4 + 59 * Y ^ 2 * ξ ^ 3 -
      87 * Y ^ 2 * ξ ^ 2 - 9 * Y ^ 2 * ξ + 9 * Y ^ 2 + 8 * Y * ξ ^ 4 + 29 * Y * ξ ^ 3 - 59 * Y *
      ξ ^ 2 + 60 * Y * ξ - 10 * Y - 9 * ξ ^ 3 + 15 * ξ ^ 2 - 10 * ξ) / (24 * Y ^ 2 * (Y - 1) ^ 3 *
      (2 * Y - 1) * (ξ - 1) ^ 3))

/-- The coefficient of `ξ log ξ` in `xiF` at `ξ → 0⁺`. -/
noncomputable def xiV0 (Y ξ : ℝ) : ℝ :=
  ((-4 * Y ^ 3 * ξ ^ 4 + 20 * Y ^ 3 * ξ ^ 3 - 64 * Y ^ 3 * ξ ^ 2 + 80 * Y ^ 3 * ξ - 32 * Y ^ 3 - 2 *
      Y ^ 2 * ξ ^ 4 + 14 * Y ^ 2 * ξ ^ 3 - 19 * Y ^ 2 * ξ ^ 2 + 19 * Y ^ 2 * ξ - 8 * Y ^ 2 - 8 * Y *
      ξ ^ 3 + 26 * Y * ξ ^ 2 - 46 * Y * ξ + 20 * Y + 9 * ξ ^ 2 - 15 * ξ + 10) / (24 * Y ^ 2 * (ξ -
      1) ^ 3))

/-- The coefficient of `lr2 (Y ξ)/ξ²` in `xiF` at `ξ → 0⁺`. -/
noncomputable def xiA0 (Y ξ : ℝ) : ℝ :=
  ((-4 * Y ^ 7 * ξ ^ 7 + 20 * Y ^ 7 * ξ ^ 6 - 64 * Y ^ 7 * ξ ^ 5 + 80 * Y ^ 7 * ξ ^ 4 - 32 * Y ^ 7 *
      ξ ^ 3 + 14 * Y ^ 6 * ξ ^ 7 - 66 * Y ^ 6 * ξ ^ 6 + 181 * Y ^ 6 * ξ ^ 5 - 133 * Y ^ 6 * ξ ^ 4 -
      48 * Y ^ 6 * ξ ^ 3 + 56 * Y ^ 6 * ξ ^ 2 - 16 * Y ^ 5 * ξ ^ 7 + 56 * Y ^ 5 * ξ ^ 6 - 34 *
      Y ^ 5 * ξ ^ 5 - 386 * Y ^ 5 * ξ ^ 4 + 604 * Y ^ 5 * ξ ^ 3 - 248 * Y ^ 5 * ξ ^ 2 + 6 * Y ^ 4 *
      ξ ^ 7 - 28 * Y ^ 4 * ξ ^ 6 - 124 * Y ^ 4 * ξ ^ 5 + 756 * Y ^ 4 * ξ ^ 4 - 709 * Y ^ 4 * ξ ^ 3 +
      27 * Y ^ 4 * ξ ^ 2 + 156 * Y ^ 4 * ξ - 24 * Y ^ 4 + 6 * Y ^ 3 * ξ ^ 6 + 88 * Y ^ 3 * ξ ^ 5 -
      386 * Y ^ 3 * ξ ^ 4 - 34 * Y ^ 3 * ξ ^ 3 + 560 * Y ^ 3 * ξ ^ 2 - 374 * Y ^ 3 * ξ + 60 *
      Y ^ 3 + 3 * Y ^ 2 * ξ ^ 5 + 29 * Y ^ 2 * ξ ^ 4 + 282 * Y ^ 2 * ξ ^ 3 - 498 * Y ^ 2 * ξ ^ 2 +
      304 * Y ^ 2 * ξ - 60 * Y ^ 2 - 14 * Y * ξ ^ 5 + 2 * Y * ξ ^ 4 - 70 * Y * ξ ^ 3 + 142 * Y *
      ξ ^ 2 - 114 * Y * ξ + 30 * Y + 14 * ξ ^ 4 - 17 * ξ ^ 3 - 3 * ξ ^ 2 + 16 * ξ - 6) / (24 *
      Y ^ 2 * (Y - 1) ^ 4 * (ξ - 1) ^ 3))

/-- The coefficient of `lr2 ((2Y - 1) ξ/Y)/ξ²` in `xiF` at `ξ → 0⁺`. -/
noncomputable def xiB0 (Y ξ : ℝ) : ℝ :=
  ((16 * Y ^ 8 * ξ ^ 7 - 80 * Y ^ 8 * ξ ^ 6 + 252 * Y ^ 8 * ξ ^ 5 - 372 * Y ^ 8 * ξ ^ 4 + 236 *
      Y ^ 8 * ξ ^ 3 - 52 * Y ^ 8 * ξ ^ 2 - 64 * Y ^ 7 * ξ ^ 7 + 304 * Y ^ 7 * ξ ^ 6 - 948 * Y ^ 7 *
      ξ ^ 5 + 1304 * Y ^ 7 * ξ ^ 4 - 718 * Y ^ 7 * ξ ^ 3 + 98 * Y ^ 7 * ξ ^ 2 + 16 * Y ^ 7 * ξ +
      92 * Y ^ 6 * ξ ^ 7 - 356 * Y ^ 6 * ξ ^ 6 + 990 * Y ^ 6 * ξ ^ 5 - 840 * Y ^ 6 * ξ ^ 4 - 187 *
      Y ^ 6 * ξ ^ 3 + 513 * Y ^ 6 * ξ ^ 2 - 172 * Y ^ 6 * ξ + 12 * Y ^ 6 - 52 * Y ^ 5 * ξ ^ 7 + 96 *
      Y ^ 5 * ξ ^ 6 - 62 * Y ^ 5 * ξ ^ 5 - 1146 * Y ^ 5 * ξ ^ 4 + 2008 * Y ^ 5 * ξ ^ 3 - 1268 *
      Y ^ 5 * ξ ^ 2 + 298 * Y ^ 5 * ξ - 18 * Y ^ 5 + 2 * Y ^ 4 * ξ ^ 7 + 164 * Y ^ 4 * ξ ^ 6 - 585 *
      Y ^ 4 * ξ ^ 5 + 1805 * Y ^ 4 * ξ ^ 4 - 1892 * Y ^ 4 * ξ ^ 3 + 872 * Y ^ 4 * ξ ^ 2 - 152 *
      Y ^ 4 * ξ + 6 * Y ^ 4 + 8 * Y ^ 3 * ξ ^ 7 - 170 * Y ^ 3 * ξ ^ 6 + 376 * Y ^ 3 * ξ ^ 5 - 814 *
      Y ^ 3 * ξ ^ 4 + 568 * Y ^ 3 * ξ ^ 3 - 190 * Y ^ 3 * ξ ^ 2 + 22 * Y ^ 3 * ξ - 2 * Y ^ 2 *
      ξ ^ 7 + 62 * Y ^ 2 * ξ ^ 6 - 30 * Y ^ 2 * ξ ^ 5 + 28 * Y ^ 2 * ξ ^ 4 + 69 * Y ^ 2 * ξ ^ 3 -
      19 * Y ^ 2 * ξ ^ 2 - 8 * Y * ξ ^ 6 - 38 * Y * ξ ^ 5 + 74 * Y * ξ ^ 4 - 70 * Y * ξ ^ 3 + 10 *
      Y * ξ ^ 2 + 9 * ξ ^ 5 - 15 * ξ ^ 4 + 10 * ξ ^ 3) / (24 * Y ^ 2 * (Y - 1) ^ 4 * (2 * Y - 1) *
      (ξ - 1) ^ 3))

/-- The rational part of `xiF` at `ξ → 1⁻`. -/
noncomputable def xiU1 (Y ξ : ℝ) : ℝ :=
  ((56 * Y ^ 8 * ξ ^ 7 - 316 * Y ^ 8 * ξ ^ 6 + 1048 * Y ^ 8 * ξ ^ 5 - 1826 * Y ^ 8 * ξ ^ 4 + 1456 *
      Y ^ 8 * ξ ^ 3 - 520 * Y ^ 8 * ξ ^ 2 - 224 * Y ^ 7 * ξ ^ 7 + 1226 * Y ^ 7 * ξ ^ 6 - 4042 *
      Y ^ 7 * ξ ^ 5 + 6865 * Y ^ 7 * ξ ^ 4 - 5024 * Y ^ 7 * ξ ^ 3 + 1678 * Y ^ 7 * ξ ^ 2 + 160 *
      Y ^ 7 * ξ + 330 * Y ^ 6 * ξ ^ 7 - 1562 * Y ^ 6 * ξ ^ 6 + 4561 * Y ^ 6 * ξ ^ 5 - 6002 * Y ^ 6 *
      ξ ^ 4 + 1037 * Y ^ 6 * ξ ^ 3 + 1553 * Y ^ 6 * ξ ^ 2 - 1648 * Y ^ 6 * ξ + 120 * Y ^ 6 - 206 *
      Y ^ 5 * ξ ^ 7 + 658 * Y ^ 5 * ξ ^ 6 - 710 * Y ^ 5 * ξ ^ 5 - 3795 * Y ^ 5 * ξ ^ 4 + 11930 *
      Y ^ 5 * ξ ^ 3 - 9442 * Y ^ 5 * ξ ^ 2 + 3998 * Y ^ 5 * ξ - 366 * Y ^ 5 + 32 * Y ^ 4 * ξ ^ 7 +
      358 * Y ^ 4 * ξ ^ 6 - 2420 * Y ^ 4 * ξ ^ 5 + 9182 * Y ^ 4 * ξ ^ 4 - 16051 * Y ^ 4 * ξ ^ 3 +
      11162 * Y ^ 4 * ξ ^ 2 - 4153 * Y ^ 4 * ξ + 531 * Y ^ 4 + 18 * Y ^ 3 * ξ ^ 7 - 490 * Y ^ 3 *
      ξ ^ 6 + 1869 * Y ^ 3 * ξ ^ 5 - 5296 * Y ^ 3 * ξ ^ 4 + 8020 * Y ^ 3 * ξ ^ 3 - 5508 * Y ^ 3 *
      ξ ^ 2 + 2227 * Y ^ 3 * ξ - 507 * Y ^ 3 - 6 * Y ^ 2 * ξ ^ 7 + 186 * Y ^ 2 * ξ ^ 6 - 342 *
      Y ^ 2 * ξ ^ 5 + 653 * Y ^ 2 * ξ ^ 4 - 867 * Y ^ 2 * ξ ^ 3 + 759 * Y ^ 2 * ξ ^ 2 - 617 *
      Y ^ 2 * ξ + 321 * Y ^ 2 - 24 * Y * ξ ^ 6 - 109 * Y * ξ ^ 5 + 408 * Y * ξ ^ 4 - 594 * Y *
      ξ ^ 3 + 310 * Y * ξ ^ 2 + 63 * Y * ξ - 117 * Y + 37 * ξ ^ 5 - 117 * ξ ^ 4 + 165 * ξ ^ 3 -
      100 * ξ ^ 2 + 6 * ξ + 18) / (72 * Y * ξ ^ 2 * (Y - 1) ^ 6))

/-- The coefficient of `log Y` in `xiF` at `ξ → 1⁻`. -/
noncomputable def xiW1Y (Y ξ : ℝ) : ℝ :=
  ((-2 * Y ^ 5 * ξ ^ 4 + 4 * Y ^ 5 * ξ ^ 3 + 7 * Y ^ 4 * ξ ^ 4 - 12 * Y ^ 4 * ξ ^ 3 + 4 * Y ^ 4 *
      ξ - 8 * Y ^ 3 * ξ ^ 4 + 4 * Y ^ 3 * ξ ^ 3 - 32 * Y ^ 3 * ξ + 3 * Y ^ 3 + 3 * Y ^ 2 * ξ ^ 4 -
      5 * Y ^ 2 * ξ ^ 3 + 45 * Y ^ 2 * ξ - 3 * Y ^ 2 + 3 * Y * ξ ^ 3 - 11 * Y * ξ) / (12 * ξ ^ 2 *
      (Y - 1) ^ 4))

/-- The coefficient of `log (1 - Y)` in `xiF` at `ξ → 1⁻`. -/
noncomputable def xiW1 (Y ξ : ℝ) : ℝ :=
  ((8 * Y ^ 6 * ξ ^ 4 - 16 * Y ^ 6 * ξ ^ 3 + 52 * Y ^ 6 * ξ ^ 2 - 16 * Y ^ 5 * ξ ^ 4 + 24 * Y ^ 5 *
      ξ ^ 3 - 154 * Y ^ 5 * ξ ^ 2 - 16 * Y ^ 5 * ξ + 6 * Y ^ 4 * ξ ^ 4 + 24 * Y ^ 4 * ξ ^ 3 + 123 *
      Y ^ 4 * ξ ^ 2 + 104 * Y ^ 4 * ξ - 12 * Y ^ 4 + 4 * Y ^ 3 * ξ ^ 4 - 64 * Y ^ 3 * ξ ^ 3 - 68 *
      Y ^ 3 * ξ ^ 2 - 188 * Y ^ 3 * ξ + 42 * Y ^ 3 - 2 * Y ^ 2 * ξ ^ 4 + 40 * Y ^ 2 * ξ ^ 3 + 44 *
      Y ^ 2 * ξ ^ 2 + 126 * Y ^ 2 * ξ - 54 * Y ^ 2 - 8 * Y * ξ ^ 3 - 30 * Y * ξ ^ 2 - 24 * Y * ξ +
      30 * Y + 9 * ξ ^ 2 - 2 * ξ - 6) / (24 * Y ^ 2 * ξ ^ 2 * (Y - 1) ^ 2 * (2 * Y - 1)))

/-- The coefficient of `lr3 (1 - ξ)/(1 - ξ)³` in `xiF` at `ξ → 1⁻`. -/
noncomputable def xiX1 (Y ξ : ℝ) : ℝ :=
  ((4 * Y ^ 3 * ξ ^ 5 - 20 * Y ^ 3 * ξ ^ 4 + 64 * Y ^ 3 * ξ ^ 3 - 80 * Y ^ 3 * ξ ^ 2 + 32 * Y ^ 3 *
      ξ + 2 * Y ^ 2 * ξ ^ 5 - 14 * Y ^ 2 * ξ ^ 4 + 19 * Y ^ 2 * ξ ^ 3 - 19 * Y ^ 2 * ξ ^ 2 + 8 *
      Y ^ 2 * ξ + 8 * Y * ξ ^ 4 - 26 * Y * ξ ^ 3 + 46 * Y * ξ ^ 2 - 20 * Y * ξ - 9 * ξ ^ 3 + 15 *
      ξ ^ 2 - 10 * ξ) / (24 * Y ^ 2))

/-- The coefficient of `lr3 (-Y (1 - ξ)/(1 - Y))/(1 - ξ)³` in `xiF` at `ξ → 1⁻`. -/
noncomputable def xiA1 (Y ξ : ℝ) : ℝ :=
  ((4 * Y ^ 7 * ξ ^ 7 - 20 * Y ^ 7 * ξ ^ 6 + 64 * Y ^ 7 * ξ ^ 5 - 80 * Y ^ 7 * ξ ^ 4 + 32 * Y ^ 7 *
      ξ ^ 3 - 14 * Y ^ 6 * ξ ^ 7 + 66 * Y ^ 6 * ξ ^ 6 - 181 * Y ^ 6 * ξ ^ 5 + 133 * Y ^ 6 * ξ ^ 4 +
      48 * Y ^ 6 * ξ ^ 3 - 56 * Y ^ 6 * ξ ^ 2 + 16 * Y ^ 5 * ξ ^ 7 - 56 * Y ^ 5 * ξ ^ 6 + 34 *
      Y ^ 5 * ξ ^ 5 + 386 * Y ^ 5 * ξ ^ 4 - 604 * Y ^ 5 * ξ ^ 3 + 248 * Y ^ 5 * ξ ^ 2 - 6 * Y ^ 4 *
      ξ ^ 7 + 28 * Y ^ 4 * ξ ^ 6 + 124 * Y ^ 4 * ξ ^ 5 - 756 * Y ^ 4 * ξ ^ 4 + 709 * Y ^ 4 * ξ ^ 3 -
      27 * Y ^ 4 * ξ ^ 2 - 156 * Y ^ 4 * ξ + 24 * Y ^ 4 - 6 * Y ^ 3 * ξ ^ 6 - 88 * Y ^ 3 * ξ ^ 5 +
      386 * Y ^ 3 * ξ ^ 4 + 34 * Y ^ 3 * ξ ^ 3 - 560 * Y ^ 3 * ξ ^ 2 + 374 * Y ^ 3 * ξ - 60 *
      Y ^ 3 - 3 * Y ^ 2 * ξ ^ 5 - 29 * Y ^ 2 * ξ ^ 4 - 282 * Y ^ 2 * ξ ^ 3 + 498 * Y ^ 2 * ξ ^ 2 -
      304 * Y ^ 2 * ξ + 60 * Y ^ 2 + 14 * Y * ξ ^ 5 - 2 * Y * ξ ^ 4 + 70 * Y * ξ ^ 3 - 142 * Y *
      ξ ^ 2 + 114 * Y * ξ - 30 * Y - 14 * ξ ^ 4 + 17 * ξ ^ 3 + 3 * ξ ^ 2 - 16 * ξ + 6) / (24 *
      Y ^ 2 * ξ ^ 2 * (Y - 1) ^ 4))

/-- The coefficient of `lr3 ((1 - 2Y)(1 - ξ)/(1 - Y))/(1 - ξ)³` in `xiF` at `ξ → 1⁻`. -/
noncomputable def xiB1 (Y ξ : ℝ) : ℝ :=
  ((-16 * Y ^ 8 * ξ ^ 7 + 80 * Y ^ 8 * ξ ^ 6 - 252 * Y ^ 8 * ξ ^ 5 + 372 * Y ^ 8 * ξ ^ 4 - 236 *
      Y ^ 8 * ξ ^ 3 + 52 * Y ^ 8 * ξ ^ 2 + 64 * Y ^ 7 * ξ ^ 7 - 304 * Y ^ 7 * ξ ^ 6 + 948 * Y ^ 7 *
      ξ ^ 5 - 1304 * Y ^ 7 * ξ ^ 4 + 718 * Y ^ 7 * ξ ^ 3 - 98 * Y ^ 7 * ξ ^ 2 - 16 * Y ^ 7 * ξ -
      92 * Y ^ 6 * ξ ^ 7 + 356 * Y ^ 6 * ξ ^ 6 - 990 * Y ^ 6 * ξ ^ 5 + 840 * Y ^ 6 * ξ ^ 4 + 187 *
      Y ^ 6 * ξ ^ 3 - 513 * Y ^ 6 * ξ ^ 2 + 172 * Y ^ 6 * ξ - 12 * Y ^ 6 + 52 * Y ^ 5 * ξ ^ 7 - 96 *
      Y ^ 5 * ξ ^ 6 + 62 * Y ^ 5 * ξ ^ 5 + 1146 * Y ^ 5 * ξ ^ 4 - 2008 * Y ^ 5 * ξ ^ 3 + 1268 *
      Y ^ 5 * ξ ^ 2 - 298 * Y ^ 5 * ξ + 18 * Y ^ 5 - 2 * Y ^ 4 * ξ ^ 7 - 164 * Y ^ 4 * ξ ^ 6 + 585 *
      Y ^ 4 * ξ ^ 5 - 1805 * Y ^ 4 * ξ ^ 4 + 1892 * Y ^ 4 * ξ ^ 3 - 872 * Y ^ 4 * ξ ^ 2 + 152 *
      Y ^ 4 * ξ - 6 * Y ^ 4 - 8 * Y ^ 3 * ξ ^ 7 + 170 * Y ^ 3 * ξ ^ 6 - 376 * Y ^ 3 * ξ ^ 5 + 814 *
      Y ^ 3 * ξ ^ 4 - 568 * Y ^ 3 * ξ ^ 3 + 190 * Y ^ 3 * ξ ^ 2 - 22 * Y ^ 3 * ξ + 2 * Y ^ 2 *
      ξ ^ 7 - 62 * Y ^ 2 * ξ ^ 6 + 30 * Y ^ 2 * ξ ^ 5 - 28 * Y ^ 2 * ξ ^ 4 - 69 * Y ^ 2 * ξ ^ 3 +
      19 * Y ^ 2 * ξ ^ 2 + 8 * Y * ξ ^ 6 + 38 * Y * ξ ^ 5 - 74 * Y * ξ ^ 4 + 70 * Y * ξ ^ 3 - 10 *
      Y * ξ ^ 2 - 9 * ξ ^ 5 + 15 * ξ ^ 4 - 10 * ξ ^ 3) / (24 * Y ^ 2 * ξ ^ 2 * (Y - 1) ^ 4 * (2 *
      Y - 1)))

/-! ### The identities, one logarithm at a time -/

section Identities

variable {Y ξ : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2) (hξ : ξ ∈ Ioo (0 : ℝ) 1)
include hY hY2 hξ

/-- The nonvanishing facts used by `field_simp`, in several normal forms. -/
theorem xi_ne_zero_facts :
    Y ≠ 0 ∧ Y - 1 ≠ 0 ∧ 1 - Y ≠ 0 ∧ 2 * Y - 1 ≠ 0 ∧ Y * 2 - 1 ≠ 0 ∧ 1 - 2 * Y ≠ 0 ∧
      1 - Y * 2 ≠ 0 ∧ ξ ≠ 0 ∧ ξ - 1 ≠ 0 ∧ 1 - ξ ≠ 0 := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  refine ⟨hY0.ne', ?_, ?_, ?_, ?_, ?_, ?_, hξ0.ne', ?_, ?_⟩ <;>
    (intro h; apply hY2; linarith)

theorem xiR0_zero_form :
    xiR0 Y ξ = xiU0 Y ξ + xiA0 Y ξ * (Y * ξ + (Y * ξ) ^ 2 / 2) / ξ ^ 2 +
      xiB0 Y ξ * ((2 * Y - 1) / Y * ξ + ((2 * Y - 1) / Y * ξ) ^ 2 / 2) / ξ ^ 2 := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', hx0, hx1, hx1'⟩ := xi_ne_zero_facts hY hY2 hξ
  rw [xiR0_eq h0 h1 hx0 hx1]
  unfold xiU0 xiA0 xiB0
  field_simp
  ring

theorem xiPx_zero_form : xiPx Y ξ = xiV0 Y ξ * ξ := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', hx0, hx1, hx1'⟩ := xi_ne_zero_facts hY hY2 hξ
  rw [xiPx_eq h0 hx1]
  unfold xiV0
  field_simp

theorem xiPA_zero_form : xiPA Y ξ = xiA0 Y ξ / ξ ^ 2 := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', hx0, hx1, hx1'⟩ := xi_ne_zero_facts hY hY2 hξ
  rw [xiPA_eq h0 h1 hx0 hx1]
  unfold xiA0
  field_simp

theorem xiPB_zero_form : xiPB Y ξ = xiB0 Y ξ / ξ ^ 2 := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', hx0, hx1, hx1'⟩ := xi_ne_zero_facts hY hY2 hξ
  rw [xiPB_eq h0 h1 h2 hx0 hx1]
  unfold xiB0
  field_simp

theorem xiPBY_zero_form : xiPB Y ξ + xiPY Y ξ = xiW0 Y ξ := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', hx0, hx1, hx1'⟩ := xi_ne_zero_facts hY hY2 hξ
  rw [xiPB_eq h0 h1 h2 hx0 hx1, xiPY_eq h1 hx0]
  unfold xiW0
  field_simp
  ring

theorem xiR0_one_form :
    xiR0 Y ξ = xiU1 Y ξ + xiX1 Y ξ * ((1 - ξ) + (1 - ξ) ^ 2 / 2 + (1 - ξ) ^ 3 / 3) / (1 - ξ) ^ 3 +
      xiA1 Y ξ * (-(Y / (1 - Y)) * (1 - ξ) + (-(Y / (1 - Y)) * (1 - ξ)) ^ 2 / 2 +
        (-(Y / (1 - Y)) * (1 - ξ)) ^ 3 / 3) / (1 - ξ) ^ 3 +
      xiB1 Y ξ * ((1 - 2 * Y) / (1 - Y) * (1 - ξ) + ((1 - 2 * Y) / (1 - Y) * (1 - ξ)) ^ 2 / 2 +
        ((1 - 2 * Y) / (1 - Y) * (1 - ξ)) ^ 3 / 3) / (1 - ξ) ^ 3 := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', hx0, hx1, hx1'⟩ := xi_ne_zero_facts hY hY2 hξ
  rw [xiR0_eq h0 h1 hx0 hx1]
  unfold xiU1 xiX1 xiA1 xiB1
  field_simp
  ring

theorem xiPx_one_form : xiPx Y ξ = xiX1 Y ξ / (1 - ξ) ^ 3 := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', hx0, hx1, hx1'⟩ := xi_ne_zero_facts hY hY2 hξ
  rw [xiPx_eq h0 hx1]
  unfold xiX1
  field_simp
  ring

theorem xiPA_one_form : xiPA Y ξ = xiA1 Y ξ / (1 - ξ) ^ 3 := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', hx0, hx1, hx1'⟩ := xi_ne_zero_facts hY hY2 hξ
  rw [xiPA_eq h0 h1 hx0 hx1]
  unfold xiA1
  field_simp
  ring

theorem xiPB_one_form : xiPB Y ξ = xiB1 Y ξ / (1 - ξ) ^ 3 := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', hx0, hx1, hx1'⟩ := xi_ne_zero_facts hY hY2 hξ
  rw [xiPB_eq h0 h1 h2 hx0 hx1]
  unfold xiB1
  field_simp
  ring

theorem xiPY_one_form : xiPY Y ξ = xiW1Y Y ξ := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', hx0, hx1, hx1'⟩ := xi_ne_zero_facts hY hY2 hξ
  rw [xiPY_eq h1 hx0]
  unfold xiW1Y
  field_simp

theorem xiPAB_one_form : xiPA Y ξ + xiPB Y ξ = xiW1 Y ξ := by
  obtain ⟨h0, h1, h1', h2, h2', h2'', h2''', hx0, hx1, hx1'⟩ := xi_ne_zero_facts hY hY2 hξ
  rw [xiPA_eq h0 h1 hx0 hx1, xiPB_eq h0 h1 h2 hx0 hx1]
  unfold xiW1
  field_simp
  ring

end Identities

/-! ### The endpoint forms -/

/-- **`xiF` near `ξ = 0`.** -/
theorem xiF_eq_zero_form {Y ξ : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2)
    (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    xiF Y ξ = xiU0 Y ξ + xiW0 Y ξ * log Y + xiV0 Y ξ * (ξ * log ξ) +
      xiA0 Y ξ * (lr2 (Y * ξ) / ξ ^ 2) + xiB0 Y ξ * (lr2 ((2 * Y - 1) / Y * ξ) / ξ ^ 2) +
      xiDil Y ξ := by
  have a := xiR0_zero_form hY hY2 hξ
  have b := xiPx_zero_form hY hY2 hξ
  have c := xiPA_zero_form hY hY2 hξ
  have d := xiPB_zero_form hY hY2 hξ
  have e := xiPBY_zero_form hY hY2 hξ
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hB : 0 < ξ + Y - 2 * Y * ξ := by nlinarith
  have e1 : 1 - (2 * Y - 1) / Y * ξ = (ξ + Y - 2 * Y * ξ) / Y := by
    field_simp
    ring
  have eB : log (ξ + Y - 2 * Y * ξ) = log Y + log (1 - (2 * Y - 1) / Y * ξ) := by
    rw [e1, log_div hB.ne' hY0.ne']
    ring
  unfold xiF xiDil lr2
  rw [eB]
  linear_combination a + log ξ * b + log (1 - Y * ξ) * c + log (1 - (2 * Y - 1) / Y * ξ) * d +
    log Y * e

/-- **`xiF` near `ξ = 1`.** -/
theorem xiF_eq_one_form {Y ξ : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2)
    (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    xiF Y ξ = xiU1 Y ξ + xiW1Y Y ξ * log Y + xiW1 Y ξ * log (1 - Y) +
      xiX1 Y ξ * (lr3 (1 - ξ) / (1 - ξ) ^ 3) +
      xiA1 Y ξ * (lr3 (-(Y / (1 - Y)) * (1 - ξ)) / (1 - ξ) ^ 3) +
      xiB1 Y ξ * (lr3 ((1 - 2 * Y) / (1 - Y) * (1 - ξ)) / (1 - ξ) ^ 3) + xiDil Y ξ := by
  have a := xiR0_one_form hY hY2 hξ
  have b := xiPx_one_form hY hY2 hξ
  have c := xiPA_one_form hY hY2 hξ
  have d := xiPB_one_form hY hY2 hξ
  have e := xiPY_one_form hY hY2 hξ
  have f := xiPAB_one_form hY hY2 hξ
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hY1' : 0 < 1 - Y := by linarith
  have hA : 0 < 1 - Y * ξ := by nlinarith
  have hB : 0 < ξ + Y - 2 * Y * ξ := by nlinarith
  have e1 : 1 - -(Y / (1 - Y)) * (1 - ξ) = (1 - Y * ξ) / (1 - Y) := by
    field_simp
    ring
  have e2 : 1 - (1 - 2 * Y) / (1 - Y) * (1 - ξ) = (ξ + Y - 2 * Y * ξ) / (1 - Y) := by
    field_simp
    ring
  have eA : log (1 - Y * ξ) = log (1 - Y) + log (1 - -(Y / (1 - Y)) * (1 - ξ)) := by
    rw [e1, log_div hA.ne' hY1'.ne']
    ring
  have eB : log (ξ + Y - 2 * Y * ξ) =
      log (1 - Y) + log (1 - (1 - 2 * Y) / (1 - Y) * (1 - ξ)) := by
    rw [e2, log_div hB.ne' hY1'.ne']
    ring
  unfold xiF xiDil lr3
  rw [eA, eB, sub_sub_cancel]
  linear_combination a + log ξ * b + log (1 - -(Y / (1 - Y)) * (1 - ξ)) * c +
    log (1 - (1 - 2 * Y) / (1 - Y) * (1 - ξ)) * d + log Y * e + log (1 - Y) * f

end QED.TwoLoop.UnitXXi

end
