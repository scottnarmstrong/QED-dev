/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCornerSplit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The corner unit C at `λ = 0`: the data of the `x`-integration

Section 6.6.1 of `docs/TWO-LOOP-UNITS.md`, in the variables `y₃ = Y ξ`, `y₄ = Y (1 - ξ)`. This file
states, as rational functions of `(Y, ξ, x)`:

* the letter coefficients of `G_C = cornerGm 0 0`: `cKx` (`K/x`, `K` the coefficient of
  `log(1 + M/(β h))`, a polynomial in `x`), `cR1` and `cR2` (the rational parts on the branches
  `x < x*` and `x > x*`);
* the coefficients of the antiderivatives in `x` (`cA1`, `cQ1x`, `cC1` on `[0, x*]`;
  `cA2`, `cC2a`, `cC2b` on `[x*, 1]`), polynomials `px` in `x`;
* the coefficients `cφ1`, `cφY`, `cφx`, `cφA`, `cφB` of `Φ_C` (eq. (6.7));
* the derivative identities `cQ1x_deriv`, …, `cA2_deriv`, each checked by `field_simp` and `ring`.

The data were generated in exact rational arithmetic by
`scripts/numerics/sc_graph/corner_integration.py`, which also checks every identity used here and
compares `Φ_C` with the engine of `scripts/numerics/two_loop_unit_integrals.py`.
-/

@[expose] public section

open Real

namespace QED.TwoLoop.UnitSCCorner

/-- `K/x`, with `K` the coefficient of `log(1 + M/(β h))` at `λ = 0`. -/
noncomputable def cKx (Y ξ x : ℝ) : ℝ :=
  ((10 * Y ^ 4 * x ^ 3 * ξ ^ 3 - 8 * Y ^ 4 * x ^ 2 * ξ ^ 3 - 16 * Y ^ 4 * x ^ 2 * ξ ^ 2 + 14 *
      Y ^ 4 * x * ξ ^ 2 + 2 * Y ^ 4 * x * ξ - 4 * Y ^ 4 * ξ + 2 * Y ^ 4 - 10 * Y ^ 3 * x ^ 3 *
      ξ ^ 2 + 8 * Y ^ 3 * x ^ 2 * ξ ^ 2 + 8 * Y ^ 3 * x ^ 2 * ξ - 4 * Y ^ 3 * x * ξ ^ 2 - 4 *
      Y ^ 3 * x * ξ + 2 * Y ^ 3 * x + 4 * Y ^ 3 * ξ - 4 * Y ^ 3 - 20 * Y ^ 2 * x ^ 3 * ξ ^ 3 + 5 *
      Y ^ 2 * x ^ 3 * ξ ^ 2 + 16 * Y ^ 2 * x ^ 2 * ξ ^ 3 + 4 * Y ^ 2 * x ^ 2 * ξ ^ 2 + 8 * Y ^ 2 *
      x ^ 2 * ξ - 4 * Y ^ 2 * x * ξ ^ 2 - 4 * Y ^ 2 * x * ξ - 5 * Y ^ 2 * x - 4 * Y ^ 2 * ξ + 4 *
      Y ^ 2 + 10 * Y * x ^ 3 * ξ ^ 3 + 10 * Y * x ^ 3 * ξ ^ 2 - 8 * Y * x ^ 2 * ξ ^ 3 - 8 * Y *
      x ^ 2 * ξ ^ 2 - 8 * Y * x ^ 2 * ξ + 6 * Y * x * ξ - 5 * x ^ 3 * ξ ^ 2 + 4 * x ^ 2 * ξ ^ 2) /
      (4 * Y ^ 4))

/-- The rational part of `G_C` on the branch `x < x*`. -/
noncomputable def cR1 (Y ξ x : ℝ) : ℝ :=
  ((20 * Y ^ 3 * x ^ 3 * ξ ^ 2 - 16 * Y ^ 3 * x ^ 2 * ξ ^ 2 - 16 * Y ^ 3 * x ^ 2 * ξ + 16 * Y ^ 3 *
      x * ξ - 4 * Y ^ 3 + 20 * Y ^ 2 * x ^ 3 * ξ ^ 2 - 20 * Y ^ 2 * x ^ 3 * ξ - 16 * Y ^ 2 * x ^ 2 *
      ξ ^ 2 + 10 * Y ^ 2 * x ^ 2 * ξ - 4 * Y ^ 2 * x + 8 * Y ^ 2 - 20 * Y * x ^ 3 * ξ ^ 2 - 10 * Y *
      x ^ 3 * ξ + 16 * Y * x ^ 2 * ξ ^ 2 + 8 * Y * x ^ 2 * ξ + 11 * Y * x ^ 2 - 8 * Y * x + 10 *
      x ^ 3 * ξ - 8 * x ^ 2 * ξ) / (8 * Y ^ 3))

/-- The numerator of `cR2` over `(1 - ξ x)(1 - (1 - ξ) x)`. -/
noncomputable def cR2N (Y ξ x : ℝ) : ℝ :=
  px
    ((4 * Y ^ 4 * ξ ^ 2 - 4 * Y ^ 4 * ξ + 10 * Y ^ 3 * ξ - 4 * Y ^ 3 - 28 * Y ^ 2 * ξ + 13 * Y ^ 2 +
        14 * Y * ξ - 2 * Y - 3) / (8 * Y ^ 4 * (ξ - 1) ^ 2))
    ((-28 * Y ^ 4 * ξ ^ 2 + 28 * Y ^ 4 * ξ - 8 * Y ^ 3 * ξ ^ 3 + 20 * Y ^ 3 * ξ ^ 2 - 38 * Y ^ 3 *
        ξ + 8 * Y ^ 3 + 24 * Y ^ 2 * ξ ^ 3 - 24 * Y ^ 2 * ξ ^ 2 + 88 * Y ^ 2 * ξ - 43 * Y ^ 2 - 8 *
        Y * ξ ^ 3 - 42 * Y * ξ + 14 * Y + 4 * ξ ^ 2 - 4 * ξ + 9) / (8 * Y ^ 4 * (ξ - 1) ^ 2))
    ((-20 * Y ^ 4 * ξ ^ 4 + 60 * Y ^ 4 * ξ ^ 3 - 40 * Y ^ 4 * ξ + 8 * Y ^ 3 * ξ ^ 4 - 6 * Y ^ 3 *
        ξ ^ 3 - 42 * Y ^ 3 * ξ ^ 2 + 62 * Y ^ 3 * ξ - 4 * Y ^ 3 + 8 * Y ^ 2 * ξ ^ 4 - 68 * Y ^ 2 *
        ξ ^ 3 + 53 * Y ^ 2 * ξ ^ 2 - 83 * Y ^ 2 * ξ + 45 * Y ^ 2 + 14 * Y * ξ ^ 3 + 24 * Y * ξ ^ 2 +
        20 * Y * ξ - 22 * Y - 13 * ξ ^ 2 + 13 * ξ - 9) / (8 * Y ^ 4 * (ξ - 1) ^ 2))
    ((16 * Y ^ 4 * ξ ^ 5 + 8 * Y ^ 4 * ξ ^ 4 - 100 * Y ^ 4 * ξ ^ 3 + 60 * Y ^ 4 * ξ ^ 2 + 16 *
        Y ^ 4 * ξ - 24 * Y ^ 3 * ξ ^ 4 + 48 * Y ^ 3 * ξ ^ 3 + 24 * Y ^ 3 * ξ ^ 2 - 54 * Y ^ 3 * ξ -
        32 * Y ^ 2 * ξ ^ 5 + 48 * Y ^ 2 * ξ ^ 4 + 32 * Y ^ 2 * ξ ^ 3 - 36 * Y ^ 2 * ξ ^ 2 + 18 *
        Y ^ 2 * ξ - 15 * Y ^ 2 + 16 * Y * ξ ^ 5 - 16 * Y * ξ ^ 4 - 16 * Y * ξ ^ 3 - 40 * Y * ξ ^ 2 +
        34 * Y * ξ + 10 * Y - 8 * ξ ^ 4 + 16 * ξ ^ 3 + 6 * ξ ^ 2 - 14 * ξ + 3) / (8 * Y ^ 4 * (ξ -
        1) ^ 2))
    ((-36 * Y ^ 4 * ξ ^ 4 + 16 * Y ^ 4 * ξ ^ 3 + 36 * Y ^ 4 * ξ ^ 2 + 36 * Y ^ 3 * ξ ^ 3 - 38 *
        Y ^ 3 * ξ ^ 2 - 20 * Y ^ 3 * ξ + 72 * Y ^ 2 * ξ ^ 4 - 74 * Y ^ 2 * ξ ^ 3 - 2 * Y ^ 2 *
        ξ ^ 2 - 5 * Y ^ 2 * ξ - 36 * Y * ξ ^ 4 + 30 * Y * ξ ^ 2 + 26 * Y * ξ + 18 * ξ ^ 3 - 18 *
        ξ ^ 2 - 5 * ξ) / (8 * Y ^ 4 * (ξ - 1)))
    ((10 * Y ^ 4 * ξ ^ 3 - 10 * Y ^ 3 * ξ ^ 2 - 20 * Y ^ 2 * ξ ^ 3 + 5 * Y ^ 2 * ξ ^ 2 + 10 * Y *
        ξ ^ 3 + 10 * Y * ξ ^ 2 - 5 * ξ ^ 2) / (4 * Y ^ 4))
    0
    x

/-- The `1`-th term of `cFormR` on the branch `x > x*`, times `(1 - ξ x)(1 - (1 - ξ) x)`. -/
noncomputable def cR2q1 (Y ξ x : ℝ) : ℝ :=
  px
    ((-Y + 2) / (2 * Y))
    ((2 * Y * ξ + 2 * Y - 5) / (2 * Y))
    ((-2 * Y ^ 2 * ξ ^ 2 - 8 * Y ^ 2 * ξ - 2 * Y ^ 2 + 4 * Y * ξ + 8 * Y - 1) / (4 * Y ^ 2))
    ((4 * Y ^ 2 * ξ ^ 2 + 4 * Y ^ 2 * ξ - 6 * Y * ξ - 2 * Y + 1) / (4 * Y ^ 2))
    ((-ξ * (Y * ξ - 1)) / (2 * Y))
    0
    0
    x

/-- The `2`-th term of `cFormR` on the branch `x > x*`, times `(1 - ξ x)(1 - (1 - ξ) x)`. -/
noncomputable def cR2q2 (Y ξ x : ℝ) : ℝ :=
  px
    0
    ((ξ * (Y - 2) * (Y - 1)) / (2 * Y ^ 2))
    ((-ξ * (Y - 1) * (2 * Y ^ 2 * ξ + 2 * Y ^ 2 + 2 * Y * ξ - 5 * Y - 1)) / (2 * Y ^ 3))
    ((ξ * (Y - 1) * (Y ^ 2 * ξ ^ 2 + 4 * Y ^ 2 * ξ + Y ^ 2 + Y * ξ - 4 * Y - 1)) / (2 * Y ^ 3))
    ((-ξ * (Y - 1) * (2 * Y * ξ ^ 2 + 2 * Y * ξ - 2 * ξ - 1)) / (2 * Y ^ 2))
    ((ξ ^ 2 * (Y - 1) * (Y * ξ - 1)) / (2 * Y ^ 2))
    0
    x

/-- The `3`-th term of `cFormR` on the branch `x > x*`, times `(1 - ξ x)(1 - (1 - ξ) x)`. -/
noncomputable def cR2q3 (Y ξ x : ℝ) : ℝ :=
  px
    0
    ((-ξ * (Y - 1) ^ 2 * (2 * Y * ξ - 1)) / (2 * Y ^ 4 * (ξ - 1)))
    ((5 * ξ * (Y - 1) ^ 2 * (2 * Y * ξ - 1)) / (4 * Y ^ 4 * (ξ - 1)))
    ((ξ * (Y - 1) ^ 2 * (2 * Y * ξ - 1) * (ξ ^ 2 - ξ - 1)) / (Y ^ 4 * (ξ - 1)))
    ((-ξ * (Y - 1) ^ 2 * (2 * Y * ξ - 1) * (6 * ξ ^ 2 - 6 * ξ - 1)) / (4 * Y ^ 4 * (ξ - 1)))
    ((ξ ^ 2 * (Y - 1) ^ 2 * (2 * Y * ξ - 1)) / (2 * Y ^ 4))
    0
    x

/-- The `4`-th term of `cFormR` on the branch `x > x*`, times `(1 - ξ x)(1 - (1 - ξ) x)`. -/
noncomputable def cR2q4 (Y ξ x : ℝ) : ℝ :=
  px
    (((Y - 1) * (2 * Y ^ 2 * ξ - Y ^ 2 + 2 * Y - 2)) / (2 * Y ^ 3 * (ξ - 1)))
    ((-3 * Y ^ 3 * ξ ^ 2 - 6 * Y ^ 3 * ξ + 2 * Y ^ 3 + 3 * Y ^ 2 * ξ ^ 2 + 5 * Y ^ 2 * ξ - 7 *
        Y ^ 2 + Y * ξ + 13 * Y - 8) / (2 * Y ^ 3 * (ξ - 1)))
    ((-2 * Y ^ 3 * ξ ^ 3 + 13 * Y ^ 3 * ξ ^ 2 + 5 * Y ^ 3 * ξ - Y ^ 3 + 2 * Y ^ 2 * ξ ^ 3 - 15 *
        Y ^ 2 * ξ ^ 2 - 5 * Y ^ 2 * ξ + 5 * Y ^ 2 + 4 * Y * ξ ^ 2 - 2 * Y * ξ - 14 * Y - 2 * ξ ^ 2 +
        2 * ξ + 10) / (2 * Y ^ 3 * (ξ - 1)))
    ((3 * Y ^ 3 * ξ ^ 4 + Y ^ 3 * ξ ^ 3 - 16 * Y ^ 3 * ξ ^ 2 - Y ^ 3 * ξ - 3 * Y ^ 2 * ξ ^ 4 + 18 *
        Y ^ 2 * ξ ^ 2 + 5 * Y ^ 2 * ξ - Y ^ 2 - Y * ξ ^ 3 - 8 * Y * ξ ^ 2 + 2 * Y * ξ + 5 * Y + 6 *
        ξ ^ 2 - 6 * ξ - 4) / (2 * Y ^ 3 * (ξ - 1)))
    ((-7 * Y ^ 3 * ξ ^ 4 + 5 * Y ^ 3 * ξ ^ 3 + 6 * Y ^ 3 * ξ ^ 2 + 7 * Y ^ 2 * ξ ^ 4 - 2 * Y ^ 2 *
        ξ ^ 3 - 10 * Y ^ 2 * ξ ^ 2 - 3 * Y ^ 2 * ξ - 3 * Y * ξ ^ 3 + 8 * Y * ξ ^ 2 - Y * ξ - 4 *
        ξ ^ 2 + 4 * ξ) / (2 * Y ^ 3 * (ξ - 1)))
    ((2 * ξ ^ 2 * (Y - 1) * (Y * ξ - 1)) / Y ^ 2)
    0
    x

/-- The `5`-th term of `cFormR` on the branch `x > x*`, times `(1 - ξ x)(1 - (1 - ξ) x)`. -/
noncomputable def cR2q5 (Y ξ x : ℝ) : ℝ :=
  px
    ((3 * (Y - 1) ^ 2 * (2 * Y * ξ - 1)) / (8 * Y ^ 4 * (ξ - 1) ^ 2))
    ((-9 * (Y - 1) ^ 2 * (2 * Y * ξ - 1)) / (8 * Y ^ 4 * (ξ - 1) ^ 2))
    ((3 * (Y - 1) ^ 2 * (2 * Y * ξ - 1) * (ξ ^ 2 - ξ + 3)) / (8 * Y ^ 4 * (ξ - 1) ^ 2))
    ((-3 * (Y - 1) ^ 2 * (2 * Y * ξ - 1) * (2 * ξ ^ 2 - 2 * ξ + 1)) / (8 * Y ^ 4 * (ξ - 1) ^ 2))
    ((-3 * ξ * (Y - 1) ^ 2 * (2 * Y * ξ - 1) * (2 * ξ ^ 2 - 2 * ξ - 1)) / (8 * Y ^ 4 * (ξ - 1)))
    ((3 * ξ ^ 2 * (Y - 1) ^ 2 * (2 * Y * ξ - 1)) / (4 * Y ^ 4))
    0
    x

/-- The rational part of `G_C` on the branch `x > x*`. -/
noncomputable def cR2 (Y ξ x : ℝ) : ℝ := cR2N Y ξ x / ((1 - ξ * x) * (1 - (1 - ξ) * x))

/-- The rational part of the antiderivative on `x < x*`. -/
noncomputable def cA1 (Y ξ x : ℝ) : ℝ :=
  px
    0
    ((-2 * Y ^ 2 * ξ ^ 2 - 2 * Y ^ 2 * ξ + 8 * Y * ξ ^ 2 + 8 * Y * ξ - 2 * Y - 6 * ξ ^ 2 - 3 * ξ) /
        (12 * Y * ξ ^ 2 * (Y - 1)))
    ((16 * Y ^ 2 * ξ ^ 2 + Y ^ 2 * ξ + 2 * Y * ξ ^ 2 - 4 * Y * ξ - 2 * Y - 9 * ξ) / (24 * Y ^ 2 *
        ξ))
    ((-4 * Y ^ 3 * ξ ^ 2 - 4 * Y ^ 3 * ξ - 4 * Y ^ 2 * ξ ^ 2 + 2 * Y ^ 2 * ξ + 4 * Y * ξ ^ 2 + 2 *
        Y * ξ + 3 * Y - 2 * ξ) / (8 * Y ^ 3))
    ((ξ * (2 * Y ^ 3 * ξ + 2 * Y ^ 2 * ξ - 2 * Y ^ 2 - 2 * Y * ξ - Y + 1)) / (4 * Y ^ 3))
    0
    0
    x

/-- The `x`-derivative of `cA1`. -/
noncomputable def cA1D (Y ξ x : ℝ) : ℝ :=
  pxD
    ((-2 * Y ^ 2 * ξ ^ 2 - 2 * Y ^ 2 * ξ + 8 * Y * ξ ^ 2 + 8 * Y * ξ - 2 * Y - 6 * ξ ^ 2 - 3 * ξ) /
        (12 * Y * ξ ^ 2 * (Y - 1)))
    ((16 * Y ^ 2 * ξ ^ 2 + Y ^ 2 * ξ + 2 * Y * ξ ^ 2 - 4 * Y * ξ - 2 * Y - 9 * ξ) / (24 * Y ^ 2 *
        ξ))
    ((-4 * Y ^ 3 * ξ ^ 2 - 4 * Y ^ 3 * ξ - 4 * Y ^ 2 * ξ ^ 2 + 2 * Y ^ 2 * ξ + 4 * Y * ξ ^ 2 + 2 *
        Y * ξ + 3 * Y - 2 * ξ) / (8 * Y ^ 3))
    ((ξ * (2 * Y ^ 3 * ξ + 2 * Y ^ 2 * ξ - 2 * Y ^ 2 - 2 * Y * ξ - Y + 1)) / (4 * Y ^ 3))
    0
    0
    x

theorem hasDerivAt_cA1 (Y ξ x : ℝ) : HasDerivAt (cA1 Y ξ) (cA1D Y ξ x) x :=
  hasDerivAt_px _ _ _ _ _ _ _ x

/-- The coefficient of `x log x` (and, times `x`, of `log ξ + log(1 - Y)`) in the antiderivative. -/
noncomputable def cQ1x (Y ξ x : ℝ) : ℝ :=
  px
    0
    ((2 * Y ^ 2 * ξ - Y ^ 2 - 2 * Y * ξ + 2 * Y + 2 * ξ - 2) / (4 * Y ^ 2))
    ((-14 * Y ^ 3 * ξ ^ 2 - 2 * Y ^ 3 * ξ + 4 * Y ^ 2 * ξ ^ 2 + 4 * Y ^ 2 * ξ - 2 * Y ^ 2 + 4 * Y *
        ξ ^ 2 + 4 * Y * ξ + 5 * Y - 6 * ξ) / (12 * Y ^ 3))
    ((2 * Y ^ 4 * ξ ^ 3 + 4 * Y ^ 4 * ξ ^ 2 - 2 * Y ^ 3 * ξ ^ 2 - 2 * Y ^ 3 * ξ - 4 * Y ^ 2 *
        ξ ^ 3 - Y ^ 2 * ξ ^ 2 - 2 * Y ^ 2 * ξ + 2 * Y * ξ ^ 3 + 2 * Y * ξ ^ 2 + 2 * Y * ξ - ξ ^ 2) /
        (4 * Y ^ 4))
    ((-2 * Y ^ 4 * ξ ^ 3 + 2 * Y ^ 3 * ξ ^ 2 + 4 * Y ^ 2 * ξ ^ 3 - Y ^ 2 * ξ ^ 2 - 2 * Y * ξ ^ 3 -
        2 * Y * ξ ^ 2 + ξ ^ 2) / (4 * Y ^ 4))
    0
    0
    x

/-- The `x`-derivative of `cQ1x`. -/
noncomputable def cQ1xD (Y ξ x : ℝ) : ℝ :=
  pxD
    ((2 * Y ^ 2 * ξ - Y ^ 2 - 2 * Y * ξ + 2 * Y + 2 * ξ - 2) / (4 * Y ^ 2))
    ((-14 * Y ^ 3 * ξ ^ 2 - 2 * Y ^ 3 * ξ + 4 * Y ^ 2 * ξ ^ 2 + 4 * Y ^ 2 * ξ - 2 * Y ^ 2 + 4 * Y *
        ξ ^ 2 + 4 * Y * ξ + 5 * Y - 6 * ξ) / (12 * Y ^ 3))
    ((2 * Y ^ 4 * ξ ^ 3 + 4 * Y ^ 4 * ξ ^ 2 - 2 * Y ^ 3 * ξ ^ 2 - 2 * Y ^ 3 * ξ - 4 * Y ^ 2 *
        ξ ^ 3 - Y ^ 2 * ξ ^ 2 - 2 * Y ^ 2 * ξ + 2 * Y * ξ ^ 3 + 2 * Y * ξ ^ 2 + 2 * Y * ξ - ξ ^ 2) /
        (4 * Y ^ 4))
    ((-2 * Y ^ 4 * ξ ^ 3 + 2 * Y ^ 3 * ξ ^ 2 + 4 * Y ^ 2 * ξ ^ 3 - Y ^ 2 * ξ ^ 2 - 2 * Y * ξ ^ 3 -
        2 * Y * ξ ^ 2 + ξ ^ 2) / (4 * Y ^ 4))
    0
    0
    x

theorem hasDerivAt_cQ1x (Y ξ x : ℝ) : HasDerivAt (cQ1x Y ξ) (cQ1xD Y ξ x) x :=
  hasDerivAt_px _ _ _ _ _ _ _ x

/-- The coefficient of `log(Y + ξ(1 - Y) x)` in the antiderivative on `x < x*`. -/
noncomputable def cC1 (Y ξ x : ℝ) : ℝ :=
  px
    ((4 * Y ^ 2 * ξ ^ 2 - 2 * Y ^ 2 * ξ - 10 * Y * ξ ^ 2 + 8 * Y * ξ - 2 * Y + 6 * ξ ^ 2 - 3 * ξ) /
        (12 * ξ ^ 3 * (Y - 1) ^ 2))
    ((-1) / 2)
    ((-(ξ - 1) * (Y ^ 2 - Y + 1)) / (2 * Y ^ 2))
    ((14 * Y ^ 3 * ξ ^ 2 + 2 * Y ^ 3 * ξ - 4 * Y ^ 2 * ξ ^ 2 - 4 * Y ^ 2 * ξ + 2 * Y ^ 2 - 4 * Y *
        ξ ^ 2 - 4 * Y * ξ - 5 * Y + 6 * ξ) / (12 * Y ^ 3))
    ((-2 * Y ^ 4 * ξ ^ 3 - 4 * Y ^ 4 * ξ ^ 2 + 2 * Y ^ 3 * ξ ^ 2 + 2 * Y ^ 3 * ξ + 4 * Y ^ 2 *
        ξ ^ 3 + Y ^ 2 * ξ ^ 2 + 2 * Y ^ 2 * ξ - 2 * Y * ξ ^ 3 - 2 * Y * ξ ^ 2 - 2 * Y * ξ + ξ ^ 2) /
        (4 * Y ^ 4))
    ((2 * Y ^ 4 * ξ ^ 3 - 2 * Y ^ 3 * ξ ^ 2 - 4 * Y ^ 2 * ξ ^ 3 + Y ^ 2 * ξ ^ 2 + 2 * Y * ξ ^ 3 +
        2 * Y * ξ ^ 2 - ξ ^ 2) / (4 * Y ^ 4))
    0
    x

/-- The `x`-derivative of `cC1`. -/
noncomputable def cC1D (Y ξ x : ℝ) : ℝ :=
  pxD
    ((-1) / 2)
    ((-(ξ - 1) * (Y ^ 2 - Y + 1)) / (2 * Y ^ 2))
    ((14 * Y ^ 3 * ξ ^ 2 + 2 * Y ^ 3 * ξ - 4 * Y ^ 2 * ξ ^ 2 - 4 * Y ^ 2 * ξ + 2 * Y ^ 2 - 4 * Y *
        ξ ^ 2 - 4 * Y * ξ - 5 * Y + 6 * ξ) / (12 * Y ^ 3))
    ((-2 * Y ^ 4 * ξ ^ 3 - 4 * Y ^ 4 * ξ ^ 2 + 2 * Y ^ 3 * ξ ^ 2 + 2 * Y ^ 3 * ξ + 4 * Y ^ 2 *
        ξ ^ 3 + Y ^ 2 * ξ ^ 2 + 2 * Y ^ 2 * ξ - 2 * Y * ξ ^ 3 - 2 * Y * ξ ^ 2 - 2 * Y * ξ + ξ ^ 2) /
        (4 * Y ^ 4))
    ((2 * Y ^ 4 * ξ ^ 3 - 2 * Y ^ 3 * ξ ^ 2 - 4 * Y ^ 2 * ξ ^ 3 + Y ^ 2 * ξ ^ 2 + 2 * Y * ξ ^ 3 +
        2 * Y * ξ ^ 2 - ξ ^ 2) / (4 * Y ^ 4))
    0
    x

theorem hasDerivAt_cC1 (Y ξ x : ℝ) : HasDerivAt (cC1 Y ξ) (cC1D Y ξ x) x :=
  hasDerivAt_px _ _ _ _ _ _ _ x

/-- The rational part of the antiderivative on `x > x*`. -/
noncomputable def cA2 (Y ξ x : ℝ) : ℝ :=
  px
    0
    ((22 * Y ^ 4 * ξ ^ 5 - 46 * Y ^ 4 * ξ ^ 4 + 34 * Y ^ 4 * ξ ^ 3 - 14 * Y ^ 4 * ξ ^ 2 + 4 *
        Y ^ 4 * ξ - 8 * Y ^ 3 * ξ ^ 5 + 14 * Y ^ 3 * ξ ^ 4 - 46 * Y ^ 3 * ξ ^ 3 + 44 * Y ^ 3 *
        ξ ^ 2 - 20 * Y ^ 3 * ξ + 4 * Y ^ 3 - 8 * Y ^ 2 * ξ ^ 5 - 16 * Y ^ 2 * ξ ^ 4 + 45 * Y ^ 2 *
        ξ ^ 3 + 33 * Y ^ 2 * ξ ^ 2 - 38 * Y ^ 2 * ξ + 8 * Y ^ 2 + 30 * Y * ξ ^ 4 - 24 * Y * ξ ^ 3 -
        42 * Y * ξ ^ 2 + 36 * Y * ξ - 12 * Y - 9 * ξ ^ 3 + 9 * ξ ^ 2) / (24 * Y ^ 4 * ξ ^ 2 * (ξ -
        1) ^ 3))
    ((-12 * Y ^ 4 * ξ ^ 4 - 13 * Y ^ 4 * ξ ^ 3 + 24 * Y ^ 4 * ξ ^ 2 + Y ^ 4 * ξ + 20 * Y ^ 3 *
        ξ ^ 3 - 36 * Y ^ 3 * ξ ^ 2 + 6 * Y ^ 3 * ξ - 2 * Y ^ 3 + 24 * Y ^ 2 * ξ ^ 4 - 10 * Y ^ 2 *
        ξ ^ 3 + 42 * Y ^ 2 * ξ ^ 2 - 19 * Y ^ 2 * ξ - 4 * Y ^ 2 - 12 * Y * ξ ^ 4 - 30 * Y * ξ ^ 2 +
        6 * Y * ξ + 6 * Y + 6 * ξ ^ 3 - 6 * ξ ^ 2 + 9 * ξ) / (24 * Y ^ 4 * ξ * (ξ - 1) ^ 2))
    ((8 * Y ^ 4 * ξ ^ 3 - 4 * Y ^ 4 * ξ ^ 2 - 4 * Y ^ 4 * ξ - 8 * Y ^ 3 * ξ ^ 2 + 10 * Y ^ 3 * ξ -
        16 * Y ^ 2 * ξ ^ 3 + 16 * Y ^ 2 * ξ ^ 2 - 8 * Y ^ 2 * ξ + 3 * Y ^ 2 + 8 * Y * ξ ^ 3 - 2 *
        Y * ξ - 2 * Y - 4 * ξ ^ 2 + 4 * ξ - 1) / (8 * Y ^ 4 * (ξ - 1) ^ 2))
    ((-2 * Y ^ 4 * ξ ^ 2 + 2 * Y ^ 3 * ξ + 4 * Y ^ 2 * ξ ^ 2 - Y ^ 2 * ξ - 2 * Y * ξ ^ 2 - 2 * Y *
        ξ + ξ) / (4 * Y ^ 4 * (ξ - 1)))
    0
    0
    x

/-- The `x`-derivative of `cA2`. -/
noncomputable def cA2D (Y ξ x : ℝ) : ℝ :=
  pxD
    ((22 * Y ^ 4 * ξ ^ 5 - 46 * Y ^ 4 * ξ ^ 4 + 34 * Y ^ 4 * ξ ^ 3 - 14 * Y ^ 4 * ξ ^ 2 + 4 *
        Y ^ 4 * ξ - 8 * Y ^ 3 * ξ ^ 5 + 14 * Y ^ 3 * ξ ^ 4 - 46 * Y ^ 3 * ξ ^ 3 + 44 * Y ^ 3 *
        ξ ^ 2 - 20 * Y ^ 3 * ξ + 4 * Y ^ 3 - 8 * Y ^ 2 * ξ ^ 5 - 16 * Y ^ 2 * ξ ^ 4 + 45 * Y ^ 2 *
        ξ ^ 3 + 33 * Y ^ 2 * ξ ^ 2 - 38 * Y ^ 2 * ξ + 8 * Y ^ 2 + 30 * Y * ξ ^ 4 - 24 * Y * ξ ^ 3 -
        42 * Y * ξ ^ 2 + 36 * Y * ξ - 12 * Y - 9 * ξ ^ 3 + 9 * ξ ^ 2) / (24 * Y ^ 4 * ξ ^ 2 * (ξ -
        1) ^ 3))
    ((-12 * Y ^ 4 * ξ ^ 4 - 13 * Y ^ 4 * ξ ^ 3 + 24 * Y ^ 4 * ξ ^ 2 + Y ^ 4 * ξ + 20 * Y ^ 3 *
        ξ ^ 3 - 36 * Y ^ 3 * ξ ^ 2 + 6 * Y ^ 3 * ξ - 2 * Y ^ 3 + 24 * Y ^ 2 * ξ ^ 4 - 10 * Y ^ 2 *
        ξ ^ 3 + 42 * Y ^ 2 * ξ ^ 2 - 19 * Y ^ 2 * ξ - 4 * Y ^ 2 - 12 * Y * ξ ^ 4 - 30 * Y * ξ ^ 2 +
        6 * Y * ξ + 6 * Y + 6 * ξ ^ 3 - 6 * ξ ^ 2 + 9 * ξ) / (24 * Y ^ 4 * ξ * (ξ - 1) ^ 2))
    ((8 * Y ^ 4 * ξ ^ 3 - 4 * Y ^ 4 * ξ ^ 2 - 4 * Y ^ 4 * ξ - 8 * Y ^ 3 * ξ ^ 2 + 10 * Y ^ 3 * ξ -
        16 * Y ^ 2 * ξ ^ 3 + 16 * Y ^ 2 * ξ ^ 2 - 8 * Y ^ 2 * ξ + 3 * Y ^ 2 + 8 * Y * ξ ^ 3 - 2 *
        Y * ξ - 2 * Y - 4 * ξ ^ 2 + 4 * ξ - 1) / (8 * Y ^ 4 * (ξ - 1) ^ 2))
    ((-2 * Y ^ 4 * ξ ^ 2 + 2 * Y ^ 3 * ξ + 4 * Y ^ 2 * ξ ^ 2 - Y ^ 2 * ξ - 2 * Y * ξ ^ 2 - 2 * Y *
        ξ + ξ) / (4 * Y ^ 4 * (ξ - 1)))
    0
    0
    x

theorem hasDerivAt_cA2 (Y ξ x : ℝ) : HasDerivAt (cA2 Y ξ) (cA2D Y ξ x) x :=
  hasDerivAt_px _ _ _ _ _ _ _ x

/-- The coefficient of `log(1 - ξ x)` in the antiderivative on `x > x*`. -/
noncomputable def cC2a (Y ξ x : ℝ) : ℝ :=
  px
    ((8 * Y ^ 3 * ξ ^ 3 - 8 * Y ^ 3 * ξ ^ 2 + 2 * Y ^ 3 * ξ - 4 * Y ^ 2 * ξ ^ 3 + 10 * Y ^ 2 *
        ξ ^ 2 - 8 * Y ^ 2 * ξ + 2 * Y ^ 2 - 4 * Y * ξ ^ 3 + 16 * Y * ξ ^ 2 - 15 * Y * ξ + 4 * Y -
        6 * ξ ^ 2 + 12 * ξ - 6) / (12 * Y ^ 3 * ξ ^ 3 * (2 * ξ - 1)))
    ((-1) / 2)
    ((-(ξ - 1) * (Y ^ 2 - Y + 1)) / (2 * Y ^ 2))
    ((14 * Y ^ 3 * ξ ^ 2 + 2 * Y ^ 3 * ξ - 4 * Y ^ 2 * ξ ^ 2 - 4 * Y ^ 2 * ξ + 2 * Y ^ 2 - 4 * Y *
        ξ ^ 2 - 4 * Y * ξ - 5 * Y + 6 * ξ) / (12 * Y ^ 3))
    ((-2 * Y ^ 4 * ξ ^ 3 - 4 * Y ^ 4 * ξ ^ 2 + 2 * Y ^ 3 * ξ ^ 2 + 2 * Y ^ 3 * ξ + 4 * Y ^ 2 *
        ξ ^ 3 + Y ^ 2 * ξ ^ 2 + 2 * Y ^ 2 * ξ - 2 * Y * ξ ^ 3 - 2 * Y * ξ ^ 2 - 2 * Y * ξ + ξ ^ 2) /
        (4 * Y ^ 4))
    ((2 * Y ^ 4 * ξ ^ 3 - 2 * Y ^ 3 * ξ ^ 2 - 4 * Y ^ 2 * ξ ^ 3 + Y ^ 2 * ξ ^ 2 + 2 * Y * ξ ^ 3 +
        2 * Y * ξ ^ 2 - ξ ^ 2) / (4 * Y ^ 4))
    0
    x

/-- The `x`-derivative of `cC2a`. -/
noncomputable def cC2aD (Y ξ x : ℝ) : ℝ :=
  pxD
    ((-1) / 2)
    ((-(ξ - 1) * (Y ^ 2 - Y + 1)) / (2 * Y ^ 2))
    ((14 * Y ^ 3 * ξ ^ 2 + 2 * Y ^ 3 * ξ - 4 * Y ^ 2 * ξ ^ 2 - 4 * Y ^ 2 * ξ + 2 * Y ^ 2 - 4 * Y *
        ξ ^ 2 - 4 * Y * ξ - 5 * Y + 6 * ξ) / (12 * Y ^ 3))
    ((-2 * Y ^ 4 * ξ ^ 3 - 4 * Y ^ 4 * ξ ^ 2 + 2 * Y ^ 3 * ξ ^ 2 + 2 * Y ^ 3 * ξ + 4 * Y ^ 2 *
        ξ ^ 3 + Y ^ 2 * ξ ^ 2 + 2 * Y ^ 2 * ξ - 2 * Y * ξ ^ 3 - 2 * Y * ξ ^ 2 - 2 * Y * ξ + ξ ^ 2) /
        (4 * Y ^ 4))
    ((2 * Y ^ 4 * ξ ^ 3 - 2 * Y ^ 3 * ξ ^ 2 - 4 * Y ^ 2 * ξ ^ 3 + Y ^ 2 * ξ ^ 2 + 2 * Y * ξ ^ 3 +
        2 * Y * ξ ^ 2 - ξ ^ 2) / (4 * Y ^ 4))
    0
    x

theorem hasDerivAt_cC2a (Y ξ x : ℝ) : HasDerivAt (cC2a Y ξ) (cC2aD Y ξ x) x :=
  hasDerivAt_px _ _ _ _ _ _ _ x

/-- The coefficient of `log(1 - (1 - ξ) x)` in the antiderivative on `x > x*`. -/
noncomputable def cC2b (Y ξ x : ℝ) : ℝ :=
  px
    ((-8 * Y ^ 3 * ξ ^ 4 + 16 * Y ^ 3 * ξ ^ 3 - 10 * Y ^ 3 * ξ ^ 2 + 2 * Y ^ 3 * ξ + 4 * Y ^ 2 *
        ξ ^ 4 + 34 * Y ^ 2 * ξ ^ 3 - 54 * Y ^ 2 * ξ ^ 2 + 26 * Y ^ 2 * ξ - 4 * Y ^ 2 + 4 * Y *
        ξ ^ 4 - 44 * Y * ξ ^ 3 + 37 * Y * ξ ^ 2 - 10 * Y * ξ + Y + 6 * ξ ^ 3) / (12 * Y ^ 3 * (ξ -
        1) ^ 4 * (2 * ξ - 1)))
    ((-1) / 2)
    ((-(ξ - 1) * (Y ^ 2 - Y + 1)) / (2 * Y ^ 2))
    ((14 * Y ^ 3 * ξ ^ 2 + 2 * Y ^ 3 * ξ - 4 * Y ^ 2 * ξ ^ 2 - 4 * Y ^ 2 * ξ + 2 * Y ^ 2 - 4 * Y *
        ξ ^ 2 - 4 * Y * ξ - 5 * Y + 6 * ξ) / (12 * Y ^ 3))
    ((-2 * Y ^ 4 * ξ ^ 3 - 4 * Y ^ 4 * ξ ^ 2 + 2 * Y ^ 3 * ξ ^ 2 + 2 * Y ^ 3 * ξ + 4 * Y ^ 2 *
        ξ ^ 3 + Y ^ 2 * ξ ^ 2 + 2 * Y ^ 2 * ξ - 2 * Y * ξ ^ 3 - 2 * Y * ξ ^ 2 - 2 * Y * ξ + ξ ^ 2) /
        (4 * Y ^ 4))
    ((2 * Y ^ 4 * ξ ^ 3 - 2 * Y ^ 3 * ξ ^ 2 - 4 * Y ^ 2 * ξ ^ 3 + Y ^ 2 * ξ ^ 2 + 2 * Y * ξ ^ 3 +
        2 * Y * ξ ^ 2 - ξ ^ 2) / (4 * Y ^ 4))
    0
    x

/-- The `x`-derivative of `cC2b`. -/
noncomputable def cC2bD (Y ξ x : ℝ) : ℝ :=
  pxD
    ((-1) / 2)
    ((-(ξ - 1) * (Y ^ 2 - Y + 1)) / (2 * Y ^ 2))
    ((14 * Y ^ 3 * ξ ^ 2 + 2 * Y ^ 3 * ξ - 4 * Y ^ 2 * ξ ^ 2 - 4 * Y ^ 2 * ξ + 2 * Y ^ 2 - 4 * Y *
        ξ ^ 2 - 4 * Y * ξ - 5 * Y + 6 * ξ) / (12 * Y ^ 3))
    ((-2 * Y ^ 4 * ξ ^ 3 - 4 * Y ^ 4 * ξ ^ 2 + 2 * Y ^ 3 * ξ ^ 2 + 2 * Y ^ 3 * ξ + 4 * Y ^ 2 *
        ξ ^ 3 + Y ^ 2 * ξ ^ 2 + 2 * Y ^ 2 * ξ - 2 * Y * ξ ^ 3 - 2 * Y * ξ ^ 2 - 2 * Y * ξ + ξ ^ 2) /
        (4 * Y ^ 4))
    ((2 * Y ^ 4 * ξ ^ 3 - 2 * Y ^ 3 * ξ ^ 2 - 4 * Y ^ 2 * ξ ^ 3 + Y ^ 2 * ξ ^ 2 + 2 * Y * ξ ^ 3 +
        2 * Y * ξ ^ 2 - ξ ^ 2) / (4 * Y ^ 4))
    0
    x

theorem hasDerivAt_cC2b (Y ξ x : ℝ) : HasDerivAt (cC2b Y ξ) (cC2bD Y ξ x) x :=
  hasDerivAt_px _ _ _ _ _ _ _ x

/-- The rational part of `Φ_C(Y, ξ)` (eq. (6.7)). -/
noncomputable def cφ1 (Y ξ : ℝ) : ℝ :=
  ((9 * Y ^ 2 * ξ ^ 4 - 22 * Y ^ 2 * ξ ^ 3 + 21 * Y ^ 2 * ξ ^ 2 - 8 * Y ^ 2 * ξ + 4 * Y * ξ ^ 3 -
      48 * Y * ξ ^ 2 + 40 * Y * ξ - 8 * Y + 24 * ξ ^ 2 - 24 * ξ + 12) / (24 * Y ^ 2 * ξ ^ 2 * (ξ -
      1) ^ 2))

/-- The coefficient of `log Y` of `Φ_C(Y, ξ)` (eq. (6.7)). -/
noncomputable def cφY (Y ξ : ℝ) : ℝ :=
  ((-3 * Y ^ 2 * ξ ^ 3 - 4 * Y ^ 2 * ξ ^ 2 + 2 * Y ^ 2 * ξ + 6 * Y * ξ ^ 3 + 10 * Y * ξ ^ 2 - 8 *
      Y * ξ + 2 * Y - 3 * ξ ^ 3 - 6 * ξ ^ 2 + 3 * ξ) / (12 * ξ ^ 3 * (Y - 1) ^ 2))

/-- The coefficient of `log ξ` of `Φ_C(Y, ξ)` (eq. (6.7)). -/
noncomputable def cφx (Y ξ : ℝ) : ℝ :=
  ((-6 * Y ^ 3 * ξ ^ 5 + 19 * Y ^ 3 * ξ ^ 4 - 32 * Y ^ 3 * ξ ^ 3 + 32 * Y ^ 3 * ξ ^ 2 - 16 * Y ^ 3 *
      ξ + 3 * Y ^ 3 + 4 * Y ^ 2 * ξ ^ 4 + 34 * Y ^ 2 * ξ ^ 3 - 54 * Y ^ 2 * ξ ^ 2 + 26 * Y ^ 2 * ξ -
      4 * Y ^ 2 + 4 * Y * ξ ^ 4 - 44 * Y * ξ ^ 3 + 37 * Y * ξ ^ 2 - 10 * Y * ξ + Y + 6 * ξ ^ 3) /
      (12 * Y ^ 3 * (ξ - 1) ^ 4 * (2 * ξ - 1)))

/-- The coefficient of `log(1 - Y ξ)` of `Φ_C(Y, ξ)` (eq. (6.7)). -/
noncomputable def cφA (Y ξ : ℝ) : ℝ :=
  ((-3 * Y ^ 5 * ξ ^ 7 + 8 * Y ^ 5 * ξ ^ 6 - 12 * Y ^ 5 * ξ ^ 5 + 10 * Y ^ 5 * ξ ^ 4 - 3 * Y ^ 5 *
      ξ ^ 3 + 6 * Y ^ 4 * ξ ^ 7 - 14 * Y ^ 4 * ξ ^ 6 + 42 * Y ^ 4 * ξ ^ 5 - 38 * Y ^ 4 * ξ ^ 4 +
      10 * Y ^ 4 * ξ ^ 3 - 3 * Y ^ 3 * ξ ^ 7 + 6 * Y ^ 3 * ξ ^ 6 - 69 * Y ^ 3 * ξ ^ 5 + 54 * Y ^ 3 *
      ξ ^ 4 - 12 * Y ^ 3 * ξ ^ 3 + 42 * Y ^ 2 * ξ ^ 5 + 42 * Y ^ 2 * ξ ^ 4 - 122 * Y ^ 2 * ξ ^ 3 +
      120 * Y ^ 2 * ξ ^ 2 - 58 * Y ^ 2 * ξ + 12 * Y ^ 2 - 6 * Y * ξ ^ 5 - 72 * Y * ξ ^ 4 + 137 * Y *
      ξ ^ 3 - 138 * Y * ξ ^ 2 + 71 * Y * ξ - 16 * Y + 18 * ξ ^ 4 - 36 * ξ ^ 3 + 42 * ξ ^ 2 - 24 *
      ξ + 6) / (12 * Y ^ 3 * ξ ^ 3 * (Y - 1) ^ 2 * (ξ - 1) ^ 4))

/-- The coefficient of `log(ξ + Y - 2Yξ)` of `Φ_C(Y, ξ)` (eq. (6.7)). -/
noncomputable def cφB (Y ξ : ℝ) : ℝ :=
  ((16 * Y ^ 5 * ξ ^ 7 - 56 * Y ^ 5 * ξ ^ 6 + 92 * Y ^ 5 * ξ ^ 5 - 90 * Y ^ 5 * ξ ^ 4 + 52 * Y ^ 5 *
      ξ ^ 3 - 16 * Y ^ 5 * ξ ^ 2 + 2 * Y ^ 5 * ξ - 40 * Y ^ 4 * ξ ^ 7 + 104 * Y ^ 4 * ξ ^ 6 - 202 *
      Y ^ 4 * ξ ^ 5 + 264 * Y ^ 4 * ξ ^ 4 - 200 * Y ^ 4 * ξ ^ 3 + 86 * Y ^ 4 * ξ ^ 2 - 20 * Y ^ 4 *
      ξ + 2 * Y ^ 4 + 24 * Y ^ 3 * ξ ^ 7 + 36 * Y ^ 3 * ξ ^ 6 - 12 * Y ^ 3 * ξ ^ 5 - 72 * Y ^ 3 *
      ξ ^ 4 + 69 * Y ^ 3 * ξ ^ 3 - 24 * Y ^ 3 * ξ ^ 2 + 3 * Y ^ 3 * ξ + 4 * Y ^ 2 * ξ ^ 7 - 128 *
      Y ^ 2 * ξ ^ 6 + 128 * Y ^ 2 * ξ ^ 5 - 46 * Y ^ 2 * ξ ^ 4 + 6 * Y ^ 2 * ξ ^ 3 - 4 * Y * ξ ^ 7 +
      56 * Y * ξ ^ 6 - 37 * Y * ξ ^ 5 + 10 * Y * ξ ^ 4 - Y * ξ ^ 3 - 6 * ξ ^ 6) / (12 * Y ^ 3 *
      ξ ^ 3 * (Y - 1) ^ 2 * (ξ - 1) ^ 4 * (2 * ξ - 1)))

theorem cQ1x_deriv {Y ξ x : ℝ} (hY0 : Y ≠ 0) :
    cQ1x Y ξ x + x * cQ1xD Y ξ x = -(x * cKx Y ξ x) := by
  unfold cQ1x cQ1xD cKx px pxD
  field_simp
  ring

theorem cC1_deriv {Y ξ x : ℝ} (hY0 : Y ≠ 0) :
    cC1D Y ξ x = x * cKx Y ξ x - (1 - x) / 2 := by
  unfold cC1D cKx pxD
  field_simp
  ring

theorem cC2a_deriv {Y ξ x : ℝ} (hY0 : Y ≠ 0) :
    cC2aD Y ξ x = x * cKx Y ξ x - (1 - x) / 2 := by
  unfold cC2aD cKx pxD
  field_simp
  ring

theorem cC2b_deriv {Y ξ x : ℝ} (hY0 : Y ≠ 0) :
    cC2bD Y ξ x = x * cKx Y ξ x - (1 - x) / 2 := by
  unfold cC2bD cKx pxD
  field_simp
  ring

theorem cA1_deriv {Y ξ x : ℝ} (hY0 : 0 < Y) (hY1 : Y < 1) (hξ0 : 0 < ξ) (hx : 0 < x) :
    cA1D Y ξ x + cQ1x Y ξ x + cC1 Y ξ x * (ξ * (1 - Y) / (Y + ξ * (1 - Y) * x)) = cR1 Y ξ x := by
  have h1Y : 0 < 1 - Y := by linarith
  have hW : Y + ξ * (1 - Y) * x ≠ 0 := by positivity
  have hY1' : Y - 1 ≠ 0 := by linarith
  have := hY0.ne'
  have := hξ0.ne'
  unfold cA1D cQ1x cC1 cR1 px pxD
  field_simp
  ring


end QED.TwoLoop.UnitSCCorner

end
