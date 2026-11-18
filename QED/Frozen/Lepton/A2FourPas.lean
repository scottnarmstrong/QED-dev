/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace QED.Lepton

/-- (U₃-alt) **Alternative candidate**: Passera (10) with its term structure kept, at `x = 1/y`.
Mathlib's `Real.log` is `log |·|`, which is the real part of the complex logarithm, so the
logarithms are Passera's literally. Only the three dilogarithms whose argument lies outside
`[-1, 1]` (where the series diverges and `tsum` is `0`) are replaced by the inversion formulas
`Re Li₂(z) = π²/3 - ½ ln² z - Li₂(1/z)` (`z = x`, `x²`) and
`Li₂(-z) = -π²/6 - ½ ln² z - Li₂(-1/z)` (`z = x`). -/
noncomputable def a2FourPas (y : ℝ) : ℝ :=
  -25 / 36 - Real.log y⁻¹ / 3 + y⁻¹ ^ 2 * (4 + 3 * Real.log y⁻¹) +
    y⁻¹ / 2 * (1 - 5 * y⁻¹ ^ 2) *
      (Real.pi ^ 2 / 2 - Real.log y⁻¹ * Real.log ((1 - y⁻¹) / (1 + y⁻¹)) -
        (Real.pi ^ 2 / 3 - Real.log y⁻¹ ^ 2 / 2 - ∑' n : ℕ, y ^ (n + 1) / ((n : ℝ) + 1) ^ 2) +
        (-(Real.pi ^ 2 / 6) - Real.log y⁻¹ ^ 2 / 2 -
          ∑' n : ℕ, (-y) ^ (n + 1) / ((n : ℝ) + 1) ^ 2)) +
    y⁻¹ ^ 4 *
      (Real.pi ^ 2 / 3 - 2 * Real.log y⁻¹ * Real.log (y⁻¹⁻¹ - y⁻¹) -
        (Real.pi ^ 2 / 3 - Real.log (y⁻¹ ^ 2) ^ 2 / 2 -
          ∑' n : ℕ, (y ^ 2) ^ (n + 1) / ((n : ℝ) + 1) ^ 2))

end QED.Lepton

end
