/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace QED.TwoLoop

/-- (U₁) **The mass-independent fourth-order coefficient** of the electron's anomalous magnetic
moment (obligation O2-1; decision D-36.2): the coefficient of `(α/π)²` in `F₂(0)` from the
two-loop diagrams with photons and the electron alone, with `α = e²/(4π)` (so
`(α/π)² = e⁴/(16π⁴)`),
`A₁⁽⁴⁾ = 197/144 + π²/12 - (π²/2) ln 2 + (3/4) ζ(3)`, with `ζ(3) = ∑_{n ≥ 1} n⁻³`. This is
Passera (2007) eq. (9) and Barbieri–Mignaco–Remiddi I (1972) eq. (1.7), p. 830 (again p. 853);
numerically `A₁⁽⁴⁾ = -0.328 478 965 579 …`. It is the sum of the vacuum-polarization part
`119/36 - π²/3` and the part without a fermion loop
`-31/16 + 5π²/12 - (π²/2) ln 2 + (3/4) ζ(3)` (BMR-I p. 852; Passera p. 2, after eq. (10)). -/
noncomputable def a1Four : ℝ :=
  197 / 144 + Real.pi ^ 2 / 12 - Real.pi ^ 2 / 2 * Real.log 2 +
    3 / 4 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3

end QED.TwoLoop

end
