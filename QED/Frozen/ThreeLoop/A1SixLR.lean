/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace QED.ThreeLoop

/-- (R₁) **The Laporta–Remiddi closed form of the sixth-order coefficient** (decision D-54.2):
the coefficient `A₁⁽⁶⁾` of `(α/π)³`, `α = e²/(4π)` (so `(α/π)³ = e⁶/(64π⁶)`), in `F₂(0)` from all
72 three-loop vertex diagrams with photons and the electron alone, as evaluated in closed form by
Laporta and Remiddi (1996), abstract and eq. (5) (source `laporta-remiddi-1996`; the same
expression is Passera (2007) eq. (14)):
`A₁⁽⁶⁾ = (83/72) π² ζ(3) - (215/24) ζ(5) + (100/3) [(a₄ + ln⁴2/24) - π² ln²2/24]
  - (239/2160) π⁴ + (139/18) ζ(3) - (298/9) π² ln 2 + (17101/810) π² + 28259/5184`,
with `ζ(s) = ∑_{n ≥ 1} n⁻ˢ` and `a₄ = Li₄(1/2) = ∑_{n ≥ 1} 2⁻ⁿ n⁻⁴`;
numerically `1.181 241 456 587 200 006 …`. The series are written out, so the definition uses no
project-defined function. That the model's three-loop coefficient equals this constant is the
three-loop headline still to be proved; this declaration only fixes the target. -/
noncomputable def a1SixLR : ℝ :=
  83 / 72 * Real.pi ^ 2 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3 -
    215 / 24 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 5 +
    100 / 3 * ((∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) ^ 4 + Real.log 2 ^ 4 / 24) -
      Real.pi ^ 2 * Real.log 2 ^ 2 / 24) -
    239 / 2160 * Real.pi ^ 4 + 139 / 18 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3 -
    298 / 9 * Real.pi ^ 2 * Real.log 2 + 17101 / 810 * Real.pi ^ 2 + 28259 / 5184

end QED.ThreeLoop

end
