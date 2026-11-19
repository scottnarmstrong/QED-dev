/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace QED.VPChain

/-- (C₅) **The sixth-order coefficient of set (b)** (obligation O3-1; decisions D-49.1, D-49.3;
plan sections 2 and 9): the contribution `A₁⁽⁶⁾(b)` to the coefficient of `(α/π)³`, `α = e²/(4π)`
(so `(α/π)³ = e⁶/(64π⁶)`), in `F₂(0)` from the one-loop vertex whose photon carries two
second-order electron vacuum-polarization bubbles in a chain (AKN Fig. 3 (b), p. 9: one diagram),
renormalized on shell:
`A₁⁽⁶⁾(b) = (8/3) ζ(3) - (4/135) π² - 943/324`, with `ζ(3) = ∑_{n ≥ 1} n⁻³`;
numerically `0.002 558 524 936 517 345 …`. **Source status:** no pinned source states this value
(AKN and AHKN give only the diagram count and the sixth-order total; Passera gives the total).
The closed form is the exact value of the chain integral
`∫₀¹ (1 - x) Π̂(x²/(1 - x))² dx` with `Π̂(s) = 2 ∫₀¹ t(1 - t) ln(1 + t(1 - t)s) dt` (theorem (C₇),
proved at helper level as `QED.Chain.integral_setB`); it was first identified by integer-relation
detection on a 50-digit evaluation (`scripts/numerics/phase5_chains.py`). The representation is
the standard vacuum-polarization-insertion formula (Lautrup–Peterman–de Rafael 1972, to pin;
reproduced from Srednicki (62.25)). The same chain formula agrees with pinned values at other
numbers of bubbles, which validates it: with one bubble it gives `119/36 - π²/3` (proved, helper
`QED.Chain.integral_oneBubble`), the vacuum-polarization part of `A₁⁽⁴⁾` (BMR-II (1.10)); with
three bubbles it gives `0.000 876 865 858 9 …` (numerics, plan section 9), the eighth-order I(a)
value `0.000 876 865 ⋯` of AHKN Table 1, p. 6. The closed form is to be pinned in the analytic
literature (Mignaco–Remiddi 1969 or Barbieri–Remiddi 1974, Passera ref. [16]; pending). -/
noncomputable def a1SixSetB : ℝ :=
  8 / 3 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3 - 4 / 135 * Real.pi ^ 2 - 943 / 324

end QED.VPChain

end
