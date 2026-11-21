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

/-- (Sc₄) **The sixth-order coefficient of set (c)** (decisions D-49.3, D-54.2, D-56; plan
sections 3 (c), 8.1; source `barbieri-remiddi-1974`): the contribution `A₁⁽⁶⁾(c)` to the
coefficient of `(α/π)³`, `α = e²/(4π)` (so `(α/π)³ = e⁶/(64π⁶)`), in `F₂(0)` from the 12
graphs obtained by inserting a second-order electron vacuum-polarization bubble on one photon line
of the six fourth-order vertex graphs without a fermion loop, renormalized on shell (AKN Fig. 3
(c), p. 9). Closed form of Barbieri and Remiddi, CERN preprint TH.1801 (1974), Phys. Lett. B 49
(1974) 468, eq. (3), with `ζ(2) = π²/6`:
`A₁⁽⁶⁾(c) = 227/72 + (31/9) ζ(2) - 8 ζ(2) ln 2 - (35/8) ζ(3) + 2 ζ(2)²`,
with `ζ(3) = ∑_{n ≥ 1} n⁻³` written out as a series; numerically `-0.150 172 282 099 798 375 …`.
The same constant is the value of `∫₀¹ λ⁽⁴⁾(x) Δα(x) dx` with the space-like kernel of
Balzani–Laporta–Passera (2022) (helper `QED.Chain.integral_setC_eq_aSetC`), which is not part of
this statement. -/
noncomputable def a1SixSetC : ℝ :=
  227 / 72 + 31 / 9 * (Real.pi ^ 2 / 6) - 8 * (Real.pi ^ 2 / 6) * Real.log 2 -
    35 / 8 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3 + 2 * (Real.pi ^ 2 / 6) ^ 2

end QED.ThreeLoop

end
