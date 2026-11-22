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

/-- (Sd₂) **The sixth-order coefficient of set (d)** (decisions D-49.3, D-54.2; plan section 3
(d)): the contribution `A₁⁽⁶⁾(d)` to the coefficient of `(α/π)³`, `α = e²/(4π)` (so
`(α/π)³ = e⁶/(64π⁶)`), in `F₂(0)` from the six graphs in which the external photon is attached to
an electron loop joined to the open line of the one-loop vertex by three photons (light-by-light
scattering; AKN Fig. 3 (d), p. 9). Closed form of Laporta and Remiddi, Phys. Lett. B 265 (1991)
181 (cited by Laporta–Remiddi 1996 as Ref. [5] among the known parts of eq. (5)), as printed in
Jegerlehner–Nyffeler, Phys. Rept. 477 (2009) 1, arXiv:0902.3360v1 (source
`jegerlehner-nyffeler-2009`), p. 32, the equal-mass display before eq. (82):
`A₁⁽⁶⁾(d) = (5/6) ζ(5) - (5/18) π² ζ(3) - (41/540) π⁴ - (2/3) π² ln² 2 + (2/3) ln⁴ 2 + 16 a₄
  - (4/3) ζ(3) - 24 π² ln 2 + (931/54) π² + 5/9`,
with `ζ(s) = ∑_{n ≥ 1} n⁻ˢ` and `a₄ = Li₄(1/2) = ∑_{n ≥ 1} 2⁻ⁿ n⁻⁴` written out as series, as in
(R₁), so the definition uses no project-defined function; numerically
`0.371 005 292 107 220 840 821 …` (Jegerlehner–Nyffeler eq. (82): `0.371005293`). -/
noncomputable def a1SixSetD : ℝ :=
  5 / 6 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 5 -
    5 / 18 * Real.pi ^ 2 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3 - 41 / 540 * Real.pi ^ 4 -
    2 / 3 * Real.pi ^ 2 * Real.log 2 ^ 2 + 2 / 3 * Real.log 2 ^ 4 +
    16 * ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) ^ 4 -
    4 / 3 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3 - 24 * Real.pi ^ 2 * Real.log 2 +
    931 / 54 * Real.pi ^ 2 + 5 / 9

end QED.ThreeLoop

end
