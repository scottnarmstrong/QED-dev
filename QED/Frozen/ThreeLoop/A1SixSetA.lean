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

/-- (A₂) **The sixth-order coefficient of set (a)** (decisions D-49.3, D-54.2, D-56; plan
sections 3 (a) and 8.1): the contribution `A₁⁽⁶⁾(a)` to the coefficient of `(α/π)³`,
`α = e²/(4π)` (so `(α/π)³ = e⁶/(64π⁶)`), in `F₂(0)` from the three graphs of the one-loop vertex
whose photon carries the fourth-order (two-loop) electron vacuum polarization, renormalized on
shell (AKN Fig. 3 (a), p. 9). Closed form of Kaptari, Lashkevich, Solovtsova, Phys. Rev. D 112
(2025) 073008, arXiv:2508.05119v1 (source `kaptari-lashkevich-solovtsova-2025`), eq. (16) (the
equal-mass value `A₂,L⁽⁶⁾(1)`, first obtained by Mignaco and Remiddi, Nuovo Cim. A 60 (1969) 519):
`A₁⁽⁶⁾(a) = 673/108 - (41/81) π² - (7/270) π⁴ - (4/9) π² ln 2 - (4/9) π² ln² 2 + (4/9) ln⁴ 2
  + (32/3) a₄ + (13/18) ζ(3)`,
with `ζ(3) = ∑_{n ≥ 1} n⁻³` and `a₄ = Li₄(1/2) = ∑_{n ≥ 1} 2⁻ⁿ n⁻⁴`, written out as series as in
(R₁), so the definition uses no project-defined function; numerically
`0.052 870 652 475 767 000 9 …` (Kaptari et al.: `0.05287065 …`). The same constant is the value
of the one-variable integral `∫₀¹ (1 - x) Π̂⁽⁴⁾(x²/(1 - x)) dx` with the Källén–Sabry function
(Kaptari et al. eqs. (20), (25); proved at helper level as `QED.Chain.integral_setA_eq_aSetA`). -/
noncomputable def a1SixSetA : ℝ :=
  673 / 108 - 41 / 81 * Real.pi ^ 2 - 7 / 270 * Real.pi ^ 4 -
    4 / 9 * Real.pi ^ 2 * Real.log 2 - 4 / 9 * Real.pi ^ 2 * Real.log 2 ^ 2 +
    4 / 9 * Real.log 2 ^ 4 + 32 / 3 * ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) ^ 4 +
    13 / 18 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3

end QED.ThreeLoop

end
