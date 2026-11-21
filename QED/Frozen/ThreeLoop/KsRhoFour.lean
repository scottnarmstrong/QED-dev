/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace QED.ThreeLoop

/-- (A₄) **The Källén–Sabry spectral function of the fourth-order vacuum polarization**
(Kaptari, Lashkevich, Solovtsova, Phys. Rev. D 112 (2025) 073008, arXiv:2508.05119v1, eq. (20)
(source `kaptari-lashkevich-solovtsova-2025`); Källén and Sabry, Dan. Mat. Fys. Medd. 29 (1955)
no. 17): `ρ⁽⁴⁾(δ) = Im Π₄(t) / (π (α/π)²)` at
the pair velocity `δ = √(1 - 4m²/t)` of a timelike `t > 4m²`, for `0 < δ < 1`:
`ρ⁽⁴⁾(δ) = [11/16 + 11δ²/24 - 7δ⁴/48 + (1/2 + δ²/3 - δ⁴/6) ln((1+δ)³/(8δ²))] ln((1+δ)/(1-δ))
  + δ [5/8 - 3δ²/8 - (1/2 - δ²/6) ln(64δ⁴/(1-δ²)³)]
  + 2 (1/2 + δ²/3 - δ⁴/6) [2 Li₂((1-δ)/(1+δ)) + Li₂(-(1-δ)/(1+δ))]`,
with `Li₂(z) = ∑_{n ≥ 1} zⁿ/n²` written out as a series (its arguments lie in `(-1, 1)`), so the
definition uses no project-defined function. Its values outside `(0, 1)` are not used. It tends to
`π²/4` at threshold and to `1/4` at high energy (helper `QED.Chain.ksRho`, which this is
definitionally). -/
noncomputable def ksRhoFour (δ : ℝ) : ℝ :=
  (11 / 16 + 11 / 24 * δ ^ 2 - 7 / 48 * δ ^ 4 +
      (1 / 2 + δ ^ 2 / 3 - δ ^ 4 / 6) * Real.log ((1 + δ) ^ 3 / (8 * δ ^ 2))) *
      Real.log ((1 + δ) / (1 - δ)) +
    δ * (5 / 8 - 3 / 8 * δ ^ 2 -
      (1 / 2 - δ ^ 2 / 6) * Real.log (64 * δ ^ 4 / (1 - δ ^ 2) ^ 3)) +
    2 * (1 / 2 + δ ^ 2 / 3 - δ ^ 4 / 6) *
      (2 * ∑' n : ℕ, ((1 - δ) / (1 + δ)) ^ (n + 1) / ((n : ℝ) + 1) ^ 2 +
        ∑' n : ℕ, (-((1 - δ) / (1 + δ))) ^ (n + 1) / ((n : ℝ) + 1) ^ 2)

end QED.ThreeLoop

end
