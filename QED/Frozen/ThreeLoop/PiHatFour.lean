/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.KsRhoFour
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

namespace QED.ThreeLoop

/-- (A₅) **The renormalized fourth-order vacuum-polarization function** `Π̂⁽⁴⁾(s)`, at the
Euclidean (spacelike) `s = k²/m²` in units of the loop mass `m`, as the coefficient of `(α/π)²`:
the once-subtracted dispersion integral of (A₄),
`Π̂⁽⁴⁾(s) = ∫₀¹ 2δ/(1 - δ²) ρ⁽⁴⁾(δ) s/(s + 4/(1 - δ²)) dδ`, with `t = 4/(1 - δ²)` and
`dt/t = 2δ dδ/(1 - δ²)` (Kaptari et al. eqs. (4), (6), (18)). So `Π̂⁽⁴⁾(0) = 0`. With the
one-loop weight `ρ⁽²⁾(δ) = δ(1 - δ²/3)/2` in place of `ρ⁽⁴⁾` the same formula is the one-loop
`Π̂` of (C₅) and (C₇) (helper `QED.Chain.piHat_eq_spectral`). Source-facing for `s > -4`. -/
noncomputable def piHatFour (s : ℝ) : ℝ :=
  ∫ δ in (0 : ℝ)..1, 2 * δ / (1 - δ ^ 2) * ksRhoFour δ * (s / (s + 4 / (1 - δ ^ 2)))

end QED.ThreeLoop

end
