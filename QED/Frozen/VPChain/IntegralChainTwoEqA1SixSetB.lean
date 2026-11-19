-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.VPChain.A1SixSetB
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import QED.Provider.VPChain.IntegralChainTwoEqA1SixSetB

@[expose] public section

namespace QED.VPChain

/-- (C₇) **`A₁⁽⁶⁾(b)` is the chain integral** (obligation O3-13): with the renormalized one-loop
vacuum polarization of an electron loop in units of `α/π` and of the electron mass,
`Π̂(s) = 2 ∫₀¹ t(1 - t) ln(1 + t(1 - t)s) dt` (Srednicki (62.25) at Euclidean `s = k²/m²`, divided
by `α/π`), the function `x ↦ (1 - x) Π̂(x²/(1 - x))²` is interval integrable on `[0, 1]` and its
integral is (C₅). For one bubble the same integral of `(1 - x) Π̂(x²/(1 - x))` is `119/36 - π²/3`,
the vacuum-polarization part of `A₁⁽⁴⁾` (BMR-II (1.10); helper `QED.Chain.integral_oneBubble`). At
`x = 1` the integrand is `0` by Lean's `x / 0 = 0`, a single point. -/
theorem integral_chainTwo_eq_a1SixSetB :
    IntervalIntegrable (fun x : ℝ => (1 - x) * (2 * ∫ t in (0 : ℝ)..1,
        t * (1 - t) * Real.log (1 + t * (1 - t) * (x ^ 2 / (1 - x)))) ^ 2)
        MeasureTheory.volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - x) * (2 * ∫ t in (0 : ℝ)..1,
        t * (1 - t) * Real.log (1 + t * (1 - t) * (x ^ 2 / (1 - x)))) ^ 2 = a1SixSetB :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.VPChain

end
-- FROZEN_ANCHOR_SUFFIX_END
