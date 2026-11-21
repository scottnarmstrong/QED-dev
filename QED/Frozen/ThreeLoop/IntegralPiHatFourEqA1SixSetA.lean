-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.PiHatFour
public import QED.Frozen.ThreeLoop.A1SixSetA
public import QED.Provider.ThreeLoop.IntegralPiHatFourEqA1SixSetA

@[expose] public section

namespace QED.ThreeLoop

/-- (A₇) **The set (a) constant is the vacuum-polarization-insertion integral** (the analogue of
(C₇); Kaptari et al. eq. (25) at `r = 1`; Srednicki (62.25)): the one-loop vertex with the
renormalized fourth-order vacuum polarization on its photon has Pauli coefficient
`∫₀¹ (1 - x) Π̂⁽⁴⁾(x²/(1 - x)) dx` in units of `(α/π)³`, and this equals (A₂). Proved at helper
level as `QED.Chain.integral_setA_eq_aSetA`. -/
theorem integral_piHatFour_eq_a1SixSetA :
    ∫ x in (0 : ℝ)..1, (1 - x) * piHatFour (x ^ 2 / (1 - x)) = a1SixSetA :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.ThreeLoop.integral_piHatFour_eq_a1SixSetA
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.ThreeLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
