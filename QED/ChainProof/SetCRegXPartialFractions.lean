/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegBubblePF

/-!
# The divided differences of the dressed crossed photon

The two numerator cancellations reduce the multisets of squared masses to
`abc`, `aabc`, `abbc`, and `aabbc`. The divided differences for these multisets
expand into the coefficients of `QED/ChainProof/SetCRegBubblePF.lean`.
-/

@[expose] public section

namespace QED.ChainProof.SetCRegX

open QED.ChainProof.SetCRegBubble

/-- The split with two distinct squared masses, oriented as the difference of
the first and second resolvents over the second mass minus the first. -/
noncomputable def massDividedDifference (a b fa fb : ℝ) : ℝ := (fa - fb) / (b - a)

/-- The four contributions after the numerator cancellations. The inputs
`da` and `db` are the mass derivatives for the repeated nodes. -/
noncomputable def bubbleDividedDifference (a b c fa fb fc da db : ℝ) : ℝ :=
  let ac := massDividedDifference a c fa fc
  let bc := massDividedDifference b c fb fc
  let aac := massDividedDifference a c (-da) ac
  let bbc := massDividedDifference b c (-db) bc
  let abc := massDividedDifference a b ac bc
  let aabc := massDividedDifference a b aac abc
  let abbc := massDividedDifference a b abc bbc
  let aabbc := massDividedDifference a b aabc abbc
  abc - a * aabc - b * abbc + a * b * aabbc

/-- The five partial-fraction coefficients act on arbitrary single-node
values and derivatives. The common factor removes the two dressed
Pauli–Villars differences. -/
theorem bubbleDividedDifference_eq_partialFractions {a b c : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (fa fb fc da db : ℝ) :
    (b - a) ^ 2 * bubbleDividedDifference a b c fa fb fc da db =
      bubCoefC a b c * fc + bubCoefA a b c * fa + bubCoefB a b c * fb -
        bubCoefA2 a c * da - bubCoefB2 b c * db := by
  have e₁ : b - a = -(a - b) := by ring
  have e₂ : c - a = -(a - c) := by ring
  have e₃ : c - b = -(b - c) := by ring
  simp only [bubbleDividedDifference, massDividedDifference, e₁, e₂, e₃,
    bubCoefC, bubCoefA, bubCoefB, bubCoefA2, bubCoefB2]
  field_simp [sub_ne_zero.mpr hab, sub_ne_zero.mpr hac, sub_ne_zero.mpr hbc]
  ring

end QED.ChainProof.SetCRegX

end
