/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegMainBDT

/-!
# Transverse crossed-pair normalization

The placements 2 and 3 of `QED/ChainProof/SetCRegMainBDT.lean` repeat slots 5 and 4.
The real-part convention in `QED/ChainProof/SetCRegFront.lean` includes division by `I`.
-/

public section

open Complex Real
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCMainB QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM

/-- Extract the common real prefactor of the two crossed transverse placements. -/
theorem uBDT_crossed_pair (P : Params) (he : P.e ≠ 0) (hm : P.m ≠ 0) (mγ Λ T : ℝ) :
    64 * π ^ 6 / P.e ^ 6 * ((1 / I) * (uBDT P 2 mγ Λ T + uBDT P 3 mγ Λ T)).re =
      (π ^ 4 * (Λ ^ 2 - mγ ^ 2) / (4 * P.e ^ 5 * P.m ^ 5)) *
        (kerT .X { P with mγ := mγ, Λ := Λ } 5 mγ Λ T +
          kerT .X { P with mγ := mγ, Λ := Λ } 4 mγ Λ T).im := by
  let R := { P with mγ := mγ, Λ := Λ }
  have hw : wD R 1 = ((-(Λ ^ 2 - mγ ^ 2) / 2 : ℝ) : ℂ) := by
    unfold wD
    change -(I / 2) * (↑(1 : ℝ) : ℂ) * ((1 / I) * ↑(Λ ^ 2 - mγ ^ 2)) = _
    push_cast
    field_simp
  have hp : -(vpCst P * wD R 1 / (64 * (P.e : ℂ) * (P.m : ℂ) ^ 5)) =
      ((P.e ^ 2 / (2 * π ^ 2) * (Λ ^ 2 - mγ ^ 2) / (128 * P.e * P.m ^ 5) : ℝ) : ℂ) := by
    rw [vpCst, hw]
    push_cast
    ring
  have h2 : repBClass 2 = .X := rfl
  have h3 : repBClass 3 = .X := rfl
  have hs2 : repBSlot 2 = 5 := rfl
  have hs3 : repBSlot 3 = 4 := rfl
  simp only [uBDT, h2, h3, hs2, hs3, ← mul_add]
  change 64 * π ^ 6 / P.e ^ 6 * ((1 / I) * (_ * (_ + _))).re = _
  rw [hp, one_div, inv_I, ← mul_assoc]
  simp only [neg_mul, neg_re, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
    zero_mul, one_mul, sub_zero, zero_sub, zero_add, neg_neg]
  field_simp [Real.pi_ne_zero]
  ring

end QED.ChainProof.SetCRegDisp

end
