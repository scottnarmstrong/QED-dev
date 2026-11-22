/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegMainBDT
public import QED.ChainProof.SetCRegXPower

/-!
# Numerator recursion and normalization for every transverse placement of set (c)

The numerator recursion of `QED/ChainProof/SetCRegXPower.lean` applies to all
twelve placements. The normalization multiplies the imaginary part of each Pauli
value by a common real factor. Both steps extend to spectral coincidence.
-/

@[expose] public section

open Complex Real
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.TwoLoop.Enumeration QED.TwoLoop.ClassIntegrable
open QED.ChainProof.SetCMainB QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM

/-- Expand the dressed placement into units with zero photon numerator power. -/
theorem kerT_eq_zero_units {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {mγ Λ T : ℝ}
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) :
    let M := √(P.m ^ 2 * T)
    kerT c P s mγ Λ T =
      unitMPauliZero c P s (fun _ => 1) (unitMMasses P.m mγ Λ mγ Λ ![M]) -
        (mγ ^ 2 : ℂ) * unitMPauliZero c P s (fun _ => 1)
          (unitMMasses P.m mγ Λ mγ Λ ![M, mγ]) -
        (Λ ^ 2 : ℂ) * (unitMPauliZero c P s (fun _ => 1)
          (unitMMasses P.m mγ Λ mγ Λ ![M, Λ]) -
          (mγ ^ 2 : ℂ) * unitMPauliZero c P s (fun _ => 1)
            (unitMMasses P.m mγ Λ mγ Λ ![M, Λ, mγ])) := by
  intro M
  have hM : 0 < M := Real.sqrt_pos.2 (mul_pos (pow_pos hm _) hT)
  let μ₀ := min M (min mγ Λ)
  have hμ₀ : 0 < μ₀ := lt_min hM (lt_min hmγ hΛ)
  have hγ : μ₀ ≤ mγ := (min_le_right _ _).trans (min_le_left _ _)
  have hΛ' : μ₀ ≤ Λ := (min_le_right _ _).trans (min_le_right _ _)
  simpa only [kerT, repBExtra, ofReal_pow] using
    unitMPauliZeroPow_three_two hc P hm hs hμ₀ (massesGe_repB hγ hΛ')
      (x := M) (min_le_left _ _) hγ hΛ'

/-- Extract the common real prefactor for any of the twelve transverse placements. -/
theorem uBDT_normalized_real (P : Params) (he : P.e ≠ 0) (hm : P.m ≠ 0)
    (i : Fin 12) (mγ Λ T : ℝ) :
    64 * π ^ 6 / P.e ^ 6 * ((1 / I) * uBDT P i mγ Λ T).re =
      (π ^ 4 * (Λ ^ 2 - mγ ^ 2) / (4 * P.e ^ 5 * P.m ^ 5)) *
        (kerT (repBClass i) { P with mγ := mγ, Λ := Λ } (repBSlot i) mγ Λ T).im := by
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
  unfold uBDT
  change 64 * π ^ 6 / P.e ^ 6 * ((1 / I) * (_ * _)).re = _
  rw [hp, one_div, inv_I, ← mul_assoc]
  simp only [neg_mul, neg_re, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
    zero_mul, one_mul, sub_zero, zero_sub, zero_add, neg_neg]
  field_simp [Real.pi_ne_zero]
  ring

end QED.ChainProof.SetCRegDisp

end
