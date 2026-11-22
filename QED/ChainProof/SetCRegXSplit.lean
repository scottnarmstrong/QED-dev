/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SimplexMergePV

/-!
# Set (c), Stage L1: split a photon group by mass

These split integrals use the affine primitive in `QED/Integration/SimplexMergePV.lean`.
The equal-mass split gives the group size times the higher resolvent power.
-/

public section

namespace QED.ChainProof.SetCRegX

open QED.Integration.SimplexMerge

/-- Integrating a split with distinct masses gives a divided difference of resolvents. -/
theorem integral_mass_split {K a b w : ℝ} (n : ℕ) (hab : a ≠ b)
    (ha : 0 < K + a * w) (hb : 0 < K + b * w) :
    ∫ t in (0 : ℝ)..w, ((K + a * t + b * (w - t)) ^ (n + 2))⁻¹ =
      (((K + a * w) ^ (n + 1))⁻¹ - ((K + b * w) ^ (n + 1))⁻¹) /
        ((n + 1) * (b - a)) := by
  have he : K + b * w + (a - b) * w = K + a * w := by ring
  have hp : 0 < K + b * w + (a - b) * w := he ▸ ha
  simp_rw [show ∀ t, K + a * t + b * (w - t) = K + b * w + (a - b) * t by
    intro t
    ring]
  rw [integral_inv_pow_affine n (sub_ne_zero.mpr hab) hb hp, he]
  rw [show b - a = -(a - b) by ring, mul_neg, div_neg, ← neg_div, neg_sub]

/-- Integrating a split with equal masses gives the factor for a double pole. -/
theorem integral_mass_split_repeat (K a w : ℝ) (n : ℕ) :
    ∫ t in (0 : ℝ)..w, ((K + a * t + a * (w - t)) ^ (n + 2))⁻¹ =
      w * ((K + a * w) ^ (n + 2))⁻¹ := by
  simp_rw [show ∀ t, K + a * t + a * (w - t) = K + a * w by
    intro t
    ring]
  simp

end QED.ChainProof.SetCRegX

end
