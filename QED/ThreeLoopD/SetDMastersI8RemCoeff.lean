/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R0
public import QED.ThreeLoopD.SetDMastersI8Wire

/-!
# Set (d), master `I₈`: from the Taylor coefficients of `Rem` to the master

`QED.ThreeLoopD.hasTruncLaurent_i8Rem_coeff` expands `Rem` through `ε⁴` with the coefficients
`cₖ = QED.ThreeLoopD.i8RemCoeff k`, and `c₀ = 3/2` (`QED.ThreeLoopD.i8RemCoeff_zero`). Once
`c₁, …, c₄` are known to equal the target values of `QED.ThreeLoopD.i8RemLaurent`, the expansion
of the master follows from `QED.ThreeLoopD.hasTruncLaurent_setDMasterI8_of_Rem`
(`QED.ThreeLoopD.hasTruncLaurent_setDMasterI8_of_coeff`).

## Main results

* `QED.ThreeLoopD.hasTruncLaurent_setDMasterI8_of_coeff`.
-/

@[expose] public section

open Complex Real QED.Polylog

namespace QED.ThreeLoopD

theorem i8RemLaurent_eq_sum {c : ℕ → ℂ} (h0 : c 0 = 3 / 2)
    (h1 : c 1 = -1 / 6 * (π : ℂ) ^ 2 + 39 / 4)
    (h2 : c 2 = -13 / 3 * (π : ℂ) ^ 2 + 2 * (zeta3 : ℂ) + 491 / 8)
    (h3 : c 3 = -25 / 72 * (π : ℂ) ^ 4 + 16 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ)
      - 379 / 12 * (π : ℂ) ^ 2 - 80 * (zeta3 : ℂ) + 5539 / 16)
    (h4 : c 4 = 323 / 120 * (π : ℂ) ^ 4 + 62 / 3 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
      - 80 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 + 152 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ)
      - 4259 / 24 * (π : ℂ) ^ 2 - 763 * (zeta3 : ℂ) - 126 * (zeta5 : ℂ)
      - 64 / 3 * (Real.log 2 : ℂ) ^ 4 - 512 * (Li 4 (1 / 2) : ℂ) + 56307 / 32)
    (ε : ℂ) : ∑ k ∈ Finset.range 5, c k * ε ^ k = i8RemLaurent ε := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3, h4, i8RemLaurent]
  ring

/-- **The master from the coefficients**: if `cₖ` takes its target value for `1 ≤ k ≤ 4`
(`c₀ = 3/2` is `QED.ThreeLoopD.i8RemCoeff_zero`), then `I₈ C⁻¹` has the LR96 expansion through
`ε²`. -/
theorem hasTruncLaurent_setDMasterI8_of_coeff (h1 : i8RemCoeff 1 = -1 / 6 * (π : ℂ) ^ 2 + 39 / 4)
    (h2 : i8RemCoeff 2 = -13 / 3 * (π : ℂ) ^ 2 + 2 * (zeta3 : ℂ) + 491 / 8)
    (h3 : i8RemCoeff 3 = -25 / 72 * (π : ℂ) ^ 4 + 16 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ)
      - 379 / 12 * (π : ℂ) ^ 2 - 80 * (zeta3 : ℂ) + 5539 / 16)
    (h4 : i8RemCoeff 4 = 323 / 120 * (π : ℂ) ^ 4 + 62 / 3 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
      - 80 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 + 152 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ)
      - 4259 / 24 * (π : ℂ) ^ 2 - 763 * (zeta3 : ℂ) - 126 * (zeta5 : ℂ)
      - 64 / 3 * (Real.log 2 : ℂ) ^ 4 - 512 * (Li 4 (1 / 2) : ℂ) + 56307 / 32) :
    HasTruncLaurent setDMasterI8 setDLaurentI8 3 := by
  refine hasTruncLaurent_setDMasterI8_of_Rem ?_
  have h := hasTruncLaurent_i8Rem_coeff
  have e : (fun ε => ∑ k ∈ Finset.range 5, i8RemCoeff k * ε ^ k) = i8RemLaurent :=
    funext (i8RemLaurent_eq_sum i8RemCoeff_zero h1 h2 h3 h4)
  rwa [e] at h

end QED.ThreeLoopD
