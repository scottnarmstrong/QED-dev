/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RestAnalytic
public import QED.ThreeLoopD.SetDMastersI12Gamma

/-!
# Set (d), master `I₁₂`: the expansion of the remainder from its Taylor coefficients

`QED.ThreeLoopD.i12Rest` is analytic at `0` and vanishes there
(`QED.ThreeLoopD.SetDMastersI12RestAnalytic`). By Taylor's theorem for analytic functions
(`AnalyticAt.exists_eventuallyEq_sum_add_pow_mul`) its expansion through `ε ^ 4` is therefore
determined by the four numbers `iteratedDeriv k i12Rest 0 / k!`, `k = 1, …, 4`. This file reduces
`HasTruncLaurent i12Rest i12RestLaurent 5`, and so the set (d) input for `I₁₂`, to the four
identities `iteratedDeriv k i12Rest 0 / k! = rₖ` with the closed forms `rₖ` of
`QED.ThreeLoopD.i12RestLaurent` (`QED.ThreeLoopD.i12RestR1` … `QED.ThreeLoopD.i12RestR4`).

## Main results

* `QED.ThreeLoopD.hasTruncLaurent_of_analyticAt_zero`: Taylor's theorem in `HasTruncLaurent` form.
* `QED.ThreeLoopD.hasTruncLaurent_i12Rest_of_coeffs`,
  `QED.ThreeLoopD.hasTruncLaurent_setDMasterI12_of_coeffs`.
-/

@[expose] public section

open Complex Filter Topology QED.Polylog
open scoped Real

namespace QED.ThreeLoopD

/-- **Taylor's theorem as a truncated expansion**: a function analytic at `0` has the expansion
`∑_{k < n} f⁽ᵏ⁾(0) / k! εᵏ` to `O(εⁿ)`. -/
theorem hasTruncLaurent_of_analyticAt_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    HasTruncLaurent f
      (fun ε => ∑ k ∈ Finset.range n, iteratedDeriv k f 0 / k.factorial * ε ^ k) n := by
  obtain ⟨F, hF, hev⟩ := hf.exists_eventuallyEq_sum_add_pow_mul n
  refine ⟨F, hF, ?_⟩
  filter_upwards [nhdsWithin_le_nhds hev] with ε hε
  rw [hε, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul]; ring

/-- The target value of the Taylor coefficient `r1` of `QED.ThreeLoopD.i12Rest`. -/
noncomputable def i12RestR1 : ℂ :=
  -11 / 3 * (π : ℂ) ^ 2 - 8 * (Real.log 2 : ℂ) ^ 2 - 71 / 6

/-- The target value of the Taylor coefficient `r2` of `QED.ThreeLoopD.i12Rest`. -/
noncomputable def i12RestR2 : ℂ :=
  2 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) + 17 / 6 * (π : ℂ) ^ 2 + 8 * (zeta3 : ℂ) +
      4 * (Real.log 2 : ℂ) ^ 2 + 179 / 36

/-- The target value of the Taylor coefficient `r3` of `QED.ThreeLoopD.i12Rest`. -/
noncomputable def i12RestR3 : ℂ :=
  -7 / 60 * (π : ℂ) ^ 4 - 10 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 -
      1 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) - 401 / 12 * (π : ℂ) ^ 2 + 2 * (zeta3 : ℂ) -
      8 / 3 * (Real.log 2 : ℂ) ^ 4 + 4 * (Real.log 2 : ℂ) ^ 2 + 47233 / 216

/-- The target value of the Taylor coefficient `r4` of `QED.ThreeLoopD.i12Rest`. -/
noncomputable def i12RestR4 : ℂ :=
  3 / 10 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) - 19 / 40 * (π : ℂ) ^ 4 -
      34 / 3 * (π : ℂ) ^ 2 * (zeta3 : ℂ) + 4 / 9 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 3 +
      5 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 + 1535 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) -
      7447 / 24 * (π : ℂ) ^ 2 - 16 * (zeta3 : ℂ) * (Real.log 2 : ℂ) ^ 2 -
      3709 / 3 * (zeta3 : ℂ) - 120 * (zeta5 : ℂ) + 4 / 3 * (Real.log 2 : ℂ) ^ 4 +
      4 * (Real.log 2 : ℂ) ^ 2 + 1810835 / 1296

theorem i12RestLaurent_eq_coeffs (ε : ℂ) :
    i12RestLaurent ε = i12RestR1 * ε + i12RestR2 * ε ^ 2 + i12RestR3 * ε ^ 3 +
      i12RestR4 * ε ^ 4 := by
  simp only [i12RestLaurent, i12RestR1, i12RestR2, i12RestR3, i12RestR4]

/-- **The expansion of the remainder from its four Taylor coefficients.** -/
theorem hasTruncLaurent_i12Rest_of_coeffs
    (h1 : iteratedDeriv 1 i12Rest 0 / (1 : ℕ).factorial = i12RestR1)
    (h2 : iteratedDeriv 2 i12Rest 0 / (2 : ℕ).factorial = i12RestR2)
    (h3 : iteratedDeriv 3 i12Rest 0 / (3 : ℕ).factorial = i12RestR3)
    (h4 : iteratedDeriv 4 i12Rest 0 / (4 : ℕ).factorial = i12RestR4) :
    HasTruncLaurent i12Rest i12RestLaurent 5 := by
  obtain ⟨F, hF, hev⟩ := hasTruncLaurent_of_analyticAt_zero analyticAt_i12Rest 5
  refine ⟨F, hF, ?_⟩
  filter_upwards [hev] with ε hε
  rw [hε, i12RestLaurent_eq_coeffs]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDeriv_zero, i12Rest_zero]
  rw [h1, h2, h3, h4]
  ring

/-- **The set (d) input for `I₁₂`, from the four Taylor coefficients of the remainder.** -/
theorem hasTruncLaurent_setDMasterI12_of_coeffs
    (h1 : iteratedDeriv 1 i12Rest 0 / (1 : ℕ).factorial = i12RestR1)
    (h2 : iteratedDeriv 2 i12Rest 0 / (2 : ℕ).factorial = i12RestR2)
    (h3 : iteratedDeriv 3 i12Rest 0 / (3 : ℕ).factorial = i12RestR3)
    (h4 : iteratedDeriv 4 i12Rest 0 / (4 : ℕ).factorial = i12RestR4) :
    HasTruncLaurent setDMasterI12 setDLaurentI12 3 :=
  hasTruncLaurent_setDMasterI12_of_rest (hasTruncLaurent_i12Rest_of_coeffs h1 h2 h3 h4)

end QED.ThreeLoopD
