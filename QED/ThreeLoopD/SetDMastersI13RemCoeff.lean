/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13RemAnalytic
public import QED.ThreeLoopD.SetDMastersI13Wire

/-!
# Set (d), master `I₁₃`: from the Taylor coefficients of `Rem` to the master

`QED.ThreeLoopD.hasTruncLaurent_i13Rem_coeff` expands `Rem` through `ε⁴` with the coefficients
`cₖ = QED.ThreeLoopD.i13RemCoeff k`. Once these are known to equal the target values
`R₀, …, R₄` of `QED.ThreeLoopD.i13RemLaurent`, the expansion of the master follows from
`QED.ThreeLoopD.hasTruncLaurent_setDMasterI13_of_Rem`
(`QED.ThreeLoopD.hasTruncLaurent_setDMasterI13_of_coeff`).

The constant term is computed here: at `ε = 0` the bubble is `1`, the subtraction is `t`, and
`c₀ = ∫₀¹ t dt = 1/2` (`QED.ThreeLoopD.i13RemCoeff_zero`).

## Main results

* `QED.ThreeLoopD.i13RemCoeff_zero`.
* `QED.ThreeLoopD.hasTruncLaurent_setDMasterI13_of_coeff`.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

theorem i13Bub_zero (t : ℝ) : i13Bub 0 t = 1 := by
  unfold i13Bub
  simp [Real.volume_real_Ioo_of_le zero_le_one]

theorem i13G_zero : i13G 0 = 1 := by
  unfold i13G
  simp

theorem i13RemInt1_zero (t : ℝ) : i13RemInt1 t 0 = t := by
  unfold i13RemInt1
  rw [i13Bub_zero, sub_zero, cpow_one]
  ring

theorem i13RemInt2_zero {t : ℝ} (ht : 0 < t) : i13RemInt2 t 0 = 0 := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  unfold i13RemInt2 i13Asym i13Al0 i13Al1 i13Al2 i13Be0 i13Be1
  rw [i13Bub_zero, i13G_zero]
  simp only [mul_zero, sub_zero, zero_sub, cpow_one, cpow_zero, cpow_neg_one]
  field_simp
  ring

/-- **The constant term** `c₀ = 1/2`. -/
theorem i13RemCoeff_zero : i13RemCoeff 0 = 1 / 2 := by
  unfold i13RemCoeff
  simp only [i13Dsl_zero, i13RemInt1_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t (ht : t ∈ Ioi (1 : ℝ)) =>
    i13RemInt2_zero (zero_lt_one.trans ht)), integral_zero, add_zero, integral_complex_ofReal,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_id]
  push_cast
  ring

theorem i13RemLaurent_eq_sum {c : ℕ → ℂ} (h0 : c 0 = 1 / 2) (h1 : c 1 = -9 / 4)
    (h2 : c 2 = -7 / 6 * (π : ℂ) ^ 2 - 4 * (zeta3 : ℂ) - 47 / 8)
    (h3 : c 3 = -1 / 90 * (π : ℂ) ^ 4 - 47 / 12 * (π : ℂ) ^ 2 + 12 * (zeta3 : ℂ) - 97 / 16)
    (h4 : c 4 = -133 / 45 * (π : ℂ) ^ 4 + 2 / 3 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
      - 32 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 - 427 / 24 * (π : ℂ) ^ 2 + 176 * (zeta3 : ℂ)
      - 12 * (zeta5 : ℂ) + 32 / 3 * (Real.log 2 : ℂ) ^ 4 + 256 * (Li 4 (1 / 2) : ℂ) + 841 / 32)
    (ε : ℂ) : ∑ k ∈ Finset.range 5, c k * ε ^ k = i13RemLaurent ε := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3, h4, i13RemLaurent]
  ring

/-- **The master from the five coefficients**: if `cₖ = Rₖ` for `k ≤ 4` (`c₀ = R₀` is
`QED.ThreeLoopD.i13RemCoeff_zero`), then `I₁₃ C⁻¹` has the LR96 expansion through `ε³`. -/
theorem hasTruncLaurent_setDMasterI13_of_coeff (h1 : i13RemCoeff 1 = -9 / 4)
    (h2 : i13RemCoeff 2 = -7 / 6 * (π : ℂ) ^ 2 - 4 * (zeta3 : ℂ) - 47 / 8)
    (h3 : i13RemCoeff 3 =
      -1 / 90 * (π : ℂ) ^ 4 - 47 / 12 * (π : ℂ) ^ 2 + 12 * (zeta3 : ℂ) - 97 / 16)
    (h4 : i13RemCoeff 4 = -133 / 45 * (π : ℂ) ^ 4 + 2 / 3 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
      - 32 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 - 427 / 24 * (π : ℂ) ^ 2 + 176 * (zeta3 : ℂ)
      - 12 * (zeta5 : ℂ) + 32 / 3 * (Real.log 2 : ℂ) ^ 4 + 256 * (Li 4 (1 / 2) : ℂ) + 841 / 32) :
    HasTruncLaurent setDMasterI13 setDLaurentI13 3 := by
  refine hasTruncLaurent_setDMasterI13_of_Rem ?_
  have h := hasTruncLaurent_i13Rem_coeff
  have e : (fun ε => ∑ k ∈ Finset.range 5, i13RemCoeff k * ε ^ k) = i13RemLaurent :=
    funext (i13RemLaurent_eq_sum i13RemCoeff_zero h1 h2 h3 h4)
  rwa [e] at h

end QED.ThreeLoopD
