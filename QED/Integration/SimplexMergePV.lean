/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Integrating out a Pauli–Villars split

A Pauli–Villars photon line is a pair of lines with masses `μ₁ = m_γ`, `μ₂ = Λ` and parameters
`(t, w - t)`, `w` the merged parameter. A parametric integrand depends on the split through
`V = K + β t` with `β = μ₁² - μ₂²`, and the split integral is the divided difference
`∫₀^w (K + β t)^{-(n+2)} dt = (K^{-(n+1)} - (K + β w)^{-(n+1)}) / ((n+1) β)`
(`integral_inv_pow_affine`), for `K > 0`, `K + β w > 0`, `β ≠ 0`.
-/

public section

open MeasureTheory Set

namespace QED.Integration.SimplexMerge

theorem pos_of_mem_uIcc_affine {K β w t : ℝ} (hK : 0 < K) (hKw : 0 < K + β * w)
    (ht : t ∈ uIcc 0 w) : 0 < K + β * t := by
  rcases le_total 0 w with hw | hw
  · rw [uIcc_of_le hw] at ht
    rcases le_total 0 β with hβ | hβ
    · nlinarith [mul_nonneg hβ ht.1]
    · nlinarith [mul_le_mul_of_nonpos_left ht.2 hβ]
  · rw [uIcc_of_ge hw] at ht
    rcases le_total 0 β with hβ | hβ
    · nlinarith [mul_le_mul_of_nonneg_left ht.1 hβ]
    · nlinarith [mul_nonneg_of_nonpos_of_nonpos hβ ht.2]

theorem continuousOn_inv_pow_affine {K β w : ℝ} (n : ℕ) (hK : 0 < K) (hKw : 0 < K + β * w) :
    ContinuousOn (fun t => ((K + β * t) ^ n)⁻¹) (uIcc 0 w) :=
  ContinuousOn.inv₀ (by fun_prop) fun t ht =>
    pow_ne_zero _ (pos_of_mem_uIcc_affine hK hKw ht).ne'

theorem intervalIntegrable_inv_pow_affine {K β w : ℝ} (n : ℕ) (hK : 0 < K)
    (hKw : 0 < K + β * w) :
    IntervalIntegrable (fun t => ((K + β * t) ^ n)⁻¹) volume 0 w :=
  (continuousOn_inv_pow_affine n hK hKw).intervalIntegrable

/-- **The Pauli–Villars split integral**:
`∫₀^w (K + β t)^{-(n+2)} dt = (K^{-(n+1)} - (K + β w)^{-(n+1)}) / ((n+1) β)`. -/
theorem integral_inv_pow_affine {K β w : ℝ} (n : ℕ) (hβ : β ≠ 0) (hK : 0 < K)
    (hKw : 0 < K + β * w) :
    ∫ t in (0 : ℝ)..w, ((K + β * t) ^ (n + 2))⁻¹ =
      ((K ^ (n + 1))⁻¹ - ((K + β * w) ^ (n + 1))⁻¹) / ((n + 1) * β) := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hderiv : ∀ t ∈ uIcc 0 w, HasDerivAt (fun t => -((K + β * t) ^ (n + 1))⁻¹ / ((n + 1) * β))
      (((K + β * t) ^ (n + 2))⁻¹) t := by
    intro t ht
    have hpos := pos_of_mem_uIcc_affine hK hKw ht
    have hlin : HasDerivAt (fun t => K + β * t) β t := by
      simpa using ((hasDerivAt_id t).const_mul β).const_add K
    have h := ((hlin.pow (n + 1)).inv (pow_ne_zero _ hpos.ne')).neg.div_const ((n + 1) * β)
    refine h.congr_deriv ?_
    have hp : (K + β * t) ≠ 0 := hpos.ne'
    simp only [Pi.pow_apply, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_inv_pow_affine (n + 2) hK hKw)]
  simp only [mul_zero, add_zero]
  ring

theorem integral_inv_pow_four_affine {K β w : ℝ} (hβ : β ≠ 0) (hK : 0 < K)
    (hKw : 0 < K + β * w) :
    ∫ t in (0 : ℝ)..w, ((K + β * t) ^ 4)⁻¹ =
      ((K ^ 3)⁻¹ - ((K + β * w) ^ 3)⁻¹) / (3 * β) := by
  have h := integral_inv_pow_affine 2 hβ hK hKw
  norm_num at h
  exact h

theorem integral_inv_pow_three_affine {K β w : ℝ} (hβ : β ≠ 0) (hK : 0 < K)
    (hKw : 0 < K + β * w) :
    ∫ t in (0 : ℝ)..w, ((K + β * t) ^ 3)⁻¹ =
      ((K ^ 2)⁻¹ - ((K + β * w) ^ 2)⁻¹) / (2 * β) := by
  have h := integral_inv_pow_affine 1 hβ hK hKw
  norm_num at h
  exact h

theorem integral_inv_pow_two_affine {K β w : ℝ} (hβ : β ≠ 0) (hK : 0 < K)
    (hKw : 0 < K + β * w) :
    ∫ t in (0 : ℝ)..w, ((K + β * t) ^ 2)⁻¹ = (K⁻¹ - (K + β * w)⁻¹) / β := by
  have h := integral_inv_pow_affine 0 hβ hK hKw
  norm_num at h
  exact h

end QED.Integration.SimplexMerge

end
