/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKDYA
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integrals over the two-simplex of inverse powers of an affine function

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step S6 of the plan (b1b, the
three-line blocks of the quadratic numerator). With
`Λ(u) = d₂ + (d₀ - d₂) u₀ + (d₁ - d₂) u₁` (the convex combination of `d₀, d₁, d₂ > 0` at the
barycentric point of `u ∈ Δ₂`) and pairwise distinct `dᵢ`:

* `integral_simplexTwo_inv_sq`:
  `∫_{Δ₂} Λ⁻² = ([d₁, d₂]_{log} - [d₁, d₀]_{log}) / (d₀ - d₂)`;
* `integral_simplexTwo_inv`:
  `∫_{Δ₂} Λ⁻¹ = ([d₀, d₁]_{x log x} - [d₁, d₂]_{x log x}) / (d₀ - d₂)`,

where `[x, y]_f = (f x - f y)/(x - y)`. These are the second divided differences of `-log` and
`x log x` (the Hermite–Genocchi formula in this case).
-/

@[expose] public section

open MeasureTheory Set intervalIntegral

namespace QED.ChainProof.SetCRegDisp

open QED.Integration.Feynman (simplexSet isCompact_simplexSet measurableSet_simplexSet)
open QED.ChainProof.SetAKS (ksD_integral_simplexTwo)

theorem comb_pos {d₀ d₁ d₂ w₀ w₁ w₂ : ℝ} (h₀ : 0 < d₀) (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (hw₀ : 0 ≤ w₀) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : w₀ + w₁ + w₂ = 1) :
    0 < d₀ * w₀ + d₁ * w₁ + d₂ * w₂ := by
  set c := min d₀ (min d₁ d₂)
  have hc : 0 < c := lt_min h₀ (lt_min h₁ h₂)
  have e₀ : c * w₀ ≤ d₀ * w₀ := mul_le_mul_of_nonneg_right (min_le_left _ _) hw₀
  have e₁ : c * w₁ ≤ d₁ * w₁ :=
    mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) hw₁
  have e₂ : c * w₂ ≤ d₂ * w₂ :=
    mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hw₂
  nlinarith

/-- `∫₀¹ (p + q t)⁻¹ dt = (log (p + q) - log p)/q` for `p, p + q > 0`, `q ≠ 0`. -/
theorem integral_inv_affine {p q : ℝ} (hp : 0 < p) (hpq : 0 < p + q) (hq : q ≠ 0) :
    ∫ t in (0 : ℝ)..1, (p + q * t)⁻¹ = (Real.log (p + q) - Real.log p) / q := by
  have hpos : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < p + q * t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have := comb_pos hp hpq hpq (w₀ := 1 - t) (w₁ := t) (w₂ := 0) (by linarith [ht.2])
      ht.1 le_rfl (by ring)
    nlinarith
  rw [integral_eq_sub_of_hasDerivAt (f := fun t => Real.log (p + q * t) / q)]
  · simp only [mul_zero, add_zero, mul_one]
    ring
  · intro t ht
    have h := ((hasDerivAt_id' t).const_mul q).const_add p
    refine ((h.log (hpos t ht).ne').div_const q).congr_deriv ?_
    have := (hpos t ht).ne'
    field_simp
  · exact (ContinuousOn.inv₀ (by fun_prop) fun t ht => (hpos t ht).ne').intervalIntegrable

/-- `∫₀¹ log (p + q t) dt = ((p + q) log (p + q) - p log p)/q - 1`. -/
theorem integral_log_affine {p q : ℝ} (hp : 0 < p) (hpq : 0 < p + q) (hq : q ≠ 0) :
    ∫ t in (0 : ℝ)..1, Real.log (p + q * t) =
      ((p + q) * Real.log (p + q) - p * Real.log p) / q - 1 := by
  have hpos : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < p + q * t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have := comb_pos hp hpq hpq (w₀ := 1 - t) (w₁ := t) (w₂ := 0) (by linarith [ht.2])
      ht.1 le_rfl (by ring)
    nlinarith
  rw [integral_eq_sub_of_hasDerivAt
    (f := fun t => ((p + q * t) * Real.log (p + q * t) - (p + q * t)) / q)]
  · simp only [mul_zero, add_zero, mul_one]
    field_simp
    ring
  · intro t ht
    have h := ((hasDerivAt_id' t).const_mul q).const_add p
    have hl := h.log (hpos t ht).ne'
    refine (((h.fun_mul hl).fun_sub h).div_const q).congr_deriv ?_
    have := (hpos t ht).ne'
    field_simp
    ring
  · exact (ContinuousOn.log (by fun_prop) fun t ht => (hpos t ht).ne').intervalIntegrable

/-- The affine function `Λ(u)` on `Δ₂`. -/
def simplexAff (d₀ d₁ d₂ : ℝ) (u : Fin 2 → ℝ) : ℝ := d₂ + (d₀ - d₂) * u 0 + (d₁ - d₂) * u 1

theorem simplexAff_pos {d₀ d₁ d₂ : ℝ} (h₀ : 0 < d₀) (h₁ : 0 < d₁) (h₂ : 0 < d₂) {r t : ℝ}
    (hr : 0 ≤ r) (ht : 0 ≤ t) (hrt : r + t ≤ 1) : 0 < d₂ + (d₀ - d₂) * r + (d₁ - d₂) * t := by
  have := comb_pos h₀ h₁ h₂ hr ht (by linarith : 0 ≤ 1 - r - t) (by ring)
  nlinarith

theorem simplexAff_pos_of_mem {d₀ d₁ d₂ : ℝ} (h₀ : 0 < d₀) (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    {u : Fin 2 → ℝ} (hu : u ∈ simplexSet 2) : 0 < simplexAff d₀ d₁ d₂ u := by
  obtain ⟨hnn, hs⟩ := (QED.Integration.SimplexMerge.mem_simplexSet_iff_le two_pos u).1 hu
  rw [Fin.sum_univ_two] at hs
  exact simplexAff_pos h₀ h₁ h₂ (hnn 0) (hnn 1) hs

theorem continuous_simplexAff (d₀ d₁ d₂ : ℝ) : Continuous (simplexAff d₀ d₁ d₂) := by
  unfold simplexAff; fun_prop

/-- **`∫_{Δ₂} Λ⁻²`**. -/
theorem integral_simplexTwo_inv_sq {d₀ d₁ d₂ : ℝ} (h₀ : 0 < d₀) (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (h₀₁ : d₀ ≠ d₁) (h₀₂ : d₀ ≠ d₂) (h₁₂ : d₁ ≠ d₂) :
    ∫ u in simplexSet 2, (simplexAff d₀ d₁ d₂ u ^ 2)⁻¹ =
      ((Real.log d₁ - Real.log d₂) / (d₁ - d₂) - (Real.log d₁ - Real.log d₀) / (d₁ - d₀)) /
        (d₀ - d₂) := by
  have hg : IntegrableOn (fun u => (simplexAff d₀ d₁ d₂ u ^ 2)⁻¹) (simplexSet 2) :=
    (ContinuousOn.inv₀ ((continuous_simplexAff d₀ d₁ d₂).pow 2).continuousOn
      fun u hu => (pow_pos (simplexAff_pos_of_mem h₀ h₁ h₂ hu) 2).ne').integrableOn_compact
      (isCompact_simplexSet 2)
  rw [ksD_integral_simplexTwo hg]
  have hc : d₀ - d₂ ≠ 0 := sub_ne_zero.2 h₀₂
  -- the inner integral
  have hin : ∀ t ∈ uIcc (0 : ℝ) 1, ∫ r in (0 : ℝ)..(1 - t),
      (simplexAff d₀ d₁ d₂ ![r, t] ^ 2)⁻¹ =
        ((d₂ + (d₁ - d₂) * t)⁻¹ - (d₀ + (d₁ - d₀) * t)⁻¹) / (d₀ - d₂) := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hpos : ∀ r ∈ uIcc (0 : ℝ) (1 - t), 0 < d₂ + (d₀ - d₂) * r + (d₁ - d₂) * t := by
      intro r hr
      rw [uIcc_of_le (by linarith [ht.2])] at hr
      exact simplexAff_pos h₀ h₁ h₂ hr.1 ht.1 (by linarith [hr.2])
    simp only [simplexAff, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [integral_eq_sub_of_hasDerivAt
      (f := fun r => -((d₀ - d₂) * (d₂ + (d₀ - d₂) * r + (d₁ - d₂) * t))⁻¹)]
    · have e1 : d₂ + (d₀ - d₂) * (1 - t) + (d₁ - d₂) * t = d₀ + (d₁ - d₀) * t := by ring
      have e2 : d₂ + (d₀ - d₂) * 0 + (d₁ - d₂) * t = d₂ + (d₁ - d₂) * t := by ring
      simp only [e1, e2]
      field_simp
      ring
    · intro r hr
      have h := (((hasDerivAt_id' r).const_mul (d₀ - d₂)).const_add d₂).add_const
        ((d₁ - d₂) * t)
      refine ((h.const_mul (d₀ - d₂)).inv (mul_ne_zero hc (hpos r hr).ne')).neg.congr_deriv ?_
      have := (hpos r hr).ne'
      field_simp
    · exact (ContinuousOn.inv₀ (by fun_prop) fun r hr =>
        (pow_pos (hpos r hr) 2).ne').intervalIntegrable
  rw [integral_congr hin, intervalIntegral.integral_div,
    intervalIntegral.integral_sub (f := fun x => (d₂ + (d₁ - d₂) * x)⁻¹)
      (g := fun x => (d₀ + (d₁ - d₀) * x)⁻¹)
      (ContinuousOn.inv₀ (by fun_prop) fun t ht => ?_).intervalIntegrable
      (ContinuousOn.inv₀ (by fun_prop) fun t ht => ?_).intervalIntegrable,
    integral_inv_affine h₂ (by linarith) (sub_ne_zero.2 h₁₂),
    integral_inv_affine h₀ (by linarith) (sub_ne_zero.2 (Ne.symm h₀₁))]
  · ring_nf
  · rw [uIcc_of_le zero_le_one] at ht
    have := simplexAff_pos h₀ h₁ h₂ le_rfl ht.1 (by linarith [ht.2])
    nlinarith
  · rw [uIcc_of_le zero_le_one] at ht
    have := simplexAff_pos h₀ h₁ h₂ (by linarith [ht.2] : 0 ≤ 1 - t) ht.1 (by linarith)
    nlinarith

/-- **`∫_{Δ₂} Λ⁻¹`**. -/
theorem integral_simplexTwo_inv {d₀ d₁ d₂ : ℝ} (h₀ : 0 < d₀) (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (h₀₁ : d₀ ≠ d₁) (h₀₂ : d₀ ≠ d₂) (h₁₂ : d₁ ≠ d₂) :
    ∫ u in simplexSet 2, (simplexAff d₀ d₁ d₂ u)⁻¹ =
      ((d₁ * Real.log d₁ - d₀ * Real.log d₀) / (d₁ - d₀) -
        (d₁ * Real.log d₁ - d₂ * Real.log d₂) / (d₁ - d₂)) / (d₀ - d₂) := by
  have hg : IntegrableOn (fun u => (simplexAff d₀ d₁ d₂ u)⁻¹) (simplexSet 2) :=
    (ContinuousOn.inv₀ (continuous_simplexAff d₀ d₁ d₂).continuousOn
      fun u hu => (simplexAff_pos_of_mem h₀ h₁ h₂ hu).ne').integrableOn_compact
      (isCompact_simplexSet 2)
  rw [ksD_integral_simplexTwo hg]
  have hc : d₀ - d₂ ≠ 0 := sub_ne_zero.2 h₀₂
  have hE : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < d₂ + (d₁ - d₂) * t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have := simplexAff_pos h₀ h₁ h₂ le_rfl ht.1 (by linarith [ht.2])
    nlinarith
  have hF : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < d₀ + (d₁ - d₀) * t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have := simplexAff_pos h₀ h₁ h₂ (by linarith [ht.2] : 0 ≤ 1 - t) ht.1 (by linarith)
    nlinarith
  have hin : ∀ t ∈ uIcc (0 : ℝ) 1, ∫ r in (0 : ℝ)..(1 - t), (simplexAff d₀ d₁ d₂ ![r, t])⁻¹ =
      (Real.log (d₀ + (d₁ - d₀) * t) - Real.log (d₂ + (d₁ - d₂) * t)) / (d₀ - d₂) := by
    intro t ht
    have ht' := ht
    rw [uIcc_of_le zero_le_one] at ht'
    have hpos : ∀ r ∈ uIcc (0 : ℝ) (1 - t), 0 < d₂ + (d₀ - d₂) * r + (d₁ - d₂) * t := by
      intro r hr
      rw [uIcc_of_le (by linarith [ht'.2])] at hr
      exact simplexAff_pos h₀ h₁ h₂ hr.1 ht'.1 (by linarith [hr.2])
    simp only [simplexAff, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [integral_eq_sub_of_hasDerivAt
      (f := fun r => Real.log (d₂ + (d₀ - d₂) * r + (d₁ - d₂) * t) / (d₀ - d₂))]
    · have e1 : d₂ + (d₀ - d₂) * (1 - t) + (d₁ - d₂) * t = d₀ + (d₁ - d₀) * t := by ring
      have e2 : d₂ + (d₀ - d₂) * 0 + (d₁ - d₂) * t = d₂ + (d₁ - d₂) * t := by ring
      simp only [e1, e2]
      ring
    · intro r hr
      have h := (((hasDerivAt_id' r).const_mul (d₀ - d₂)).const_add d₂).add_const
        ((d₁ - d₂) * t)
      refine ((h.log (hpos r hr).ne').div_const (d₀ - d₂)).congr_deriv ?_
      have := (hpos r hr).ne'
      field_simp
    · exact (ContinuousOn.inv₀ (by fun_prop) fun r hr => (hpos r hr).ne').intervalIntegrable
  rw [integral_congr hin, intervalIntegral.integral_div,
    intervalIntegral.integral_sub (f := fun x => Real.log (d₀ + (d₁ - d₀) * x))
      (g := fun x => Real.log (d₂ + (d₁ - d₂) * x))
      (ContinuousOn.log (by fun_prop) fun t ht => (hF t ht).ne').intervalIntegrable
      (ContinuousOn.log (by fun_prop) fun t ht => (hE t ht).ne').intervalIntegrable,
    integral_log_affine h₀ (by linarith) (sub_ne_zero.2 (Ne.symm h₀₁)),
    integral_log_affine h₂ (by linarith) (sub_ne_zero.2 h₁₂)]
  ring_nf

end QED.ChainProof.SetCRegDisp

end
