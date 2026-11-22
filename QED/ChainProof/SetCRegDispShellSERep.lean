/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSEQBlk
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The two-simplex integrals of the three-line block at a repeated node

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step S6 of the plan (b1b). The
quadratic part of the class `V` limit needs the three-line blocks `Q(a, a, b)` and `Q(a, b, b)`
(`QED/ChainProof/SetCRegDispShellSEExp.lean`), so the two-simplex integrals `seSimJ₂`,
`seSimJ₁` of `QED/ChainProof/SetCRegDispShellSEQBlk.lean` are needed with two equal nodes,
where the divided-difference closed forms `seSimI₂`, `seSimI₁` do not apply.

* `seSimJ₂_eq_iter`, `seSimJ₁_eq_iter`: after the inner integral, for `d₀ ≠ d₂` only,
  `J₂ = (∫₀¹ (d₂ + (d₁-d₂)t)⁻¹ - (d₀ + (d₁-d₀)t)⁻¹ dt)/(d₀ - d₂)` and
  `J₁ = (∫₀¹ log (d₀ + (d₁-d₀)t) - log (d₂ + (d₁-d₂)t) dt)/(d₀ - d₂)`;
* **`seSimJ₂_rep01`**, **`seSimJ₁_rep01`**: the nodes `(D, D, E)`;
* **`seSimJ₂_rep12`**, **`seSimJ₁_rep12`**: the nodes `(D, E, E)`.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral

namespace QED.ChainProof.SetCRegDisp

open QED.Integration.Feynman (simplexSet isCompact_simplexSet)
open QED.ChainProof.SetAKS (ksD_integral_simplexTwo)

section Iter

variable {d₀ d₁ d₂ : ℝ} (h₀ : 0 < d₀) (h₁ : 0 < d₁) (h₂ : 0 < d₂)

include h₀ h₁ h₂ in
theorem simplexEdge_pos_right {t : ℝ} (ht : t ∈ uIcc (0 : ℝ) 1) : 0 < d₂ + (d₁ - d₂) * t := by
  rw [uIcc_of_le zero_le_one] at ht
  have := simplexAff_pos h₀ h₁ h₂ le_rfl ht.1 (by linarith [ht.2])
  nlinarith

include h₀ h₁ h₂ in
theorem simplexEdge_pos_left {t : ℝ} (ht : t ∈ uIcc (0 : ℝ) 1) : 0 < d₀ + (d₁ - d₀) * t := by
  rw [uIcc_of_le zero_le_one] at ht
  have := simplexAff_pos h₀ h₁ h₂ (by linarith [ht.2] : 0 ≤ 1 - t) ht.1 (by linarith)
  nlinarith

include h₀ h₁ h₂ in
/-- **`J₂` after the inner integral**, for `d₀ ≠ d₂`. -/
theorem seSimJ₂_eq_iter (h₀₂ : d₀ ≠ d₂) :
    seSimJ₂ d₀ d₁ d₂ = (∫ t in (0 : ℝ)..1,
      ((d₂ + (d₁ - d₂) * t)⁻¹ - (d₀ + (d₁ - d₀) * t)⁻¹)) / (d₀ - d₂) := by
  have hg : IntegrableOn (fun u => (simplexAff d₀ d₁ d₂ u ^ 2)⁻¹) (simplexSet 2) :=
    (ContinuousOn.inv₀ ((continuous_simplexAff d₀ d₁ d₂).pow 2).continuousOn
      fun u hu => (pow_pos (simplexAff_pos_of_mem h₀ h₁ h₂ hu) 2).ne').integrableOn_compact
      (isCompact_simplexSet 2)
  unfold seSimJ₂
  rw [ksD_integral_simplexTwo hg]
  have hc : d₀ - d₂ ≠ 0 := sub_ne_zero.2 h₀₂
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
      have q1 : d₀ + (d₁ - d₀) * t ≠ 0 := by
        have := hpos (1 - t) (by rw [uIcc_of_le (by linarith [ht.2])]; exact ⟨by linarith [ht.2],
          le_rfl⟩)
        rw [e1] at this; exact this.ne'
      have q2 : d₂ + (d₁ - d₂) * t ≠ 0 := by
        have := hpos 0 (by rw [uIcc_of_le (by linarith [ht.2])]; exact ⟨le_rfl,
          by linarith [ht.2]⟩)
        rw [e2] at this; exact this.ne'
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
  rw [integral_congr hin, intervalIntegral.integral_div]

include h₀ h₁ h₂ in
/-- **`J₁` after the inner integral**, for `d₀ ≠ d₂`. -/
theorem seSimJ₁_eq_iter (h₀₂ : d₀ ≠ d₂) :
    seSimJ₁ d₀ d₁ d₂ = (∫ t in (0 : ℝ)..1,
      (Real.log (d₀ + (d₁ - d₀) * t) - Real.log (d₂ + (d₁ - d₂) * t))) / (d₀ - d₂) := by
  have hg : IntegrableOn (fun u => (simplexAff d₀ d₁ d₂ u)⁻¹) (simplexSet 2) :=
    (ContinuousOn.inv₀ (continuous_simplexAff d₀ d₁ d₂).continuousOn
      fun u hu => (simplexAff_pos_of_mem h₀ h₁ h₂ hu).ne').integrableOn_compact
      (isCompact_simplexSet 2)
  unfold seSimJ₁
  rw [ksD_integral_simplexTwo hg]
  have hc : d₀ - d₂ ≠ 0 := sub_ne_zero.2 h₀₂
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
  rw [integral_congr hin, intervalIntegral.integral_div]

end Iter

section Rep

variable {D E : ℝ} (hD : 0 < D) (hE : 0 < E) (hDE : D ≠ E)

include hD hE hDE in
/-- **`J₂` at the nodes `(D, D, E)`**: `((log D - log E)/(D - E) - D⁻¹)/(D - E)`. -/
theorem seSimJ₂_rep01 :
    seSimJ₂ D D E = ((Real.log D - Real.log E) / (D - E) - D⁻¹) / (D - E) := by
  rw [seSimJ₂_eq_iter hD hD hE hDE]
  have hpos : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < E + (D - E) * t := fun t ht =>
    simplexEdge_pos_right hD hD hE ht
  simp only [sub_self, zero_mul, add_zero]
  rw [intervalIntegral.integral_sub (f := fun t => (E + (D - E) * t)⁻¹) (g := fun _ => D⁻¹)
      (ContinuousOn.inv₀ (by fun_prop) fun t ht => (hpos t ht).ne').intervalIntegrable
      intervalIntegrable_const,
    integral_inv_affine hE (by linarith) (sub_ne_zero.2 hDE), intervalIntegral.integral_const]
  simp only [sub_zero, one_smul, add_sub_cancel]

include hD hE hDE in
/-- **`J₁` at the nodes `(D, D, E)`**: `(log D - (D log D - E log E)/(D - E) + 1)/(D - E)`. -/
theorem seSimJ₁_rep01 :
    seSimJ₁ D D E =
      (Real.log D - ((D * Real.log D - E * Real.log E) / (D - E) - 1)) / (D - E) := by
  rw [seSimJ₁_eq_iter hD hD hE hDE]
  have hpos : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < E + (D - E) * t := fun t ht =>
    simplexEdge_pos_right hD hD hE ht
  simp only [sub_self, zero_mul, add_zero]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
      (ContinuousOn.log (by fun_prop) fun t ht => (hpos t ht).ne').intervalIntegrable,
    integral_log_affine hE (by linarith) (sub_ne_zero.2 hDE), intervalIntegral.integral_const]
  simp only [sub_zero, add_sub_cancel, smul_eq_mul, one_mul]

include hD hE hDE in
/-- **`J₂` at the nodes `(D, E, E)`**: `(E⁻¹ - (log E - log D)/(E - D))/(D - E)`. -/
theorem seSimJ₂_rep12 :
    seSimJ₂ D E E = (E⁻¹ - (Real.log E - Real.log D) / (E - D)) / (D - E) := by
  rw [seSimJ₂_eq_iter hD hE hE hDE]
  have hpos : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < D + (E - D) * t := fun t ht =>
    simplexEdge_pos_left hD hE hE ht
  simp only [sub_self, zero_mul, add_zero]
  rw [intervalIntegral.integral_sub (f := fun _ => E⁻¹) (g := fun t => (D + (E - D) * t)⁻¹)
      intervalIntegrable_const
      (ContinuousOn.inv₀ (by fun_prop) fun t ht => (hpos t ht).ne').intervalIntegrable,
    integral_inv_affine hD (by linarith) (sub_ne_zero.2 (Ne.symm hDE)),
    intervalIntegral.integral_const]
  simp only [sub_zero, add_sub_cancel, smul_eq_mul, one_mul]

include hD hE hDE in
/-- **`J₁` at the nodes `(D, E, E)`**: `((E log E - D log D)/(E - D) - 1 - log E)/(D - E)`. -/
theorem seSimJ₁_rep12 :
    seSimJ₁ D E E =
      ((E * Real.log E - D * Real.log D) / (E - D) - 1 - Real.log E) / (D - E) := by
  rw [seSimJ₁_eq_iter hD hE hE hDE]
  have hpos : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < D + (E - D) * t := fun t ht =>
    simplexEdge_pos_left hD hE hE ht
  simp only [sub_self, zero_mul, add_zero]
  rw [intervalIntegral.integral_sub
      (ContinuousOn.log (by fun_prop) fun t ht => (hpos t ht).ne').intervalIntegrable
      intervalIntegrable_const,
    integral_log_affine hD (by linarith) (sub_ne_zero.2 (Ne.symm hDE)),
    intervalIntegral.integral_const]
  simp only [sub_zero, add_sub_cancel, smul_eq_mul, one_mul]

end Rep

end QED.ChainProof.SetCRegDisp

end
