/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SymanzikIntegrabilityRefined

/-!
# (R-Π₄) step L10, `MajDRay`: the pairing of two numerator lines

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. A contraction
of two numerator lines `e`, `f` in `coeffTwo`, `coeffThree` costs
`α_eᵀ A⁻¹ α_f = P_{ef}/U` with `P_{ef} = ∑_t z_t det(α_e, α_t) det(α_f, α_t)` (the adjugate
`adj A = ∑ₜ zₜ (J αₜ)(J αₜ)ᵀ`): only lines `t` parallel to neither `e` nor `f` contribute. This
is the sharp count behind the merged pieces' power counting (a single numerator line of a
one-loop subgraph pairs only with lines outside it, at cost `O(1)`), the input of the weights
of `QED.GradedProof.RPi4.faceIdRayAP_integrableOn_wt`.

* `majDPRLinePair`, `majDPR_linePair_eq_adjugate`, `majDPR_linePair_div_symanzikU`;
* **`majDPR_abs_pairing_le`**: `|α_eᵀA⁻¹α_f| ≤ ∑ⱼ zⱼ |det(α_e, αⱼ)| |det(α_f, αⱼ)| / U`.
-/

@[expose] public section

open Matrix

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop

variable {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)

/-! ### The line pairings -/

/-- `P_{ef}(z) = ∑ⱼ zⱼ det(α_e, αⱼ) det(α_f, αⱼ)`, so that `P_{ef}/U = α_eᵀ A⁻¹ α_f`
(`majDPR_linePair_div_symanzikU`); `P_{ee} = Q_e` is `lineQuad`. -/
def majDPRLinePair (e f : Fin (m + 1)) (z : Fin (m + 1) → ℝ) : ℝ :=
  ∑ j, z j * (pairDet α e j * pairDet α f j)

theorem majDPR_linePair_eq_adjugate (e f : Fin (m + 1)) (z : Fin (m + 1) → ℝ) :
    majDPRLinePair α e f z = α e ⬝ᵥ (Matrix.adjugate (symanzikMatrix α z) *ᵥ α f) := by
  simp only [majDPRLinePair, pairDet, Matrix.adjugate_fin_two, dotProduct, Matrix.mulVec,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, symanzikMatrix]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The pairing of two lines**: `α_eᵀ A⁻¹ α_f = P_{ef}/U`. -/
theorem majDPR_linePair_div_symanzikU (e f : Fin (m + 1)) (z : Fin (m + 1) → ℝ) :
    majDPRLinePair α e f z / symanzikU α z =
      α e ⬝ᵥ ((symanzikMatrix α z)⁻¹ *ᵥ α f) := by
  rw [majDPR_linePair_eq_adjugate, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, div_eq_inv_mul]
  rfl

/-- `|α_eᵀ A⁻¹ α_f| ≤ ∑ⱼ zⱼ |det(α_e, αⱼ)| |det(α_f, αⱼ)| / U` for `z ≥ 0`, `U > 0`: only the
lines `j` parallel to neither `e` nor `f` contribute. -/
theorem majDPR_abs_pairing_le (e f : Fin (m + 1)) {z : Fin (m + 1) → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hU : 0 < symanzikU α z) :
    |α e ⬝ᵥ ((symanzikMatrix α z)⁻¹ *ᵥ α f)| ≤
      (∑ j, z j * (|pairDet α e j| * |pairDet α f j|)) / symanzikU α z := by
  rw [← majDPR_linePair_div_symanzikU, abs_div, abs_of_pos hU]
  refine div_le_div_of_nonneg_right ?_ hU.le
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  rw [abs_mul, abs_mul, abs_of_nonneg (hz j)]

end QED.GradedProof.RPi4

end
