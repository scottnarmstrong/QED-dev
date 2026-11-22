/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FacePerm

/-!
# Set (a), stage B3: homogeneity of the collapsed integrand in the Feynman parameters

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B3 (the nested
form). Scaling all Feynman parameters by `t > 0` scales the Symanzik matrix `A` by `t`, `U` by
`t²` and `V` by `t`, and leaves the loop shift unchanged; the moment functional `Ê₅` is
homogeneous of degree `-2` in `(A, W)`. So the five-moment collapsed integrand is homogeneous of
degree `-5`:

* **`ksN_pieceF_smul`**: `pieceF 5 Q α p M γ u (t • z) = (t⁵)⁻¹ * pieceF 5 Q α p M γ u z`.

This is the hypothesis of the Cheng–Wu theorem `QED.Integration.ChengWu.integral_simplex_chengWu`.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.GradedProof.RPi4
open QED.GradedProof.WI2 (ehat)

variable {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) (z : Fin (m + 1) → ℝ) {t : ℝ}

theorem ksN_symanzikMatrix_smul (t : ℝ) : symanzikMatrix α (t • z) = t • symanzikMatrix α z := by
  ext s r
  simp only [symanzikMatrix, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem ksN_symanzikU_smul (t : ℝ) : symanzikU α (t • z) = t ^ 2 * symanzikU α z := by
  rw [symanzikU, ksN_symanzikMatrix_smul, Matrix.det_smul, Fintype.card_fin, symanzikU]

theorem ksN_inv_smul (ht : t ≠ 0) (A : Matrix (Fin 2) (Fin 2) ℝ) : (t • A)⁻¹ = t⁻¹ • A⁻¹ := by
  by_cases hA : IsUnit A.det
  · have h := Matrix.inv_smul' A (Units.mk0 t ht) hA
    rwa [Units.smul_def, Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0] at h
  · have hA' : ¬ IsUnit (t • A).det := by
      rw [Matrix.det_smul, isUnit_iff_ne_zero, Fintype.card_fin]
      rw [isUnit_iff_ne_zero, not_not] at hA
      simp [hA]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hA, Matrix.nonsing_inv_apply_not_isUnit _ hA',
      smul_zero]

theorem ksN_coefVec_smul (t : ℝ) (q : Fin (m + 1) → ℝ) :
    coefVec α (t • z) q = t • coefVec α z q := by
  funext s
  simp only [coefVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem ksN_symanzikVector_smul (t : ℝ) :
    symanzikVector α p (t • z) = t • symanzikVector α p z := by
  funext s μ
  simp only [symanzikVector, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem ksN_inv_mulVec_smul (ht : t ≠ 0) (q : Fin (m + 1) → ℝ) :
    (symanzikMatrix α (t • z))⁻¹.mulVec (coefVec α (t • z) q) =
      (symanzikMatrix α z)⁻¹.mulVec (coefVec α z q) := by
  rw [ksN_symanzikMatrix_smul, ksN_inv_smul ht, ksN_coefVec_smul, Matrix.smul_mulVec,
    Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ ht, one_smul]

theorem ksN_loopShift_smul (ht : t ≠ 0) : loopShift α p (t • z) = loopShift α p z := by
  have h := ksN_inv_mulVec_smul α z ht
  have hs : spatialShift α p (t • z) = spatialShift α p z := by
    funext s c
    simp only [spatialShift, h]
  simp only [loopShift, energyShift, h, hs]

theorem ksN_dot_smul (t : ℝ) (a b : Fin 4 → ℝ) :
    Minkowski.dot (t • a) (t • b) = t ^ 2 * Minkowski.dot a b := by
  simp only [Minkowski.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem ksN_symanzikV_smul (ht : t ≠ 0) :
    symanzikV α p M (t • z) = t * symanzikV α p M z := by
  simp only [symanzikV, ksN_symanzikMatrix_smul, ksN_inv_smul ht, ksN_symanzikVector_smul,
    Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, ksN_dot_smul, mul_sub, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun _ _ => by ring
  · refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    field_simp

theorem ksN_loopMetricInv_smul (ht : t ≠ 0) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    loopMetricInv (t • A) = t⁻¹ • loopMetricInv A := by
  ext a b
  simp only [loopMetricInv, ksN_inv_smul ht, Matrix.smul_apply, smul_eq_mul]
  ring

theorem ksN_contractTwo_smul (ht : t ≠ 0) (Q : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (X : LoopIndex → ℂ) : Q.contractTwo (t • A) X = (t : ℂ)⁻¹ * Q.contractTwo A X := by
  simp only [LoopQuartic.contractTwo, ksN_loopMetricInv_smul ht, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  push_cast
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem ksN_contractFour_smul (ht : t ≠ 0) (Q : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Q.contractFour (t • A) = ((t : ℂ) ^ 2)⁻¹ * Q.contractFour A := by
  simp only [LoopQuartic.contractFour, ksN_loopMetricInv_smul ht, matPair, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- **`Ê₅` is homogeneous of degree `-2` in `(A, W)`.** -/
theorem ksN_ehat_five_smul (ht : t ≠ 0) (Q : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (X : LoopIndex → ℂ) (W : ℂ) :
    ehat 5 Q (t • A) X ((t : ℂ) * W) = ((t : ℂ) ^ 2)⁻¹ * ehat 5 Q A X W := by
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht
  simp only [ehat, ksN_contractTwo_smul ht, ksN_contractFour_smul ht]
  norm_num
  rw [mul_pow, mul_inv]
  ring

/-- **The collapsed integrand of `Ê₅` is homogeneous of degree `-5`.** -/
theorem ksN_pieceF_smul (ht : t ≠ 0) (Q : LoopQuartic) (γ : Fin (m + 1)) (u : ℝ) :
    pieceF 5 Q α p M γ u (t • z) = ((t : ℂ) ^ 5)⁻¹ * pieceF 5 Q α p M γ u z := by
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht
  have hW : symanzikV α p M (t • z) + (t • z) γ * u = t * (symanzikV α p M z + z γ * u) := by
    rw [ksN_symanzikV_smul α p M z ht, Pi.smul_apply, smul_eq_mul]
    ring
  rw [pieceF, pieceF, hW]
  simp only [paramAtV, ksN_symanzikU_smul, ksN_symanzikMatrix_smul,
    ksN_loopShift_smul α p z ht, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [ksN_ehat_five_smul ht]
  field_simp

end QED.ChainProof.SetAKS

end
