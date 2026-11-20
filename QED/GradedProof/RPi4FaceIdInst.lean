/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdSumB
public import QED.GradedProof.RPi4FaceIdDirac
public import QED.GradedProof.RPi4WRem

/-!
# (R-Π₄) step L6d3: the class numerators satisfy the hypotheses of the merged-piece lemmas

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3.

* `faceId_lapF_vNum_VA`, `faceId_lapF_vNum_VC`: the class numerators of `VA` and `VC` are affine
  in `ℓ₁` (one fermion line carries `ℓ₁`), so their loop-`1` Laplacian vanishes;
* `faceId_isLoopPoly_bubTr`: the bubble trace has degree two;
* `faceId_half_lapF_VB_one`, `faceId_half_lapF_VB_zero`: the half Laplacians of the `VB` numerator
  are `A₀ + m² A₂` with `A₀` a trace quadratic in the face momentum and `A₂` constant.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.Bridge

variable (e mγ Λ m : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4)

theorem faceId_lapF_vNum_VA (ℓ : Fin 2 → Fin 4 → ℝ) :
    faceIdLapF 1 (fun ℓ => vNum e mγ Λ aVA baseVA cVA m k ℓ μ ν) ℓ = 0 := by
  unfold faceIdLapF
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun a _ => mul_eq_zero_of_right _ ?_)
  simp only [vNum, fm_VA, (faceId_add_E_one ℓ a).1, (faceId_add_E_one ℓ a).2,
    (faceId_sub_E_one ℓ a).1, (faceId_sub_E_one ℓ a).2, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun ρ _ => Finset.sum_eq_zero fun σ _ => ?_
  simp only [vT, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, faceId_eN_add, faceId_eN_sub,
    Matrix.mul_add,
    Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub]
  ring

theorem faceId_lapF_vNum_VC (ℓ : Fin 2 → Fin 4 → ℝ) :
    faceIdLapF 1 (fun ℓ => vNum e mγ Λ aVC baseVC cVC m k ℓ μ ν) ℓ = 0 := by
  unfold faceIdLapF
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun a _ => mul_eq_zero_of_right _ ?_)
  simp only [vNum, fm_VC, (faceId_add_E_one ℓ a).1, (faceId_add_E_one ℓ a).2,
    (faceId_sub_E_one ℓ a).1, (faceId_sub_E_one ℓ a).2, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun ρ _ => Finset.sum_eq_zero fun σ _ => ?_
  simp only [vT, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, faceId_eN_add, faceId_eN_sub,
    Matrix.mul_add,
    Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub]
  ring

/-- The bubble trace as a polynomial of degree two in the face momentum. -/
theorem faceId_isLoopPoly_bubTr (A B : Matrix (Fin 4) (Fin 4) ℂ) (M : ℝ) (c₁ c₂ : Bool)
    (k₁ k₂ : Fin 4 → ℝ) :
    IsLoopPoly 2 2 fun ℓ : Fin 2 → Fin 4 → ℝ =>
      bubTr A B M (zk k₁ c₁ (ℓ 0)) (zk k₂ c₂ (ℓ 0)) := by
  have h := ((((IsLoopPolyMat.const A).mul
    ((isLoopAffine_zk k₁ c₁).isLoopPolyMat_electronNumerator M)).mul
    (IsLoopPolyMat.const B)).mul
    ((isLoopAffine_zk k₂ c₂).isLoopPolyMat_electronNumerator M)).trace
  exact h.mono (by norm_num)

/-- **The half loop-`1` Laplacian of the `VB` numerator** at the face `ℓ = (x, 0)`. -/
theorem faceId_half_lapF_VB_one (x : Fin 4 → ℝ) :
    2⁻¹ * faceIdLapF 1 (fun ℓ => vNum e mγ Λ aVB baseVB cVB m k ℓ μ ν) ![x, 0] =
      faceIdKV e mγ Λ * bubTr (Dirac.gamma μ) (Dirac.gamma ν) 0 (zk k false x) (zk k true x) +
        (m : ℂ) ^ 2 * (faceIdKV e mγ Λ * (Dirac.gamma μ * Dirac.gamma ν).trace) := by
  rw [faceId_lapF_vNum_VB_one]
  have h : (Dirac.gamma μ * electronNumerator m x * Dirac.gamma ν *
      electronNumerator m (k + x)).trace = _ :=
    bubTr_eq (isOddG_gamma μ) (isOddG_gamma ν) m x (k + x)
  simp only [Matrix.cons_val_zero, zk, ite_true, Bool.false_eq_true, ite_false, h,
    bubTr_eq (isOddG_gamma μ) (isOddG_gamma ν) 0 x (k + x)]
  push_cast
  ring

/-- **The half loop-`0` Laplacian of the `VB` numerator** at the face `ℓ = (0, x)`. -/
theorem faceId_half_lapF_VB_zero (x : Fin 4 → ℝ) :
    2⁻¹ * faceIdLapF 0 (fun ℓ => vNum e mγ Λ aVB baseVB cVB m k ℓ μ ν) ![0, x] =
      faceIdKV e mγ Λ * bubTr (Dirac.gamma μ) (Dirac.gamma ν) 0 (zk (-k) true x)
          (zk k false x) +
        (m : ℂ) ^ 2 * (faceIdKV e mγ Λ * (Dirac.gamma μ * Dirac.gamma ν).trace) := by
  rw [faceId_lapF_vNum_VB_zero]
  have h : (Dirac.gamma μ * electronNumerator m (-k + x) * Dirac.gamma ν *
      electronNumerator m x).trace = _ :=
    bubTr_eq (isOddG_gamma μ) (isOddG_gamma ν) m (-k + x) x
  simp only [Matrix.cons_val_one]
  rw [sub_eq_neg_add]
  simp only [zk, ite_true, Bool.false_eq_true, ite_false,
    bubTr_eq (isOddG_gamma μ) (isOddG_gamma ν) 0 (-k + x) x]
  push_cast
  linear_combination faceIdKV e mγ Λ * h

end QED.GradedProof.RPi4

end
