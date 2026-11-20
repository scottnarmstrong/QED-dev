/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdBlock
public import QED.GradedProof.RPi4MassInsLim

/-!
# (R-Π₄) step L6d3: the face integrands as one-loop bubbles

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The face
integrands of the three classes at one flavour are one-loop integrands:

* `faceId_HA_eq`: `VA` is `-faceIdKV` times the inserted bubble of `F0` with `δ₂ = 1`,
  `δ_m = 4` (the self-energy insertion `-(ℓ̸ + 4M)` on the line `ℓ`);
* `faceId_HC_eq`: `VC` is `-faceIdKV` times the inserted bubble of `F1`;
* `faceId_bubTr_split`, `faceId_HB1_eq`, `faceId_HB0_eq`: each face of `VB` is `faceIdKV` times
  the bubble of `F1`, the loop-`0` face after the translation `x ↦ x + k`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.Bridge

variable (e mγ Λ M ε : ℝ) (k x : Fin 4 → ℝ) (μ ν : Fin 4)

/-- **The face integrand of `VA` is an inserted bubble of `F0`.** -/
theorem faceId_HA_eq :
    vNum e mγ Λ aVA baseVA cVA M k ![x, (1 / 2 : ℝ) • (x + (0 : ℝ) • k)] μ ν *
        ∏ l, faceIdG (faceIdRB baseVA ![1, 0] l) (faceIdV cVA ε k x l) ((M : ℂ) ^ 2) =
      -(faceIdKV e mγ Λ *
        insG (gAF true μ ν) (gBF true μ ν) 1 4 M ε (zk k true x) (zk k false x)) := by
  rw [zero_smul, add_zero, faceId_vNum_VA_half]
  simp (config := {decide := true}) only [Fin.prod_univ_four, faceIdRB, faceIdV,
    faceId_c_castSucc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, cVA, decide_true, decide_false,
    faceId_G_false, Fin.isValue, zero_smul, one_smul, zero_add]
  simp only [faceIdG, ite_true]
  simp only [insG, insTr, gAF, gBF, ite_true, zk, Bool.false_eq_true, ite_false,
    VP2.propDenom_eq_add M ε]
  have hc := Matrix.trace_mul_comm (Dirac.gamma ν * electronNumerator M (k + x))
    (Dirac.gamma μ * electronNumerator M x * QED.TwoLoop.Insertion.fermionCtMatrix 1 4 M x *
      electronNumerator M x)
  simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, Matrix.trace_neg] at hc ⊢
  rw [hc]
  ring

/-- **The face integrand of `VC` is an inserted bubble of `F1`.** -/
theorem faceId_HC_eq :
    vNum e mγ Λ aVC baseVC cVC M k ![x, (1 / 2 : ℝ) • (x + (1 : ℝ) • k)] μ ν *
        ∏ l, faceIdG (faceIdRB baseVC ![1, 0] l) (faceIdV cVC ε k x l) ((M : ℂ) ^ 2) =
      -(faceIdKV e mγ Λ *
        insG (gAF false μ ν) (gBF false μ ν) 1 4 M ε (zk k false x) (zk k true x)) := by
  rw [one_smul, add_comm x k, faceId_vNum_VC_half]
  simp (config := {decide := true}) only [Fin.prod_univ_four, faceIdRB, faceIdV,
    faceId_c_castSucc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, cVC, decide_true, decide_false,
    faceId_G_false, Fin.isValue, zero_smul, one_smul, zero_add]
  simp only [faceIdG, ite_true]
  simp only [insG, insTr, gAF, gBF, zk, Bool.false_eq_true, ite_false, ite_true,
    VP2.propDenom_eq_add M ε, Matrix.mul_neg, Matrix.neg_mul, Matrix.trace_neg]
  ring

/-- The two terms of the half Laplacian of `VB` recombine into the bubble trace at mass `M`. -/
theorem faceId_bubTr_split (y z : Fin 4 → ℝ) :
    faceIdKV e mγ Λ * bubTr (Dirac.gamma μ) (Dirac.gamma ν) 0 y z +
        (M : ℂ) ^ 2 * (faceIdKV e mγ Λ * (Dirac.gamma μ * Dirac.gamma ν).trace) =
      faceIdKV e mγ Λ * bubTr (gAF false μ ν) (gBF false μ ν) M y z := by
  simp only [gAF, gBF, Bool.false_eq_true, ite_false,
    bubTr_eq (isOddG_gamma μ) (isOddG_gamma ν)]
  push_cast
  ring

/-- **The loop-`1` face integrand of `VB` is a bubble of `F1`.** -/
theorem faceId_HB1_eq :
    (faceIdKV e mγ Λ * bubTr (Dirac.gamma μ) (Dirac.gamma ν) 0 (zk k false x) (zk k true x) +
        (M : ℂ) ^ 2 * (faceIdKV e mγ Λ * (Dirac.gamma μ * Dirac.gamma ν).trace)) *
        ∏ l, faceIdG (faceIdRB baseVB ![1, 0] l) (faceIdV cVB ε k x l) ((M : ℂ) ^ 2) =
      faceIdKV e mγ Λ * (bubTr (gAF false μ ν) (gBF false μ ν) M (zk k false x) (zk k true x) *
        (propDenom M ε (zk k false x))⁻¹ * (propDenom M ε (zk k true x))⁻¹) := by
  rw [faceId_bubTr_split]
  simp (config := {decide := true}) only [Fin.prod_univ_four, faceIdRB, faceIdV,
    faceId_c_castSucc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, cVB, decide_true, decide_false,
    faceId_G_false, Fin.isValue, zero_smul, one_smul, zero_add, mul_one]
  simp only [faceIdG, ite_true, zk, Bool.false_eq_true, ite_false, VP2.propDenom_eq_add M ε]
  ring

/-- **The loop-`0` face integrand of `VB`, translated by `k`, is the same bubble.** -/
theorem faceId_HB0_eq :
    (faceIdKV e mγ Λ * bubTr (Dirac.gamma μ) (Dirac.gamma ν) 0 (zk (-k) true (x + k))
          (zk k false (x + k)) +
        (M : ℂ) ^ 2 * (faceIdKV e mγ Λ * (Dirac.gamma μ * Dirac.gamma ν).trace)) *
        ∏ l, faceIdG (faceIdRB baseVB ![0, 1] l) (faceIdV cVB ε k (x + k) l) ((M : ℂ) ^ 2) =
      faceIdKV e mγ Λ * (bubTr (gAF false μ ν) (gBF false μ ν) M (zk k false x) (zk k true x) *
        (propDenom M ε (zk k false x))⁻¹ * (propDenom M ε (zk k true x))⁻¹) := by
  have h2 : x + k = k + x := add_comm x k
  rw [faceId_bubTr_split]
  simp (config := {decide := true}) only [Fin.prod_univ_four, faceIdRB, faceIdV,
    faceId_c_castSucc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, cVB, decide_true, decide_false,
    faceId_G_false, Fin.isValue, zero_smul, one_smul, zero_add, mul_one, one_mul, neg_smul]
  simp only [faceIdG, ite_true, zk, Bool.false_eq_true, ite_false, VP2.propDenom_eq_add M ε,
    h2, neg_add_cancel_left]
  ring

end QED.GradedProof.RPi4

end
