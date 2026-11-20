/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdPsiE

/-!
# (R-Π₄) step L6d3: the face integrals of the pieces of `VB`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. For the class
`VB` (vertex faces only: loop `1` with rest lines `0, 3`, loop `0` with rest lines `1, 2`) every
piece of `faceIdTriPsi` is the sum of two energy-first integrals of the uniform form of
`QED.GradedProof.RPi4.faceId_tri_g`, one per face, with the half Laplacian of the numerator; the
padded piece vanishes (its numerator does not depend on `ℓ₁`).

* `faceId_psiA_VB`, `faceId_psiB_VB`, `faceId_psiP_VB`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.Bridge

variable (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
  (k : Fin 4 → ℝ) (μ ν : Fin 4) (M X Y ε : ℝ)

/-- **The pieces with eight lines of `VB`.** -/
theorem faceId_psiA_VB (i j : Fin 4) (hij : i ≤ j) :
    faceIdPsi baseVB cVB (shA i j) (fun ℓ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * Num M k ℓ μ ν)
      ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2, mA M X Y i j 3, X, Y, 0] 0 k ε =
    (QED.OneLoop.energyFirstIntegral fun x => 2⁻¹ * faceIdLapF 1 (fun ℓ =>
        ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * Num M k ℓ μ ν) ![x, 0] *
      ((∏ l : Fin 4, faceIdG (faceIdRB baseVB ![1, 0] l) (faceIdV cVB ε k x l)
          (if l ≤ i then (M : ℂ) ^ 2 else if l ≤ j then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2)) *
        faceIdW (faceIdRB baseVB ![1, 0] i) (faceIdV cVB ε k x i) ((X : ℂ) ^ 2) *
        faceIdW (faceIdRB baseVB ![1, 0] j) (faceIdV cVB ε k x j) ((Y : ℂ) ^ 2))) +
    QED.OneLoop.energyFirstIntegral fun x => 2⁻¹ * faceIdLapF 0 (fun ℓ =>
        ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * Num M k ℓ μ ν) ![0, x] *
      ((∏ l : Fin 4, faceIdG (faceIdRB baseVB ![0, 1] l) (faceIdV cVB ε k x l)
          (if l ≤ i then (M : ℂ) ^ 2 else if l ≤ j then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2)) *
        faceIdW (faceIdRB baseVB ![0, 1] i) (faceIdV cVB ε k x i) ((X : ℂ) ^ 2) *
        faceIdW (faceIdRB baseVB ![0, 1] j) (faceIdV cVB ε k x j) ((Y : ℂ) ^ 2)) := by
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hij ⊢
  all_goals first
    | exact absurd hij (by decide)
    | (rw [faceId_psi_vtx1 _ _ _ _ _ _ _ _ (by decide) (by decide)]
       simp (config := {decide := true}) only [faceId_shA_castSucc, Fin.prod_univ_succ,
         Fin.prod_univ_zero, mA, faceIdRB, faceIdV, faceId_c_castSucc,
         Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two,
         Matrix.cons_val_three, Matrix.head_cons, cVB, ite_true, ite_false, decide_true,
         decide_false, faceId_G_false, faceId_W_true, faceId_W_false, mul_zero, faceId_efi_zero,
         add_zero, faceId_inv_propDenom_eq_G, Fin.isValue, mul_one, one_mul, Matrix.tail_cons,
         zero_smul, one_smul, zero_add]
       congr 1
       funext x
       ring)
    | (rw [faceId_psi_vtx0 _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)]
       simp (config := {decide := true}) only [faceId_shA_castSucc, Fin.prod_univ_succ,
         Fin.prod_univ_zero, mA, faceIdRB, faceIdV, faceId_c_castSucc,
         Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two,
         Matrix.cons_val_three, Matrix.head_cons, cVB, ite_true, ite_false, decide_true,
         decide_false, faceId_G_false, faceId_W_true, faceId_W_false, mul_zero, faceId_efi_zero,
         zero_add, faceId_inv_propDenom_eq_G, Fin.isValue, mul_one, one_mul, Matrix.tail_cons,
         zero_smul, one_smul, neg_smul]
       congr 1
       funext x
       ring)
    | (rw [faceId_psi_zero _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)]
       simp (config := {decide := true}) only [faceIdRB, faceId_W_false, Fin.isValue, mul_zero,
         decide_true, decide_false, faceId_efi_zero, add_zero, zero_mul])

/-- **The pieces with seven lines of `VB`.** -/
theorem faceId_psiB_VB (i : Fin 4) :
    faceIdPsi baseVB cVB (shB i) (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        (Num X k ℓ μ ν - Num M k ℓ μ ν))
      ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, 0] 0 k ε =
    (QED.OneLoop.energyFirstIntegral fun x => 2⁻¹ * faceIdLapF 1 (fun ℓ =>
        -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν)) ![x, 0] *
      ((∏ l : Fin 4, faceIdG (faceIdRB baseVB ![1, 0] l) (faceIdV cVB ε k x l)
          (if l ≤ i then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2)) *
        faceIdW (faceIdRB baseVB ![1, 0] i) (faceIdV cVB ε k x i) ((Y : ℂ) ^ 2))) +
    QED.OneLoop.energyFirstIntegral fun x => 2⁻¹ * faceIdLapF 0 (fun ℓ =>
        -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν)) ![0, x] *
      ((∏ l : Fin 4, faceIdG (faceIdRB baseVB ![0, 1] l) (faceIdV cVB ε k x l)
          (if l ≤ i then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2)) *
        faceIdW (faceIdRB baseVB ![0, 1] i) (faceIdV cVB ε k x i) ((Y : ℂ) ^ 2)) := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  all_goals first
    | (rw [faceId_psi_vtx1 _ _ _ _ _ _ _ _ (by decide) (by decide)]
       simp (config := {decide := true}) only [faceId_shB_castSucc, Fin.prod_univ_succ,
         Fin.prod_univ_zero, mB, faceIdRB, faceIdV, faceId_c_castSucc,
         Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two,
         Matrix.cons_val_three, Matrix.head_cons, cVB, ite_true, ite_false, decide_true,
         decide_false, faceId_G_false, faceId_W_true, faceId_W_false, mul_zero, faceId_efi_zero,
         add_zero, faceId_inv_propDenom_eq_G, Fin.isValue, mul_one, one_mul, Matrix.tail_cons,
         zero_smul, one_smul, zero_add]
       congr 1
       funext x
       ring)
    | (rw [faceId_psi_vtx0 _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)]
       simp (config := {decide := true}) only [faceId_shB_castSucc, Fin.prod_univ_succ,
         Fin.prod_univ_zero, mB, faceIdRB, faceIdV, faceId_c_castSucc,
         Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two,
         Matrix.cons_val_three, Matrix.head_cons, cVB, ite_true, ite_false, decide_true,
         decide_false, faceId_G_false, faceId_W_true, faceId_W_false, mul_zero, faceId_efi_zero,
         zero_add, faceId_inv_propDenom_eq_G, Fin.isValue, mul_one, one_mul, Matrix.tail_cons,
         zero_smul, one_smul, neg_smul]
       congr 1
       funext x
       ring)

/-- **The padded piece of `VB` vanishes.** -/
theorem faceId_psiP_VB (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) :
    faceIdPsi baseVB cVB (shB 0) (fun ℓ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 k μ ν * propDenom Y 0 (fm baseVB (ppc cVB k) 0 ℓ))
      ![Y, Y, Y, Y, Y, 0] 0 k ε = 0 := by
  rw [faceId_psi_vtx1 _ _ _ _ _ _ _ _ (by decide) (by decide)]
  have h : ∀ x : Fin 4 → ℝ, faceIdLapF 1 (fun ℓ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 k μ ν * propDenom Y 0 (fm baseVB (ppc cVB k) 0 ℓ))
      ![x, 0] = 0 := fun x =>
    faceId_lapF_eq_zero _ _ _ fun a => by
      simp only [fm_VB, Matrix.cons_val_zero, (faceId_add_E_one _ a).1,
        (faceId_sub_E_one _ a).1, and_self]
  simp only [h, mul_zero, zero_mul, faceId_efi_zero]

end QED.GradedProof.RPi4

end
