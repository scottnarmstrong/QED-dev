/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdPsiE

/-!
# (R-Π₄) step L6d3: the face integrals of the pieces of `VC`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. For the class
`VC` (loop-`1` self-energy faces, rest lines `0, 1, 3`) every piece of `faceIdTriPsi` is one
energy-first integral of the uniform form of `QED.GradedProof.RPi4.faceId_tri_g`: numerator at
the face midpoint times the line factors `faceIdG` of the rest lines and `faceIdW` of the
duplicated lines. The pieces duplicating the block line `2` vanish (their loop-`1` Laplacian is
`0`, hypothesis `hL`).

* `faceId_psiA_VC`, `faceId_psiB_VC`, `faceId_psiP_VC`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.Bridge

variable (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
  (k : Fin 4 → ℝ) (μ ν : Fin 4) (M X Y ε : ℝ)

/-- **The pieces with eight lines of `VC`.** -/
theorem faceId_psiA_VC (hL : ∀ m ℓ, faceIdLapF 1 (fun ℓ => Num m k ℓ μ ν) ℓ = 0)
    (i j : Fin 4) (hij : i ≤ j) :
    faceIdPsi baseVC cVC (shA i j) (fun ℓ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * Num M k ℓ μ ν)
      ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2, mA M X Y i j 3, X, Y, 0] 1 k ε =
    QED.OneLoop.energyFirstIntegral fun x => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * Num M k ![x, (1 / 2 : ℝ) • (x + (1 : ℝ) • k)] μ ν *
      ((∏ l : Fin 4, faceIdG (faceIdRB baseVC ![1, 0] l) (faceIdV cVC ε k x l)
          (if l ≤ i then (M : ℂ) ^ 2 else if l ≤ j then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2)) *
        faceIdW (faceIdRB baseVC ![1, 0] i) (faceIdV cVC ε k x i) ((X : ℂ) ^ 2) *
        faceIdW (faceIdRB baseVC ![1, 0] j) (faceIdV cVC ε k x j) ((Y : ℂ) ^ 2)) := by
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hij ⊢
  all_goals first
    | exact absurd hij (by decide)
    | (rw [faceId_psi_se _ _ _ _ _ _ _ _ (by decide) (by decide)]
       congr 1
       funext x
       simp (config := {decide := true}) only [faceId_shA_castSucc, Fin.prod_univ_succ,
         Fin.prod_univ_zero, mA, faceIdRB, faceIdV, faceId_c_castSucc,
         Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two,
         Matrix.cons_val_three, Matrix.head_cons, cVC, ite_true, ite_false, decide_true,
         decide_false, faceId_G_false, faceId_W_true,
         faceId_inv_propDenom_eq_G, Fin.isValue, mul_one, one_mul, Matrix.tail_cons, zero_smul,
         one_smul, zero_add]
       ring)
    | (rw [faceId_psi_vtx1 _ _ _ _ _ _ _ _ (by decide) (by decide)]
       congr 1
       funext x
       rw [faceId_lapF_const_mul, hL]
       simp (config := {decide := true}) only [faceIdRB, faceId_W_false, Fin.isValue, mul_zero,
         decide_true, decide_false, zero_mul])
    | (rw [faceId_psi_zero _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)]
       simp (config := {decide := true}) only [faceIdRB, faceId_W_false, Fin.isValue, mul_zero,
         decide_false, faceId_efi_zero])

/-- **The pieces with seven lines of `VC`.** -/
theorem faceId_psiB_VC (hL : ∀ m ℓ, faceIdLapF 1 (fun ℓ => Num m k ℓ μ ν) ℓ = 0) (i : Fin 4) :
    faceIdPsi baseVC cVC (shB i) (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        (Num X k ℓ μ ν - Num M k ℓ μ ν))
      ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, 0] 1 k ε =
    QED.OneLoop.energyFirstIntegral fun x => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        (Num X k ![x, (1 / 2 : ℝ) • (x + (1 : ℝ) • k)] μ ν -
          Num M k ![x, (1 / 2 : ℝ) • (x + (1 : ℝ) • k)] μ ν) *
      ((∏ l : Fin 4, faceIdG (faceIdRB baseVC ![1, 0] l) (faceIdV cVC ε k x l)
          (if l ≤ i then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2)) *
        faceIdW (faceIdRB baseVC ![1, 0] i) (faceIdV cVC ε k x i) ((Y : ℂ) ^ 2)) := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  all_goals first
    | (rw [faceId_psi_se _ _ _ _ _ _ _ _ (by decide) (by decide)]
       congr 1
       funext x
       simp (config := {decide := true}) only [faceId_shB_castSucc, Fin.prod_univ_succ,
         Fin.prod_univ_zero, mB, faceIdRB, faceIdV, faceId_c_castSucc,
         Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two,
         Matrix.cons_val_three, Matrix.head_cons, cVC, ite_true, ite_false, decide_true,
         decide_false, faceId_G_false, faceId_W_true,
         faceId_inv_propDenom_eq_G, Fin.isValue, mul_one, one_mul, Matrix.tail_cons, zero_smul,
         one_smul, zero_add]
       ring)
    | (rw [faceId_psi_vtx1 _ _ _ _ _ _ _ _ (by decide) (by decide)]
       congr 1
       funext x
       rw [faceId_lapF_const_mul, faceId_lapF_sub, hL, hL]
       simp (config := {decide := true}) only [faceIdRB, faceId_W_false, Fin.isValue, mul_zero,
         decide_false, zero_mul, sub_zero])

/-- **The padded piece of `VC`.** -/
theorem faceId_psiP_VC (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) :
    faceIdPsi baseVC cVC (shB 0) (fun ℓ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 k μ ν * propDenom Y 0 (fm baseVC (ppc cVC k) 0 ℓ))
      ![Y, Y, Y, Y, Y, 0] 1 k ε =
    QED.OneLoop.energyFirstIntegral fun x => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 k μ ν * propDenom Y 0 x *
      ((∏ l : Fin 4, faceIdG (faceIdRB baseVC ![1, 0] l) (faceIdV cVC ε k x l) ((Y : ℂ) ^ 2)) *
        faceIdW (faceIdRB baseVC ![1, 0] 0) (faceIdV cVC ε k x 0) ((Y : ℂ) ^ 2)) := by
  rw [faceId_psi_se _ _ _ _ _ _ _ _ (by decide) (by decide)]
  congr 1
  funext x
  rw [fm_VC]
  simp (config := {decide := true}) only [faceId_shB_castSucc, Fin.prod_univ_succ,
    Fin.prod_univ_zero, faceIdRB, faceIdV, faceId_c_castSucc,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, cVC, ite_true, ite_false, decide_true,
    decide_false, faceId_G_false, faceId_W_true,
    faceId_inv_propDenom_eq_G, Fin.isValue, mul_one, one_mul, Matrix.tail_cons, zero_smul,
    one_smul, zero_add]
  ring

end QED.GradedProof.RPi4

end
