/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdPsiE

/-!
# (R-Π₄) step L6d3: integrability of the face integrands of the pieces

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The face
integrands of the pieces in the uniform form of `QED.GradedProof.RPi4.faceId_tri_g`
(`faceIdFA`, `faceIdFB`, `faceIdFP`: numerator times the line factors of the rest lines and of the
duplicated lines) are integrable in both stages (`EF`) at `ε > 0`, for every face of the three
classes, with the numerator degrees of the faces (`4` resp. `2` over five resp. four lines for
the self-energy faces, `2` resp. `0` over four resp. three lines for the vertex faces).

* `faceIdFA`, `faceIdFB`, `faceIdFP`;
* `faceId_efA_VA`, `faceId_efB_VA`, `faceId_efP_VA`, the same for `VC`, and
  `faceId_efA_VB1`, `faceId_efB_VB1`, `faceId_efA_VB0`, `faceId_efB_VB0`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.Bridge

/-- The face integrand of a piece with eight lines in the uniform form. -/
noncomputable def faceIdFA (b : Fin 4 → Bool) (c : Fin 5 → ℝ) (ε : ℝ) (k : Fin 4 → ℝ)
    (n : (Fin 4 → ℝ) → ℂ) (M X Y : ℝ) (i j : Fin 4) (x : Fin 4 → ℝ) : ℂ :=
  n x * ((∏ l : Fin 4, faceIdG (b l) (faceIdV c ε k x l)
      (if l ≤ i then (M : ℂ) ^ 2 else if l ≤ j then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2)) *
    faceIdW (b i) (faceIdV c ε k x i) ((X : ℂ) ^ 2) *
      faceIdW (b j) (faceIdV c ε k x j) ((Y : ℂ) ^ 2))

/-- The face integrand of a piece with seven lines in the uniform form. -/
noncomputable def faceIdFB (b : Fin 4 → Bool) (c : Fin 5 → ℝ) (ε : ℝ) (k : Fin 4 → ℝ)
    (n : (Fin 4 → ℝ) → ℂ) (X Y : ℝ) (i : Fin 4) (x : Fin 4 → ℝ) : ℂ :=
  n x * ((∏ l : Fin 4, faceIdG (b l) (faceIdV c ε k x l)
      (if l ≤ i then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2)) *
    faceIdW (b i) (faceIdV c ε k x i) ((Y : ℂ) ^ 2))

/-- The face integrand of the padded piece in the uniform form. -/
noncomputable def faceIdFP (b : Fin 4 → Bool) (c : Fin 5 → ℝ) (ε : ℝ) (k : Fin 4 → ℝ)
    (n : (Fin 4 → ℝ) → ℂ) (Y : ℝ) (x : Fin 4 → ℝ) : ℂ :=
  n x * ((∏ l : Fin 4, faceIdG (b l) (faceIdV c ε k x l) ((Y : ℂ) ^ 2)) *
    faceIdW (b 0) (faceIdV c ε k x 0) ((Y : ℂ) ^ 2))

variable {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) (M X Y : ℝ)
include hε

theorem faceId_efA_VA (n : (Fin 4 → ℝ) → ℂ) (hn : IsLoopPoly 2 4 fun ℓ => n (ℓ 0))
    (i j : Fin 4) (hij : i ≤ j) :
    EF (faceIdFA (faceIdRB baseVA ![1, 0]) cVA ε k n M X Y i j) := by
  by_cases hb : faceIdRB baseVA ![1, 0] i = true ∧ faceIdRB baseVA ![1, 0] j = true
  · refine (ef5 k hε n hn (mA M X Y i j 0) (mA M X Y i j 2) (mA M X Y i j 3) X Y false false
      true (decide (i = 3)) (decide (j = 3))).congr fun x => ?_
    fin_cases i <;> fin_cases j <;> first
      | exact absurd hij (by decide)
      | exact absurd hb (by decide)
      | (simp (config := {decide := true}) only [faceIdFA, Fin.prod_univ_four, mA, faceIdRB,
          faceIdV, faceId_c_castSucc, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, cVA,
          ite_true, ite_false, decide_true, decide_false, faceId_G_false, faceId_W_true,
          faceId_inv_propDenom_eq_G, Fin.isValue, mul_one, zero_smul, one_smul,
          zero_add, zk, Fin.zero_eta, Fin.reduceFinMk])
  · refine EF.zero.congr fun x => ?_
    simp only [faceIdFA]
    cases hi : faceIdRB baseVA ![1, 0] i <;> cases hj : faceIdRB baseVA ![1, 0] j <;>
      simp_all [faceId_W_false]

theorem faceId_efB_VA (n : (Fin 4 → ℝ) → ℂ) (hn : IsLoopPoly 2 2 fun ℓ => n (ℓ 0))
    (i : Fin 4) : EF (faceIdFB (faceIdRB baseVA ![1, 0]) cVA ε k n X Y i) := by
  by_cases hb : faceIdRB baseVA ![1, 0] i = true
  · refine (ef4 k hε n hn (mB X Y i 0) (mB X Y i 2) (mB X Y i 3) Y false false true
      (decide (i = 3))).congr fun x => ?_
    fin_cases i <;> first
      | exact absurd hb (by decide)
      | (simp (config := {decide := true}) only [faceIdFB, Fin.prod_univ_four, mB, faceIdRB,
          faceIdV, faceId_c_castSucc, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, cVA,
          ite_true, ite_false, decide_true, decide_false, faceId_G_false, faceId_W_true,
          faceId_inv_propDenom_eq_G, Fin.isValue, mul_one, zero_smul, one_smul,
          zero_add, zk, Fin.zero_eta, Fin.reduceFinMk])
  · refine EF.zero.congr fun x => ?_
    simp only [faceIdFB]
    cases hi : faceIdRB baseVA ![1, 0] i <;> simp_all [faceId_W_false]

theorem faceId_efP_VA (n : (Fin 4 → ℝ) → ℂ) (hn : IsLoopPoly 2 2 fun ℓ => n (ℓ 0)) :
    EF (faceIdFP (faceIdRB baseVA ![1, 0]) cVA ε k n Y) := by
  refine (ef4 k hε n hn Y Y Y Y false false true false).congr fun x => ?_
  simp (config := {decide := true}) only [faceIdFP, Fin.prod_univ_four, faceIdRB,
    faceIdV, faceId_c_castSucc, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, cVA,
    ite_true, ite_false, decide_true, decide_false, faceId_G_false, faceId_W_true,
    faceId_inv_propDenom_eq_G, Fin.isValue, mul_one, zero_smul, one_smul,
    zero_add, zk]

theorem faceId_efA_VC (n : (Fin 4 → ℝ) → ℂ) (hn : IsLoopPoly 2 4 fun ℓ => n (ℓ 0))
    (i j : Fin 4) (hij : i ≤ j) :
    EF (faceIdFA (faceIdRB baseVC ![1, 0]) cVC ε k n M X Y i j) := by
  by_cases hb : faceIdRB baseVC ![1, 0] i = true ∧ faceIdRB baseVC ![1, 0] j = true
  · refine (ef5 k hε n hn (mA M X Y i j 0) (mA M X Y i j 1) (mA M X Y i j 3) X Y false true
      true (decide (i ≠ 0)) (decide (j ≠ 0))).congr fun x => ?_
    fin_cases i <;> fin_cases j <;> first
      | exact absurd hij (by decide)
      | exact absurd hb (by decide)
      | (simp (config := {decide := true}) only [faceIdFA, Fin.prod_univ_four, mA, faceIdRB,
          faceIdV, faceId_c_castSucc, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, cVC,
          ite_true, ite_false, decide_true, decide_false, faceId_G_false, faceId_W_true,
          faceId_inv_propDenom_eq_G, Fin.isValue, mul_one, zero_smul, one_smul,
          zero_add, zk, Fin.zero_eta, Fin.reduceFinMk])
  · refine EF.zero.congr fun x => ?_
    simp only [faceIdFA]
    cases hi : faceIdRB baseVC ![1, 0] i <;> cases hj : faceIdRB baseVC ![1, 0] j <;>
      simp_all [faceId_W_false]

theorem faceId_efB_VC (n : (Fin 4 → ℝ) → ℂ) (hn : IsLoopPoly 2 2 fun ℓ => n (ℓ 0))
    (i : Fin 4) : EF (faceIdFB (faceIdRB baseVC ![1, 0]) cVC ε k n X Y i) := by
  by_cases hb : faceIdRB baseVC ![1, 0] i = true
  · refine (ef4 k hε n hn (mB X Y i 0) (mB X Y i 1) (mB X Y i 3) Y false true true
      (decide (i ≠ 0))).congr fun x => ?_
    fin_cases i <;> first
      | exact absurd hb (by decide)
      | (simp (config := {decide := true}) only [faceIdFB, Fin.prod_univ_four, mB, faceIdRB,
          faceIdV, faceId_c_castSucc, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, cVC,
          ite_true, ite_false, decide_true, decide_false, faceId_G_false, faceId_W_true,
          faceId_inv_propDenom_eq_G, Fin.isValue, mul_one, zero_smul, one_smul,
          zero_add, zk, Fin.zero_eta, Fin.reduceFinMk])
  · refine EF.zero.congr fun x => ?_
    simp only [faceIdFB]
    cases hi : faceIdRB baseVC ![1, 0] i <;> simp_all [faceId_W_false]

theorem faceId_efP_VC (n : (Fin 4 → ℝ) → ℂ) (hn : IsLoopPoly 2 2 fun ℓ => n (ℓ 0)) :
    EF (faceIdFP (faceIdRB baseVC ![1, 0]) cVC ε k n Y) := by
  refine (ef4 k hε n hn Y Y Y Y false true true false).congr fun x => ?_
  simp (config := {decide := true}) only [faceIdFP, Fin.prod_univ_four, faceIdRB,
    faceIdV, faceId_c_castSucc, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, cVC,
    ite_true, ite_false, decide_true, decide_false, faceId_G_false, faceId_W_true,
    faceId_inv_propDenom_eq_G, Fin.isValue, mul_one, zero_smul, one_smul,
    zero_add, zk]

theorem faceId_efA_VB1 (n : (Fin 4 → ℝ) → ℂ) (hn : IsLoopPoly 2 2 fun ℓ => n (ℓ 0))
    (i j : Fin 4) (hij : i ≤ j) :
    EF (faceIdFA (faceIdRB baseVB ![1, 0]) cVB ε k n M X Y i j) := by
  by_cases hb : faceIdRB baseVB ![1, 0] i = true ∧ faceIdRB baseVB ![1, 0] j = true
  · refine (ef4 k hε n hn (mA M X Y i j 0) (mA M X Y i j 3) X Y false true
      (decide (i = 3)) (decide (j = 3))).congr fun x => ?_
    fin_cases i <;> fin_cases j <;> first
      | exact absurd hij (by decide)
      | exact absurd hb (by decide)
      | (simp (config := {decide := true}) only [faceIdFA, Fin.prod_univ_four, mA, faceIdRB,
          faceIdV, faceId_c_castSucc, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, cVB,
          ite_true, ite_false, decide_true, decide_false, faceId_G_false, faceId_W_true,
          faceId_inv_propDenom_eq_G, Fin.isValue, mul_one, zero_smul, one_smul,
          zero_add, zk, Fin.zero_eta, Fin.reduceFinMk])
  · refine EF.zero.congr fun x => ?_
    simp only [faceIdFA]
    cases hi : faceIdRB baseVB ![1, 0] i <;> cases hj : faceIdRB baseVB ![1, 0] j <;>
      simp_all [faceId_W_false]

theorem faceId_efB_VB1 (n : (Fin 4 → ℝ) → ℂ) (hn : IsLoopPoly 2 0 fun ℓ => n (ℓ 0))
    (i : Fin 4) : EF (faceIdFB (faceIdRB baseVB ![1, 0]) cVB ε k n X Y i) := by
  by_cases hb : faceIdRB baseVB ![1, 0] i = true
  · refine (ef3 k hε n hn (mB X Y i 0) (mB X Y i 3) Y false true (decide (i = 3))).congr fun x => ?_
    fin_cases i <;> first
      | exact absurd hb (by decide)
      | (simp (config := {decide := true}) only [faceIdFB, Fin.prod_univ_four, mB, faceIdRB,
          faceIdV, faceId_c_castSucc, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, cVB,
          ite_true, ite_false, decide_true, decide_false, faceId_G_false, faceId_W_true,
          faceId_inv_propDenom_eq_G, Fin.isValue, mul_one, zero_smul, one_smul,
          zero_add, zk, Fin.zero_eta, Fin.reduceFinMk])
  · refine EF.zero.congr fun x => ?_
    simp only [faceIdFB]
    cases hi : faceIdRB baseVB ![1, 0] i <;> simp_all [faceId_W_false]

theorem faceId_efA_VB0 (n : (Fin 4 → ℝ) → ℂ) (hn : IsLoopPoly 2 2 fun ℓ => n (ℓ 0))
    (i j : Fin 4) (hij : i ≤ j) :
    EF (faceIdFA (faceIdRB baseVB ![0, 1]) cVB ε k n M X Y i j) := by
  by_cases hb : faceIdRB baseVB ![0, 1] i = true ∧ faceIdRB baseVB ![0, 1] j = true
  · refine (ef4 (-k) hε n hn (mA M X Y i j 1) (mA M X Y i j 2) X Y true false
      (decide (i = 1)) (decide (j = 1))).congr fun x => ?_
    fin_cases i <;> fin_cases j <;> first
      | exact absurd hij (by decide)
      | exact absurd hb (by decide)
      | (simp (config := {decide := true}) only [faceIdFA, Fin.prod_univ_four, mA, faceIdRB,
          faceIdV, faceId_c_castSucc, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, cVB,
          ite_true, ite_false, decide_true, decide_false, faceId_G_false, faceId_W_true,
          faceId_inv_propDenom_eq_G, Fin.isValue, mul_one, zero_smul, one_smul,
          zero_add, zk, Fin.reduceFinMk, neg_smul, one_mul])
  · refine EF.zero.congr fun x => ?_
    simp only [faceIdFA]
    cases hi : faceIdRB baseVB ![0, 1] i <;> cases hj : faceIdRB baseVB ![0, 1] j <;>
      simp_all [faceId_W_false]

theorem faceId_efB_VB0 (n : (Fin 4 → ℝ) → ℂ) (hn : IsLoopPoly 2 0 fun ℓ => n (ℓ 0))
    (i : Fin 4) : EF (faceIdFB (faceIdRB baseVB ![0, 1]) cVB ε k n X Y i) := by
  by_cases hb : faceIdRB baseVB ![0, 1] i = true
  · refine (ef3 (-k) hε n hn (mB X Y i 1) (mB X Y i 2) Y true false
      (decide (i = 1))).congr fun x => ?_
    fin_cases i <;> first
      | exact absurd hb (by decide)
      | (simp (config := {decide := true}) only [faceIdFB, Fin.prod_univ_four, mB, faceIdRB,
          faceIdV, faceId_c_castSucc, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, cVB,
          ite_true, ite_false, decide_true, decide_false, faceId_G_false, faceId_W_true,
          faceId_inv_propDenom_eq_G, Fin.isValue, mul_one, zero_smul, one_smul,
          zero_add, zk, Fin.reduceFinMk, neg_smul, one_mul])
  · refine EF.zero.congr fun x => ?_
    simp only [faceIdFB]
    cases hi : faceIdRB baseVB ![0, 1] i <;> simp_all [faceId_W_false]

end QED.GradedProof.RPi4

end
