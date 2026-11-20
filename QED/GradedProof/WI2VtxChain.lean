/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2Chain
public import QED.TwoLoop.LimitCovarianceOpen

/-!
# The open-class vertex chains at zero photon momentum, contracted

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A7 for the six open classes. The numerator of an open class is the chain form
`chainNum P π E μ` (`QED.TwoLoop.LimitCovariance.chainNum`) with the external photon at the
vertex `π 0`. Contracted with `r` (`∑_μ r_μ`), the external vertex becomes `r̸`, and removing that
vertex leaves the open two-loop chain of `R` or `X` (`chainAt (wR P)`, `chainAt (wX P)`) with the
two electron numerators next to it merged into one slot `E r̸ E'`
(`sum_lower_smul_chainNum_Sp`, …, one per class).

* `sum_lower_smul_chainNum`: the contraction collapses the Kronecker symbol;
* `sum_fin5_insertNth`: the sum over the five vertex indices with one index singled out;
* `openChain_insertNth_one`, `_two`, `_three`: the chain with the vertex `k` removed.
-/

@[expose] public section

open Complex Matrix

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 QED.TwoLoop.LimitCovariance

variable (P : QED.WickModel.Params)

/-- **Contracting the external photon index** of the chain form with `r`. -/
theorem sum_lower_smul_chainNum (π : Equiv.Perm (Fin 5)) (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (r : Fin 4 → ℝ) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) • chainNum P π E μ =
      ∑ l : Fin 5 → Fin 4, (((Minkowski.lower r (l (π 0)) : ℝ) : ℂ) *
        (pvEta P (l (π 1)) (l (π 2)) * pvEta P (l (π 3)) (l (π 4)))) •
          openChain (fun t => Dirac.gamma (l t)) E := by
  simp only [chainNum, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp only [kron, mul_assoc, mul_ite, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

/-- The sum over the five vertex indices with the index `k` singled out. -/
theorem sum_fin5_insertNth {M : Type*} [AddCommMonoid M] (k : Fin 5)
    (f : (Fin 5 → Fin 4) → M) :
    ∑ l, f l = ∑ x : Fin 4, ∑ l' : Fin 4 → Fin 4, f (Fin.insertNth k x l') := by
  rw [← (Fin.insertNthEquiv (fun _ => Fin 4) k).sum_comp, Fintype.sum_prod_type]
  rfl

variable (x : Fin 4) (l : Fin 4 → Fin 4) (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)

/-- The chain with the vertex `1` removed. -/
theorem openChain_insertNth_one :
    openChain (fun t => Dirac.gamma (Fin.insertNth (α := fun _ => Fin 4) 1 x l t)) E =
      chainG (fun t => Dirac.gamma (l t)) (E 3) (E 2) (E 1 * Dirac.gamma x * E 0) := by
  simp only [openChain, chainG, Matrix.mul_assoc]
  rfl

/-- The chain with the vertex `2` removed. -/
theorem openChain_insertNth_two :
    openChain (fun t => Dirac.gamma (Fin.insertNth (α := fun _ => Fin 4) 2 x l t)) E =
      chainG (fun t => Dirac.gamma (l t)) (E 3) (E 2 * Dirac.gamma x * E 1) (E 0) := by
  simp only [openChain, chainG, Matrix.mul_assoc]
  rfl

/-- The chain with the vertex `3` removed. -/
theorem openChain_insertNth_three :
    openChain (fun t => Dirac.gamma (Fin.insertNth (α := fun _ => Fin 4) 3 x l t)) E =
      chainG (fun t => Dirac.gamma (l t)) (E 3 * Dirac.gamma x * E 2) (E 1) (E 0) := by
  simp only [openChain, chainG, Matrix.mul_assoc]
  rfl


variable (r : Fin 4 → ℝ) (w : (Fin 4 → Fin 4) → ℂ)

/-- **External photon at vertex `1`**: the contracted chain form is the two-loop chain with
`E₁ r̸ E₀` in slot `0`. -/
theorem sum_lower_smul_chainNum_one (π : Equiv.Perm (Fin 5)) (hπ : π 0 = 1)
    (hw : ∀ y l, pvEta P (Fin.insertNth (α := fun _ => Fin 4) 1 y l (π 1))
      (Fin.insertNth (α := fun _ => Fin 4) 1 y l (π 2)) *
        pvEta P (Fin.insertNth (α := fun _ => Fin 4) 1 y l (π 3))
          (Fin.insertNth (α := fun _ => Fin 4) 1 y l (π 4)) = w l) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) • chainNum P π E μ =
      chainAt w ![E 1 * Dirac.slash r * E 0, E 2, E 3] := by
  rw [sum_lower_smul_chainNum, sum_fin5_insertNth 1, Finset.sum_comm]
  simp only [chainAt, chain4]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [hπ, Fin.insertNth_apply_same, hw, openChain_insertNth_one]
  simp only [chainG, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Dirac.slash, Matrix.mul_sum, Matrix.sum_mul,
    Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  exact Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

/-- **External photon at vertex `2`**: the contracted chain form is the two-loop chain with
`E₂ r̸ E₁` in slot `1`. -/
theorem sum_lower_smul_chainNum_two (π : Equiv.Perm (Fin 5)) (hπ : π 0 = 2)
    (hw : ∀ y l, pvEta P (Fin.insertNth (α := fun _ => Fin 4) 2 y l (π 1))
      (Fin.insertNth (α := fun _ => Fin 4) 2 y l (π 2)) *
        pvEta P (Fin.insertNth (α := fun _ => Fin 4) 2 y l (π 3))
          (Fin.insertNth (α := fun _ => Fin 4) 2 y l (π 4)) = w l) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) • chainNum P π E μ =
      chainAt w ![E 0, E 2 * Dirac.slash r * E 1, E 3] := by
  rw [sum_lower_smul_chainNum, sum_fin5_insertNth 2, Finset.sum_comm]
  simp only [chainAt, chain4]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [hπ, Fin.insertNth_apply_same, hw, openChain_insertNth_two]
  simp only [chainG, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Dirac.slash, Matrix.mul_sum, Matrix.sum_mul,
    Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  exact Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

/-- **External photon at vertex `3`**: the contracted chain form is the two-loop chain with
`E₃ r̸ E₂` in slot `2`. -/
theorem sum_lower_smul_chainNum_three (π : Equiv.Perm (Fin 5)) (hπ : π 0 = 3)
    (hw : ∀ y l, pvEta P (Fin.insertNth (α := fun _ => Fin 4) 3 y l (π 1))
      (Fin.insertNth (α := fun _ => Fin 4) 3 y l (π 2)) *
        pvEta P (Fin.insertNth (α := fun _ => Fin 4) 3 y l (π 3))
          (Fin.insertNth (α := fun _ => Fin 4) 3 y l (π 4)) = w l) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) • chainNum P π E μ =
      chainAt w ![E 0, E 1, E 3 * Dirac.slash r * E 2] := by
  rw [sum_lower_smul_chainNum, sum_fin5_insertNth 3, Finset.sum_comm]
  simp only [chainAt, chain4]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [hπ, Fin.insertNth_apply_same, hw, openChain_insertNth_three]
  simp only [chainG, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Dirac.slash, Matrix.mul_sum, Matrix.sum_mul,
    Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  exact Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

/-! ### The six open classes -/

theorem sum_lower_smul_chainNum_Sp :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) • chainNum P permSp E μ =
      chainAt (wR P) ![E 1 * Dirac.slash r * E 0, E 2, E 3] :=
  sum_lower_smul_chainNum_one P E r _ permSp rfl fun _ _ => rfl

theorem sum_lower_smul_chainNum_Cp :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) • chainNum P permCp E μ =
      chainAt (wX P) ![E 1 * Dirac.slash r * E 0, E 2, E 3] :=
  sum_lower_smul_chainNum_one P E r _ permCp rfl fun _ _ => rfl

theorem sum_lower_smul_chainNum_L :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) • chainNum P permL E μ =
      chainAt (wR P) ![E 0, E 2 * Dirac.slash r * E 1, E 3] :=
  sum_lower_smul_chainNum_two P E r _ permL rfl fun _ _ => rfl

theorem sum_lower_smul_chainNum_X :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) • chainNum P permX E μ =
      chainAt (wX P) ![E 0, E 2 * Dirac.slash r * E 1, E 3] :=
  sum_lower_smul_chainNum_two P E r _ permX rfl fun _ _ => rfl

theorem sum_lower_smul_chainNum_Sm :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) • chainNum P permSm E μ =
      chainAt (wR P) ![E 0, E 1, E 3 * Dirac.slash r * E 2] :=
  sum_lower_smul_chainNum_three P E r _ permSm rfl fun _ _ => rfl

theorem sum_lower_smul_chainNum_Cm :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) • chainNum P permCm E μ =
      chainAt (wX P) ![E 0, E 1, E 3 * Dirac.slash r * E 2] :=
  sum_lower_smul_chainNum_three P E r _ permCm rfl fun _ _ => rfl

end QED.GradedProof.WI2

end
