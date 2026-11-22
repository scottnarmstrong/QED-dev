/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMUnit
public import QED.TwoLoop.PauliZeroExplicitQuartic

/-!
# Grouping the repeated photon parameters

For the unscaled rows of `QED/ChainProof/SetCUnitMUnit.lean`, the extended Symanzik
matrix and vector depend on the sum of the parameters of the repeated line. The
second Symanzik function retains the weighted mass-square differences.
-/

@[expose] public section

namespace QED.ChainProof.SetCUnitM

open QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassIntegrable
open QED.Integration.TwoLoop

variable {r : ℕ}

/-- Absorb the extra parameters into the parameter of the repeated line. -/
def groupExtra (s : Fin 8) (z : Fin (r + 8) → ℝ) (i : Fin 8) : ℝ :=
  z (mEmb r i) + if i = s then ∑ j, z (mExtra r j) else 0

private theorem sum_lines (f : Fin (r + 8) → ℝ) :
    ∑ i, f i = (∑ i, f (mEmb r i)) + ∑ j, f (mExtra r j) := by
  let e := (finSumFinEquiv (m := 8) (n := r)).trans (finCongr (Nat.add_comm 8 r))
  calc
    ∑ i, f i = ∑ k, f (e k) := (e.sum_comp f).symm
    _ = _ := by
      rw [Fintype.sum_sum_type]
      congr 1
      exact Finset.sum_congr rfl fun j _ =>
        congrArg f (Fin.ext (Nat.add_comm 8 j.val))

private theorem sum_groupExtra (s : Fin 8) (z : Fin (r + 8) → ℝ) (f : Fin 8 → ℝ) :
    ∑ i, groupExtra s z i * f i = (∑ i, z (mEmb r i) * f i) +
      ∑ j, z (mExtra r j) * f s := by
  simp only [groupExtra, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ s), Finset.sum_mul]

/-- Grouping parallel copies of a line preserves the loop matrix. -/
theorem symanzikMatrix_unitM_group (c : Class5) (s : Fin 8) (z : Fin (r + 8) → ℝ) :
    symanzikMatrix (unitMMatrix c s (fun _ : Fin r => 1)) z =
      symanzikMatrix (castLoopMatrix (class5LoopMatrixPV c)) (groupExtra s z) := by
  ext k l
  simp only [symanzikMatrix, Matrix.of_apply, mul_assoc]
  rw [sum_lines, sum_groupExtra]
  simp [unitMMatrix, mScale, mLine, mExt_mEmb, mExt_mExtra]

/-- Grouping parallel copies of a line preserves the external-momentum vector. -/
theorem symanzikVector_unitM_group (c : Class5) (s : Fin 8) (p p' : Fin 4 → ℝ)
    (z : Fin (r + 8) → ℝ) :
    symanzikVector (unitMMatrix c s (fun _ : Fin r => 1))
      (unitMMomenta c s (fun _ : Fin r => 1) p p') z =
      symanzikVector (castLoopMatrix (class5LoopMatrixPV c)) (pvMomentaE c p p')
        (groupExtra s z) := by
  funext k l
  simp only [symanzikVector, mul_assoc]
  rw [sum_lines, sum_groupExtra]
  simp [unitMMatrix, unitMMomenta, mScale, mLine, mExt_mEmb, mExt_mExtra]

/-- The first Symanzik polynomial uses only the grouped parameters. -/
theorem symanzikU_unitM_group (c : Class5) (s : Fin 8) (z : Fin (r + 8) → ℝ) :
    symanzikU (unitMMatrix c s (fun _ : Fin r => 1)) z =
      symanzikU (castLoopMatrix (class5LoopMatrixPV c)) (groupExtra s z) := by
  rw [symanzikU, symanzikU, symanzikMatrix_unitM_group]

/-- The momentum used to shift a quartic numerator uses only the grouped parameters. -/
theorem loopShift_unitM_group (c : Class5) (s : Fin 8) (p p' : Fin 4 → ℝ)
    (z : Fin (r + 8) → ℝ) :
    loopShift (unitMMatrix c s (fun _ : Fin r => 1))
      (unitMMomenta c s (fun _ : Fin r => 1) p p') z =
      loopShift (castLoopMatrix (class5LoopMatrixPV c)) (pvMomentaE c p p')
        (groupExtra s z) := by
  have h (μ : Fin 4) :
      coefVec (unitMMatrix c s (fun _ : Fin r => 1)) z
          (fun i => unitMMomenta c s (fun _ : Fin r => 1) p p' i μ) =
        coefVec (castLoopMatrix (class5LoopMatrixPV c)) (groupExtra s z)
          (fun i => pvMomentaE c p p' i μ) :=
    congrArg (fun B : Fin 2 → Fin 4 → ℝ => fun k => B k μ)
      (symanzikVector_unitM_group c s p p' z)
  unfold loopShift
  congr 1
  · unfold energyShift
    rw [symanzikMatrix_unitM_group, h]
  · funext k μ
    unfold spatialShift
    rw [symanzikMatrix_unitM_group, h]

/-- After grouping, only the mass-square differences affect the remainder. -/
theorem symanzikV_unitM_group (c : Class5) (s : Fin 8) (p p' : Fin 4 → ℝ)
    (M : Fin 8 → ℝ) (cs : Fin r → ℝ) (z : Fin (r + 8) → ℝ) :
    symanzikV (unitMMatrix c s (fun _ : Fin r => 1))
      (unitMMomenta c s (fun _ : Fin r => 1) p p') (mExt M cs) z =
      symanzikV (castLoopMatrix (class5LoopMatrixPV c)) (pvMomentaE c p p') M
          (groupExtra s z) + ∑ j, z (mExtra r j) * (cs j ^ 2 - M s ^ 2) := by
  rw [symanzikV, symanzikV, symanzikMatrix_unitM_group, symanzikVector_unitM_group,
    sum_lines, sum_groupExtra]
  simp only [mExt_mEmb, mExt_mExtra, unitMMomenta, mScale, mLine, id, one_smul]
  have h : (∑ j, z (mExtra r j) *
      (cs j ^ 2 + QED.Minkowski.dot (pvMomentaE c p p' s) (pvMomentaE c p p' s))) =
      (∑ j, z (mExtra r j) *
        (M s ^ 2 + QED.Minkowski.dot (pvMomentaE c p p' s) (pvMomentaE c p p' s))) +
      ∑ j, z (mExtra r j) * (cs j ^ 2 - M s ^ 2) := by
    rw [← Finset.sum_add_distrib]
    congr 1
    funext j
    ring
  rw [h]
  ring

open QED.Integration.Feynman (simplexPoint)
open QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.PauliZeroLimit QED.TwoLoop.ClassLimit

/-- In the extended parametric numerator, the three quartic contractions use grouped
coordinates. The ungrouped masses enter only through the powers of the remainder. -/
theorem paramNumOf_unitM_group (c : Class5) (s : Fin 8) (p p' : Fin 4 → ℝ)
    (M : Fin (r + 8) → ℝ) (x : Fin (r + 7) → ℝ)
    (F : (Fin 2 → Fin 4 → ℝ) → ℂ) :
    let z := simplexPoint x
    let w := groupExtra s z
    let α := castLoopMatrix (class5LoopMatrixPV c)
    let A := symanzikMatrix α w
    let S := loopShift α (pvMomentaE c p p') w
    let V : ℂ := ↑(symanzikV (unitMMatrix c s (fun _ : Fin r => 1))
      (unitMMomenta c s (fun _ : Fin r => 1) p p') M z)
    let Q := numQuartic F
    paramNumOf F (unitMMatrix c s (fun _ : Fin r => 1))
        (unitMMomenta c s (fun _ : Fin r => 1) p p') M x =
      (↑(symanzikU α w ^ 2) : ℂ)⁻¹ *
        (((r + 3).factorial : ℂ) * Q.eval (-S) +
          ((r + 2).factorial : ℂ) / 2 * Q.contractTwo A (loopComp (-S)) * V +
          ((r + 1).factorial : ℂ) / 4 * Q.contractFour A * V ^ 2) := by
  dsimp only
  rw [paramNumOf, paramNum]
  simp only [coeffOne, coeffTwo, coeffThree, symanzikU_unitM_group,
    symanzikMatrix_unitM_group, loopShift_unitM_group]
  rw [show r + 7 - 4 = r + 3 by omega, show r + 7 - 5 = r + 2 by omega,
    show r + 7 - 6 = r + 1 by omega]
  ring

end QED.ChainProof.SetCUnitM

end
