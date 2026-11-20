/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4LoopDeg
public import QED.GradedProof.VP2VNum
public import QED.GradedProof.VP2ClassVA
public import QED.GradedProof.VP2ClassVB
public import QED.GradedProof.VP2ClassVC

/-!
# (R-Π₄) step L6d1: the degree of the class numerators along one loop

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d1. A class numerator
`QED.GradedProof.VP2.vNum` is a trace with one factor `M - ℓ̸ₑ` per fermion line, so its degree
along loop `s` is at most the number of fermion lines whose loop row has a nonzero entry `s`:

* `IsLoopPolyDegMat`, with `const`, `mul`, `trace`;
* `isLoopPolyDeg_coord_affine`, `isLoopPolyDegMat_electronNumerator`: one factor;
* `loopDegOf base s`: the number of fermion lines of `base` that run through loop `s`;
* `isLoopPolyDeg_vT`, **`isLoopPolyDeg_vNum`**;
* `exists_loopQuartic_vNum`, `exists_loopQuartic_vNum_sub`: the numerators of the merged pieces
  as quartics whose coefficients with more than `loopDegOf base s` indices in loop `s` vanish;
* `loopDegOf_VA`, `loopDegOf_VB`, `loopDegOf_VC`: along loop `1`, the classes `VA` and `VC` (a
  self-energy insertion) have degree `1` and `VB` (a vertex insertion) degree `2`; along loop `0`,
  `VB` has degree `2`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.Bridge QED.GradedProof.VP2

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-! ### Matrices of polynomials of bounded degree along one loop -/

/-- The entries of a matrix-valued function have degree `≤ d` along loop `s` and total degree
`≤ n`. -/
def IsLoopPolyDegMat (s : Fin 2) (d n : ℕ)
    (A : (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ i j, IsLoopPolyDeg s d n fun ℓ => A ℓ i j

namespace IsLoopPolyDegMat

variable {s : Fin 2} {d d' n n' : ℕ} {A B : (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}

theorem const (C : Matrix (Fin 4) (Fin 4) ℂ) : IsLoopPolyDegMat s 0 0 fun _ => C :=
  fun _ _ => IsLoopPolyDeg.const _

theorem mul (hA : IsLoopPolyDegMat s d n A) (hB : IsLoopPolyDegMat s d' n' B) :
    IsLoopPolyDegMat s (d + d') (n + n') fun ℓ => A ℓ * B ℓ := fun i j => by
  simp only [Matrix.mul_apply]
  exact IsLoopPolyDeg.sum _ fun k _ => (hA i k).mul (hB k j)

theorem trace (hA : IsLoopPolyDegMat s d n A) : IsLoopPolyDeg s d n fun ℓ => (A ℓ).trace := by
  simp only [Matrix.trace, Matrix.diag]
  exact IsLoopPolyDeg.sum _ fun i _ => hA i i

end IsLoopPolyDegMat

/-! ### One factor `M - ℓ̸ₑ` -/

/-- `0` if the affine coefficient of loop `s` vanishes, else `1`. -/
noncomputable def affDeg (s : Fin 2) (a : Fin 2 → ℝ) : ℕ := by
  classical exact if a s = 0 then 0 else 1

theorem isLoopPolyDeg_coord_affine (s : Fin 2) (a : Fin 2 → ℝ) (b : Fin 4 → ℝ) (ν : Fin 4) :
    IsLoopPolyDeg s (affDeg s a) 1 fun ℓ => (((∑ r, a r • ℓ r + b) ν : ℝ) : ℂ) := by
  classical
  have h : (fun ℓ : Fin 2 → Fin 4 → ℝ => (((∑ r, a r • ℓ r + b) ν : ℝ) : ℂ)) =
      fun ℓ => (∑ r ∈ Finset.univ, (a r : ℂ) * ((ℓ r ν : ℝ) : ℂ)) + (b ν : ℂ) := by
    funext ℓ
    simp
  rw [h]
  refine (IsLoopPolyDeg.sum _ fun r _ => ?_).add (IsLoopPolyDeg.const _)
  by_cases hr : r = s
  · subst hr
    by_cases ha : a r = 0
    · simp only [ha, ofReal_zero, zero_mul]
      exact IsLoopPolyDeg.const _
    · have : affDeg r a = 1 := by simp [affDeg, ha]
      rw [this]
      exact (IsLoopPolyDeg.coord r ν le_rfl le_rfl).const_mul _
  · exact (IsLoopPolyDeg.coord_ne hr ν le_rfl).const_mul _

theorem isLoopPolyDegMat_electronNumerator (s : Fin 2) (a : Fin 2 → ℝ) (b : Fin 4 → ℝ) (m : ℝ) :
    IsLoopPolyDegMat s (affDeg s a) 1 fun ℓ => electronNumerator m (∑ r, a r • ℓ r + b) :=
  fun i j => by
    simp only [electronNumerator_apply]
    refine (IsLoopPolyDeg.const _).sub
      (IsLoopPolyDeg.sum _ fun μ _ => IsLoopPolyDeg.sum _ fun ν _ => ?_)
    have h : (fun ℓ : Fin 2 → Fin 4 → ℝ => ((Minkowski.metric μ ν : ℝ) : ℂ) *
        (((∑ r, a r • ℓ r + b) ν : ℝ) : ℂ) * Dirac.gamma μ i j) =
        fun ℓ => (((Minkowski.metric μ ν : ℝ) : ℂ) * Dirac.gamma μ i j) *
          (((∑ r, a r • ℓ r + b) ν : ℝ) : ℂ) := by
      funext ℓ; ring
    rw [h]
    exact (isLoopPolyDeg_coord_affine s a b ν).const_mul _

/-! ### The class numerators -/

/-- The number of fermion lines of `base` running through loop `s`. -/
def loopDegOf (base : Fin 5 → Fin 2 → ℤ) (s : Fin 2) : ℕ :=
  ∑ l : Fin 4, if base l.castSucc s = 0 then 0 else 1

theorem affDeg_castLoopMatrix (base : Fin 5 → Fin 2 → ℤ) (s : Fin 2) (l : Fin 4) :
    affDeg s (castLoopMatrix base l.castSucc) = if base l.castSucc s = 0 then 0 else 1 := by
  simp [affDeg, castLoopMatrix]

theorem fm_eq_affine (base : Fin 5 → Fin 2 → ℤ) (pp : Fin 5 → Fin 4 → ℝ) (l : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    fm base pp l ℓ = ∑ r, castLoopMatrix base l.castSucc r • ℓ r + pp l.castSucc := by
  funext μ
  simp [fm, lineMomentum, Fin.sum_univ_two]

/-- **The trace of a fermion loop has degree at most `loopDegOf base s` along loop `s`.** -/
theorem isLoopPolyDeg_vT (base : Fin 5 → Fin 2 → ℤ) (pp : Fin 5 → Fin 4 → ℝ) (s : Fin 2)
    (G : Fin 4 → Mat) (M : ℝ) :
    IsLoopPolyDeg s (loopDegOf base s) 4 fun ℓ => vT G M (fun l => fm base pp l ℓ) := by
  have N : ∀ l : Fin 4, IsLoopPolyDegMat s (if base l.castSucc s = 0 then 0 else 1) 1
      fun ℓ => electronNumerator M (fm base pp l ℓ) := fun l => by
    simp only [fm_eq_affine]
    rw [← affDeg_castLoopMatrix]
    exact isLoopPolyDegMat_electronNumerator s _ _ M
  have h := ((((((((IsLoopPolyDegMat.const (s := s) (G 0)).mul (N 0)).mul
    (IsLoopPolyDegMat.const (G 1))).mul (N 1)).mul (IsLoopPolyDegMat.const (G 2))).mul
    (N 2)).mul (IsLoopPolyDegMat.const (G 3))).mul (N 3)).trace
  refine h.mono (le_of_eq ?_) (by norm_num)
  simp [loopDegOf, Fin.sum_univ_four]

/-- **The class numerator has degree at most `loopDegOf base s` along loop `s`.** -/
theorem isLoopPolyDeg_vNum (e mγ Λ : ℝ) (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Mat)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (s : Fin 2) (m : ℝ) (k : Fin 4 → ℝ)
    (a b : Fin 4) :
    IsLoopPolyDeg s (loopDegOf base s) 4 fun ℓ => vNum e mγ Λ A base c m k ℓ a b :=
  IsLoopPolyDeg.sum _ fun ρ _ => IsLoopPolyDeg.sum _ fun σ _ =>
    (isLoopPolyDeg_vT base (ppc c k) s (A a b ρ σ) m).const_mul _

/-- **A quartic of bounded degree along loop `s` for a multiple of a class numerator** (the
numerator of the merged pieces with eight lines). -/
theorem exists_loopQuartic_vNum (e mγ Λ : ℝ) (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Mat)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (s : Fin 2) (C : ℂ) (m : ℝ) (k : Fin 4 → ℝ)
    (a b : Fin 4) : ∃ Q : LoopQuartic, LoopDegLe s (loopDegOf base s) Q ∧
      Q.eval = fun ℓ => C * vNum e mγ Λ A base c m k ℓ a b :=
  exists_loopQuartic_deg ((isLoopPolyDeg_vNum e mγ Λ A base c s m k a b).const_mul C)

/-- The same for a multiple of a difference of class numerators at two masses (the numerator of
the merged pieces with seven lines). -/
theorem exists_loopQuartic_vNum_sub (e mγ Λ : ℝ)
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Mat) (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
    (s : Fin 2) (C : ℂ) (m m' : ℝ) (k : Fin 4 → ℝ) (a b : Fin 4) :
    ∃ Q : LoopQuartic, LoopDegLe s (loopDegOf base s) Q ∧
      Q.eval = fun ℓ => C * (vNum e mγ Λ A base c m k ℓ a b - vNum e mγ Λ A base c m' k ℓ a b) :=
  exists_loopQuartic_deg (((isLoopPolyDeg_vNum e mγ Λ A base c s m k a b).sub
    (isLoopPolyDeg_vNum e mγ Λ A base c s m' k a b)).const_mul C)

theorem loopDegOf_VA : loopDegOf baseVA 1 = 1 := by decide

theorem loopDegOf_VB : loopDegOf baseVB 1 = 2 ∧ loopDegOf baseVB 0 = 2 := by decide

theorem loopDegOf_VC : loopDegOf baseVC 1 = 1 := by decide

end QED.GradedProof.RPi4

end
