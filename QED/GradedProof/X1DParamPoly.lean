/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroLimitParam

/-!
# (X₁) piece D: the parametric numerator is polynomial in the external momenta

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece D. Let the line momenta `mom y` of a parametric representation depend on
external four-vectors `y` so that each coordinate is affine (`IsLoopPoly L 1`). At every point
`x` of the simplex, for a **fixed** numerator `Q`:

* the loop shift is affine in `y` (`isLoopPoly_loopShift`), `V` is quadratic
  (`isLoopPoly_symanzikV`);
* `Q(-S)` has degree at most `4` and the contraction `H(-S)·G` degree at most `2`;
* the parametric numerator `paramNum = T₁ + T₂ V + T₃ V²` of
  `QED.TwoLoop.PauliZeroLimit.paramNum` has degree at most `4` in `y`
  (`isLoopPoly_paramNum`).

This is the multi-variable form of `QED.TwoLoop.PauliZeroLimit.isUPoly_paramNum`.
-/

@[expose] public section

open Complex
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit
open QED.Integration.Feynman (simplexPoint)
open QED.TwoLoop.Bridge (IsLoopPoly)
open QED.TwoLoop.PauliZeroLimit (paramNum cdot ofReal_dot_mul)

namespace QED.GradedProof.X1D

variable {L : ℕ}

theorem isLoopPoly_neg {n : ℕ} {F : (Fin L → Fin 4 → ℝ) → ℂ} (hF : IsLoopPoly L n F) :
    IsLoopPoly L n fun y => -F y := by
  simpa using hF.const_mul (-1)

theorem isLoopPoly_cdot {D E : ℕ} {a b : (Fin L → Fin 4 → ℝ) → Fin 4 → ℂ}
    (ha : ∀ μ, IsLoopPoly L D fun y => a y μ) (hb : ∀ μ, IsLoopPoly L E fun y => b y μ) :
    IsLoopPoly L (D + E) fun y => cdot (a y) (b y) := by
  unfold cdot
  exact (((isLoopPoly_neg ((ha 0).mul (hb 0))).add ((ha 1).mul (hb 1))).add
    ((ha 2).mul (hb 2))).add ((ha 3).mul (hb 3))

section Data

variable {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (mom : (Fin L → Fin 4 → ℝ) → Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) (z : Fin (m + 1) → ℝ)

theorem isLoopPoly_loopShift (hmom : ∀ i μ, IsLoopPoly L 1 fun y => ((mom y i μ : ℝ) : ℂ))
    (s : Fin 2) (μ : Fin 4) :
    IsLoopPoly L 1 fun y => ((loopShift α (mom y) z s μ : ℝ) : ℂ) := by
  have e : ∀ y, ((loopShift α (mom y) z s μ : ℝ) : ℂ) =
      ∑ t, (((symanzikMatrix α z)⁻¹ s t : ℝ) : ℂ) *
        ∑ i, ((z i * α i t : ℝ) : ℂ) * ((mom y i μ : ℝ) : ℂ) := by
    intro y
    have hS : loopShift α (mom y) z s μ =
        ∑ t, (symanzikMatrix α z)⁻¹ s t * ∑ i, z i * α i t * mom y i μ := by
      refine Fin.cases ?_ (fun c => ?_) μ <;> rfl
    rw [hS]
    push_cast
    rfl
  rw [show (fun y => ((loopShift α (mom y) z s μ : ℝ) : ℂ)) = _ from funext e]
  exact IsLoopPoly.sum _ fun t _ => IsLoopPoly.const_mul _
    (IsLoopPoly.sum _ fun i _ => IsLoopPoly.const_mul _ (hmom i μ))

/-- **`V` is quadratic in the external momenta.** -/
theorem isLoopPoly_symanzikV (hmom : ∀ i μ, IsLoopPoly L 1 fun y => ((mom y i μ : ℝ) : ℂ)) :
    IsLoopPoly L 2 fun y => ((symanzikV α (mom y) M z : ℝ) : ℂ) := by
  have hB : ∀ s μ, IsLoopPoly L 1 fun y => ((symanzikVector α (mom y) z s μ : ℝ) : ℂ) :=
    fun s μ => by
      have e : ∀ y, ((symanzikVector α (mom y) z s μ : ℝ) : ℂ) =
          ∑ i, ((z i * α i s : ℝ) : ℂ) * ((mom y i μ : ℝ) : ℂ) := by
        intro y
        simp only [symanzikVector]
        push_cast
        rfl
      rw [show (fun y => ((symanzikVector α (mom y) z s μ : ℝ) : ℂ)) = _ from funext e]
      exact IsLoopPoly.sum _ fun i _ => IsLoopPoly.const_mul _ (hmom i μ)
  have e : ∀ y, ((symanzikV α (mom y) M z : ℝ) : ℂ) =
      ∑ i, ((z i : ℝ) : ℂ) * (((M i ^ 2 : ℝ) : ℂ) +
        cdot (fun μ => ((mom y i μ : ℝ) : ℂ)) (fun μ => ((mom y i μ : ℝ) : ℂ))) -
      ∑ s, ∑ t, (((symanzikMatrix α z)⁻¹ s t : ℝ) : ℂ) *
        cdot (fun μ => ((symanzikVector α (mom y) z s μ : ℝ) : ℂ))
          (fun μ => ((symanzikVector α (mom y) z t μ : ℝ) : ℂ)) := by
    intro y
    have h1 := fun a b : Fin 4 → ℝ => ofReal_dot_mul a b 1 1
    simp only [one_mul] at h1
    simp only [symanzikV, ← h1]
    push_cast
    rfl
  rw [show (fun y => ((symanzikV α (mom y) M z : ℝ) : ℂ)) = _ from funext e]
  refine IsLoopPoly.sub ?_ ?_
  · refine IsLoopPoly.sum _ fun i _ => ?_
    have h := ((IsLoopPoly.const ((M i ^ 2 : ℝ) : ℂ)).add
      (isLoopPoly_cdot (fun μ => hmom i μ) (fun μ => hmom i μ)))
    exact (IsLoopPoly.const_mul _ h).mono (le_refl _)
  · exact IsLoopPoly.sum _ fun s _ => IsLoopPoly.sum _ fun t _ =>
      IsLoopPoly.const_mul _ (isLoopPoly_cdot (fun μ => hB s μ) (fun μ => hB t μ))

end Data

section Contract

variable (Q : LoopQuartic) (X : (Fin L → Fin 4 → ℝ) → LoopIndex → ℂ)

theorem isLoopPoly_evalC (hX : ∀ a, IsLoopPoly L 1 fun y => X y a) :
    IsLoopPoly L 4 fun y => Q.evalC (X y) := by
  unfold LoopQuartic.evalC
  refine ((((IsLoopPoly.const Q.const).add ?_).add ?_).add ?_).add ?_
  · exact IsLoopPoly.sum _ fun a _ => IsLoopPoly.const_mul _ ((hX a).mono (by norm_num))
  · exact IsLoopPoly.sum _ fun a _ => IsLoopPoly.sum _ fun b _ => IsLoopPoly.const_mul _
      (((hX a).mul (hX b)).mono (by norm_num))
  · exact IsLoopPoly.sum _ fun a _ => IsLoopPoly.sum _ fun b _ => IsLoopPoly.sum _ fun c _ =>
      IsLoopPoly.const_mul _ ((((hX a).mul (hX b)).mul (hX c)).mono (by norm_num))
  · exact IsLoopPoly.sum _ fun a _ => IsLoopPoly.sum _ fun b _ => IsLoopPoly.sum _ fun c _ =>
      IsLoopPoly.sum _ fun d _ => IsLoopPoly.const_mul _ ((((hX a).mul (hX b)).mul (hX c)).mul
        (hX d))

theorem isLoopPoly_contractTwo (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hX : ∀ a, IsLoopPoly L 1 fun y => X y a) :
    IsLoopPoly L 2 fun y => Q.contractTwo A (X y) := by
  unfold LoopQuartic.contractTwo LoopQuartic.hess
  refine IsLoopPoly.sum _ fun a _ => IsLoopPoly.sum _ fun b _ => ?_
  have h : IsLoopPoly L 2 fun y => Q.quad a b + ∑ c, (Q.cub a b c + Q.cub a c b +
      Q.cub c a b) * X y c + ∑ c, ∑ d, Q.quartSym a b c d * (X y c * X y d) := by
    refine ((IsLoopPoly.const _).add ?_).add ?_
    · exact IsLoopPoly.sum _ fun c _ => IsLoopPoly.const_mul _ ((hX c).mono (by norm_num))
    · exact IsLoopPoly.sum _ fun c _ => IsLoopPoly.sum _ fun d _ =>
        IsLoopPoly.const_mul _ ((hX c).mul (hX d))
  exact (h.mul (IsLoopPoly.const (n := 0) _)).mono (by norm_num)

end Contract

/-- **The parametric numerator is polynomial of degree at most `4` in the external momenta**,
at every point `x` of the simplex, for a fixed numerator `Q`. -/
theorem isLoopPoly_paramNum {m : ℕ} (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (mom : (Fin L → Fin 4 → ℝ) → Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ)
    (hmom : ∀ i μ, IsLoopPoly L 1 fun y => ((mom y i μ : ℝ) : ℂ)) (x : Fin m → ℝ) :
    IsLoopPoly L 4 fun y => paramNum Q α (mom y) M x := by
  have hS := isLoopPoly_loopShift α mom (simplexPoint x) hmom
  have hX : ∀ a : LoopIndex, IsLoopPoly L 1 fun y =>
      loopComp (-loopShift α (mom y) (simplexPoint x)) a := fun a => by
    have e : ∀ y, loopComp (-loopShift α (mom y) (simplexPoint x)) a =
        -((loopShift α (mom y) (simplexPoint x) a.1 a.2 : ℝ) : ℂ) := by
      intro y
      simp [loopComp]
    rw [show (fun y => loopComp (-loopShift α (mom y) (simplexPoint x)) a) = _ from funext e]
    exact isLoopPoly_neg (hS a.1 a.2)
  have hV := isLoopPoly_symanzikV α mom M (simplexPoint x) hmom
  have h1 := (isLoopPoly_evalC Q _ hX).const_mul
    (((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ * ((m - 4).factorial : ℂ))
  have h2 := ((isLoopPoly_contractTwo Q _ (symanzikMatrix α (simplexPoint x)) hX).mul
    hV).const_mul
    (((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ * (((m - 5).factorial : ℂ) / 2))
  have h3 := (hV.mul hV).const_mul
    (((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
      (((m - 6).factorial : ℂ) / 4 * Q.contractFour (symanzikMatrix α (simplexPoint x))))
  have e : (fun y => paramNum Q α (mom y) M x) = fun y =>
      ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ * ((m - 4).factorial : ℂ) *
          Q.evalC (loopComp (-loopShift α (mom y) (simplexPoint x))) +
        ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ * (((m - 5).factorial : ℂ) / 2) *
          (Q.contractTwo (symanzikMatrix α (simplexPoint x))
            (loopComp (-loopShift α (mom y) (simplexPoint x))) *
            ((symanzikV α (mom y) M (simplexPoint x) : ℝ) : ℂ)) +
        ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
            (((m - 6).factorial : ℂ) / 4 * Q.contractFour (symanzikMatrix α (simplexPoint x))) *
          (((symanzikV α (mom y) M (simplexPoint x) : ℝ) : ℂ) *
            ((symanzikV α (mom y) M (simplexPoint x) : ℝ) : ℂ)) := by
    funext y
    simp only [paramNum, coeffOne, coeffTwo, coeffThree, LoopQuartic.eval]
    ring
  rw [e]
  exact (h1.add (h2.mono (by norm_num))).add h3

end QED.GradedProof.X1D

end
