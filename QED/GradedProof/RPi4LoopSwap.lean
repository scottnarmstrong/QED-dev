/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceScale
public import QED.GradedProof.RPi4CollapseSwap
public import QED.GradedProof.RPi4FaceV

/-!
# (R-Π₄) step L6d2: relabelling the loops and reversing lines

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d2. The second vertex
face `H₁` of the class `VB` has loop `0` as its subgraph loop. Exchanging the two loops (the
columns of the loop rows `α`, and the loop indices of the numerator `Q`) and reversing the lines
whose row becomes `(-1, 1)` (row and external momentum negated) turns it into a face of loop `1`
with rows `(0, 1)`/`(1, -1)` on the face block and `(1, 0)` on the rest, so the face analysis of
`RPi4FaceRate` applies unchanged. The parametric integrand and `V` are invariant:

* `swI`, `swapQ`, `evalC_swapQ`, `hess_swapQ`, `cTwoG_swapQ`, `cFourG_swapQ`, `ehat_swapQ`;
* `swapRows`, **`paramAtV_swap`**, **`symanzikV_swap`**, **`loopDegLe_swapQ`**;
* `flipRows`, **`paramAtV_flip`**, **`symanzikV_flip`** (lines reversed, `εᵢ = ±1`).
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit
open QED.GradedProof.WI2 (ehat)

/-- The exchange of the two loops. -/
def lsw : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

/-- The exchange of the two loops on loop indices. -/
def swI : LoopIndex ≃ LoopIndex := Equiv.prodCongr lsw (Equiv.refl (Fin 4))

theorem swI_apply (a : LoopIndex) : swI a = (lsw a.1, a.2) := rfl

section Sums

variable {β : Type*} [AddCommMonoid β]

theorem sum_swI (F : LoopIndex → β) : ∑ a, F (swI a) = ∑ a, F a := Equiv.sum_comp swI F

theorem sum_swI₂ (F : LoopIndex → LoopIndex → β) :
    ∑ a, ∑ b, F (swI a) (swI b) = ∑ a, ∑ b, F a b := by
  rw [← sum_swI fun a => ∑ b, F a b]
  exact Finset.sum_congr rfl fun a _ => sum_swI (F (swI a))

theorem sum_swI₃ (F : LoopIndex → LoopIndex → LoopIndex → β) :
    ∑ a, ∑ b, ∑ c, F (swI a) (swI b) (swI c) = ∑ a, ∑ b, ∑ c, F a b c := by
  rw [← sum_swI₂ fun a b => ∑ c, F a b c]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    sum_swI (F (swI a) (swI b))

theorem sum_swI₄ (F : LoopIndex → LoopIndex → LoopIndex → LoopIndex → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, F (swI a) (swI b) (swI c) (swI d) = ∑ a, ∑ b, ∑ c, ∑ d, F a b c d := by
  rw [← sum_swI₃ fun a b c => ∑ d, F a b c d]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => sum_swI (F (swI a) (swI b) (swI c))

end Sums

/-- The numerator with the two loops exchanged. -/
def swapQ (Q : LoopQuartic) : LoopQuartic where
  const := Q.const
  lin a := Q.lin (swI a)
  quad a b := Q.quad (swI a) (swI b)
  cub a b c := Q.cub (swI a) (swI b) (swI c)
  quart a b c d := Q.quart (swI a) (swI b) (swI c) (swI d)

variable (Q : LoopQuartic) (X : LoopIndex → ℂ)

theorem evalC_swapQ : (swapQ Q).evalC (X ∘ swI) = Q.evalC X := by
  simp only [LoopQuartic.evalC, swapQ, Function.comp]
  rw [sum_swI (fun a => Q.lin a * X a), sum_swI₂ (fun a b => Q.quad a b * (X a * X b)),
    sum_swI₃ (fun a b c => Q.cub a b c * (X a * X b * X c)),
    sum_swI₄ (fun a b c d => Q.quart a b c d * (X a * X b * X c * X d))]

theorem hess_swapQ (a b : LoopIndex) :
    (swapQ Q).hess (X ∘ swI) a b = Q.hess X (swI a) (swI b) := by
  simp only [LoopQuartic.hess, LoopQuartic.quartSym, swapQ, Function.comp]
  rw [sum_swI (fun c => (Q.cub (swI a) (swI b) c + Q.cub (swI a) c (swI b) +
      Q.cub c (swI a) (swI b)) * X c),
    sum_swI₂ (fun c d => (Q.quart (swI a) (swI b) c d + Q.quart (swI a) c (swI b) d +
      Q.quart (swI a) c d (swI b) + Q.quart c (swI a) (swI b) d + Q.quart c (swI a) d (swI b) +
      Q.quart c d (swI a) (swI b)) * (X c * X d))]

theorem gMet_submatrix (G : Matrix (Fin 2) (Fin 2) ℝ) (a b : LoopIndex) :
    gMet (G.submatrix lsw lsw) a b = gMet G (swI a) (swI b) := rfl

theorem cTwoG_swapQ (G : Matrix (Fin 2) (Fin 2) ℝ) :
    cTwoG (swapQ Q) (G.submatrix lsw lsw) (X ∘ swI) = cTwoG Q G X := by
  simp only [cTwoG, hess_swapQ, gMet_submatrix]
  exact sum_swI₂ (fun a b => Q.hess X a b * (gMet G a b : ℂ))

theorem cFourG_swapQ (G : Matrix (Fin 2) (Fin 2) ℝ) :
    cFourG (swapQ Q) (G.submatrix lsw lsw) = cFourG Q G := by
  simp only [cFourG, swapQ]
  exact sum_swI₄ (fun a b c d => Q.quart a b c d * (matPair (gMet G) a b c d : ℂ))

theorem ehat_swapQ (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ) (W : ℂ) :
    ehat n (swapQ Q) (A.submatrix lsw lsw) (X ∘ swI) W = ehat n Q A X W := by
  simp only [ehat, contractTwo_eq_cTwoG, contractFour_eq_cFourG, Matrix.inv_submatrix_equiv,
    evalC_swapQ, cTwoG_swapQ, cFourG_swapQ]

/-! ### Exchanging the loop columns of the rows -/

variable {m : ℕ}

/-- The loop rows with the two loops exchanged. -/
def swapRows (α : Fin (m + 1) → Fin 2 → ℝ) : Fin (m + 1) → Fin 2 → ℝ := fun i s => α i (lsw s)

variable (α : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ) (z : Fin (m + 1) → ℝ)

theorem symanzikMatrix_swap :
    symanzikMatrix (swapRows α) z = (symanzikMatrix α z).submatrix lsw lsw := by
  ext s t; rfl

theorem symanzikU_swap : symanzikU (swapRows α) z = symanzikU α z := by
  simp only [symanzikU, symanzikMatrix_swap, Matrix.det_submatrix_equiv_self]

theorem symanzikVector_swap (s : Fin 2) :
    symanzikVector (swapRows α) pp z s = symanzikVector α pp z (lsw s) := rfl

theorem loopShift_swap (s : Fin 2) (μ : Fin 4) :
    loopShift (swapRows α) pp z s μ = loopShift α pp z (lsw s) μ := by
  rw [QED.TwoLoop.LimitCovariance.loopShift_apply, QED.TwoLoop.LimitCovariance.loopShift_apply,
    symanzikMatrix_swap, Matrix.inv_submatrix_equiv]
  exact Equiv.sum_comp lsw (fun t => (symanzikMatrix α z)⁻¹ (lsw s) t *
    ∑ i, z i * α i t * pp i μ)

/-- **The parametric integrand is invariant under the exchange of the loops.** -/
theorem paramAtV_swap (n : ℕ) (v : ℝ) :
    paramAtV n (swapQ Q) (swapRows α) pp z v = paramAtV n Q α pp z v := by
  have e : loopComp (-loopShift (swapRows α) pp z) = loopComp (-loopShift α pp z) ∘ swI := by
    funext a
    simp only [loopComp, Pi.neg_apply, loopShift_swap, Function.comp, swI_apply]
  simp only [paramAtV, symanzikU_swap, symanzikMatrix_swap, e, ehat_swapQ]

/-- **`V` is invariant under the exchange of the loops.** -/
theorem symanzikV_swap (M : Fin (m + 1) → ℝ) :
    symanzikV (swapRows α) pp M z = symanzikV α pp M z := by
  simp only [symanzikV, symanzikMatrix_swap, Matrix.inv_submatrix_equiv, symanzikVector_swap]
  congr 1
  rw [← Equiv.sum_comp lsw (fun s => ∑ t, (symanzikMatrix α z)⁻¹ s t *
    Minkowski.dot (symanzikVector α pp z s) (symanzikVector α pp z t))]
  exact Finset.sum_congr rfl fun s _ => Equiv.sum_comp lsw
    (fun t => (symanzikMatrix α z)⁻¹ (lsw s) t *
      Minkowski.dot (symanzikVector α pp z (lsw s)) (symanzikVector α pp z t))

theorem loopInd_swI (a : LoopIndex) : loopInd 1 a = loopInd 0 (swI a) := by
  obtain ⟨s, μ⟩ := a
  fin_cases s <;> rfl

/-- **The degree along a loop is carried to the other loop.** -/
theorem loopDegLe_swapQ {d : ℕ} {Q : LoopQuartic} (h : LoopDegLe 0 d Q) :
    LoopDegLe 1 d (swapQ Q) where
  lin a ha := h.lin _ (by rwa [loopInd_swI] at ha)
  quad a b ha := h.quad _ _ (by rwa [loopInd_swI, loopInd_swI] at ha)
  cub a b c ha := h.cub _ _ _ (by rwa [loopInd_swI, loopInd_swI, loopInd_swI] at ha)
  quart a b c e ha := h.quart _ _ _ _ (by
    rwa [loopInd_swI, loopInd_swI, loopInd_swI, loopInd_swI] at ha)

/-! ### Reversing lines -/

/-- The rows with line `i` reversed when `εᵢ = -1`. -/
def flipRows (ε : Fin (m + 1) → ℝ) (α : Fin (m + 1) → Fin 2 → ℝ) : Fin (m + 1) → Fin 2 → ℝ :=
  fun i s => ε i * α i s

/-- The external momenta with line `i` reversed when `εᵢ = -1`. -/
def flipMom (ε : Fin (m + 1) → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ) : Fin (m + 1) → Fin 4 → ℝ :=
  fun i μ => ε i * pp i μ

variable {ε : Fin (m + 1) → ℝ} (hε : ∀ i, ε i * ε i = 1)
include hε

theorem symanzikMatrix_flip : symanzikMatrix (flipRows ε α) z = symanzikMatrix α z := by
  ext s t
  simp only [symanzikMatrix, Matrix.of_apply, flipRows]
  exact Finset.sum_congr rfl fun i _ => by
    linear_combination (z i * α i s * α i t) * hε i

theorem symanzikVector_flip :
    symanzikVector (flipRows ε α) (flipMom ε pp) z = symanzikVector α pp z := by
  funext s μ
  simp only [symanzikVector, flipRows, flipMom]
  exact Finset.sum_congr rfl fun i _ => by
    linear_combination (z i * α i s * pp i μ) * hε i

/-- **Reversing lines leaves the parametric integrand unchanged.** -/
theorem paramAtV_flip (n : ℕ) (v : ℝ) :
    paramAtV n Q (flipRows ε α) (flipMom ε pp) z v = paramAtV n Q α pp z v := by
  have hS : loopShift (flipRows ε α) (flipMom ε pp) z = loopShift α pp z := by
    funext s μ
    rw [QED.TwoLoop.LimitCovariance.loopShift_apply, QED.TwoLoop.LimitCovariance.loopShift_apply,
      symanzikMatrix_flip α z hε]
    have e : ∀ t, ∑ i, z i * flipRows ε α i t * flipMom ε pp i μ = ∑ i, z i * α i t * pp i μ :=
      fun t => congrFun (congrFun (symanzikVector_flip α pp z hε) t) μ
    simp only [e]
  simp only [paramAtV, symanzikU, symanzikMatrix_flip α z hε, hS]

/-- **Reversing lines leaves `V` unchanged.** -/
theorem symanzikV_flip (M : Fin (m + 1) → ℝ) :
    symanzikV (flipRows ε α) (flipMom ε pp) M z = symanzikV α pp M z := by
  simp only [symanzikV, symanzikMatrix_flip α z hε, symanzikVector_flip α pp z hε]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have : Minkowski.dot (flipMom ε pp i) (flipMom ε pp i) = Minkowski.dot (pp i) (pp i) := by
    have e : flipMom ε pp i = ε i • pp i := rfl
    rw [e, dot_smul_left_face, dot_smul_right_face, ← mul_assoc, hε i, one_mul]
  rw [this]

end QED.GradedProof.RPi4

end
