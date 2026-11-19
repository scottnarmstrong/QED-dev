/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2PA
public import QED.Integration.SimplexMerge

/-!
# Merging a doubled line

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A3. Doubling line `i` (`dbl i`: the data of line `i` appended as a last line) and splitting
the Feynman parameter `zᵢ` into `(t, zᵢ - t)` (`QED.Integration.SimplexMerge.splitAt`) leaves the
Symanzik data `A, U, S, V` unchanged (`symanzikMatrix_dbl`, …). Hence the parametric integral of
`N + 1` lines with a doubled line is the integral over `N` lines of `zᵢ` times the
`(N + 1)`-line moment functional at the same data (`integral_paramIntegrand_dbl`): this turns the
term `U⁻² Ê_{N+1}[P · zᵢ ∂Dᵢ]` of the parametric derivative identity into a parametric integral.
-/

@[expose] public section

open Complex MeasureTheory Matrix

namespace QED.GradedProof.WI2

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.Integration.SimplexMerge
open QED.Integration.Feynman (simplexSet simplexPoint)

variable {m : ℕ}

/-- Line data with line `i` doubled (appended as the last line). -/
def dbl {β : Type*} (i : Fin (m + 1)) (f : Fin (m + 1) → β) : Fin (m + 2) → β :=
  Fin.snoc (α := fun _ => β) f (f i)

theorem dbl_map {β₁ β₂ β₃ γ : Type*} (i : Fin (m + 1)) (f : Fin (m + 1) → β₁)
    (g : Fin (m + 1) → β₂) (h : Fin (m + 1) → β₃) (φ : β₁ → β₂ → β₃ → γ) :
    (fun j => φ (dbl i f j) (dbl i g j) (dbl i h j)) = dbl i fun k => φ (f k) (g k) (h k) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [dbl]
  | cast k => simp [dbl]

theorem sum_splitAt_mul_dbl (i : Fin (m + 1)) (z : Fin (m + 1) → ℝ) (t : ℝ)
    (g : Fin (m + 1) → ℝ) : ∑ j, splitAt i z t j * dbl i g j = ∑ j, z j * g j := by
  rw [Fin.sum_univ_castSucc]
  simp only [splitAt_castSucc, splitAt_last, dbl, Fin.snoc_castSucc, Fin.snoc_last]
  have h := Finset.sum_update_of_mem (Finset.mem_univ i) z t
  have e : ∑ j, Function.update z i t j * g j =
      ∑ j, z j * g j - z i * g i + t * g i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    have : ∑ x ∈ Finset.univ.erase i, Function.update z i t x * g x =
        ∑ x ∈ Finset.univ.erase i, z x * g x :=
      Finset.sum_congr rfl fun x hx => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
    rw [this]
    ring
  rw [e]
  ring

theorem sum_splitAt_dbl (i : Fin (m + 1)) (z : Fin (m + 1) → ℝ) (t : ℝ)
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ)
    (φ : (Fin 2 → ℝ) → (Fin 4 → ℝ) → ℝ → ℝ) :
    ∑ j, splitAt i z t j * φ (dbl i α j) (dbl i p j) (dbl i M j) =
      ∑ j, z j * φ (α j) (p j) (M j) := by
  have h := congrFun (dbl_map i α p M φ)
  simp only [h]
  exact sum_splitAt_mul_dbl i z t _

section Data

variable (i : Fin (m + 1)) (z : Fin (m + 1) → ℝ) (t : ℝ) (α : Fin (m + 1) → Fin 2 → ℝ)
  (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ)

theorem symanzikMatrix_dbl :
    symanzikMatrix (dbl i α) (splitAt i z t) = symanzikMatrix α z := by
  ext s r
  simp only [symanzikMatrix, of_apply, mul_assoc]
  exact sum_splitAt_dbl i z t α 0 0 fun a _ _ => a s * a r

theorem symanzikU_dbl : symanzikU (dbl i α) (splitAt i z t) = symanzikU α z := by
  rw [symanzikU, symanzikMatrix_dbl, symanzikU]

theorem symanzikVector_dbl :
    symanzikVector (dbl i α) (dbl i p) (splitAt i z t) = symanzikVector α p z := by
  funext s μ
  simp only [symanzikVector, mul_assoc]
  exact sum_splitAt_dbl i z t α p 0 fun a b _ => a s * b μ

theorem symanzikV_dbl :
    symanzikV (dbl i α) (dbl i p) (dbl i M) (splitAt i z t) = symanzikV α p M z := by
  rw [symanzikV, symanzikV, symanzikMatrix_dbl, symanzikVector_dbl]
  congr 1
  exact sum_splitAt_dbl i z t α p M fun _ b c => c ^ 2 + Minkowski.dot b b

theorem loopShift_dbl :
    loopShift (dbl i α) (dbl i p) (splitAt i z t) = loopShift α p z := by
  funext s μ
  simp only [QED.TwoLoop.LimitCovariance.loopShift_apply, symanzikMatrix_dbl]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  simp only [mul_assoc]
  exact sum_splitAt_dbl i z t α p 0 fun a b _ => a r * b μ

end Data

/-- The parametric integrand as a function of the Feynman point. -/
noncomputable def paramAt (n : ℕ) (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (ε : ℝ) (z : Fin (m + 1) → ℝ) : ℂ :=
  ((symanzikU α z ^ 2 : ℝ) : ℂ)⁻¹ *
    ehat n Q (symanzikMatrix α z) (loopComp (-loopShift α p z))
      (((symanzikV α p M z : ℝ) : ℂ) - (ε : ℂ) * I)

theorem paramIntegrand_eq_paramAt (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (ε : ℝ) (x : Fin m → ℝ) :
    paramIntegrand Q α p M ε x = paramAt m Q α p M ε (simplexPoint x) := rfl

theorem paramAt_dbl (n : ℕ) (Q : LoopQuartic) (i : Fin (m + 1)) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (ε : ℝ) (z : Fin (m + 1) → ℝ)
    (t : ℝ) :
    paramAt n Q (dbl i α) (dbl i p) (dbl i M) ε (splitAt i z t) = paramAt n Q α p M ε z := by
  simp only [paramAt, symanzikU_dbl, symanzikMatrix_dbl, loopShift_dbl, symanzikV_dbl]

/-- **Merging a doubled line**: the parametric integral with line `i` doubled is the integral of
`zᵢ` times the `(N + 1)`-line functional at the undoubled data. -/
theorem integral_paramIntegrand_dbl (hm : 0 < m) (Q : LoopQuartic) (i : Fin (m + 1))
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ)
    (ε : ℝ)
    (hI : IntegrableOn (paramIntegrand Q (dbl i α) (dbl i p) (dbl i M) ε) (simplexSet (m + 1))) :
    IntegrableOn (fun y => (simplexPoint y i : ℂ) * paramAt (m + 1) Q α p M ε (simplexPoint y))
        (simplexSet m) ∧
      ∫ x in simplexSet (m + 1), paramIntegrand Q (dbl i α) (dbl i p) (dbl i M) ε x =
        ∫ y in simplexSet m,
          (simplexPoint y i : ℂ) * paramAt (m + 1) Q α p M ε (simplexPoint y) := by
  obtain ⟨h1, h2⟩ := integral_simplex_splitAt hm i
    (f := paramAt (m + 1) Q (dbl i α) (dbl i p) (dbl i M) ε) hI
  have hin : ∀ y : Fin m → ℝ, ∫ t in (0 : ℝ)..simplexPoint y i,
      paramAt (m + 1) Q (dbl i α) (dbl i p) (dbl i M) ε (splitAt i (simplexPoint y) t) =
        (simplexPoint y i : ℂ) * paramAt (m + 1) Q α p M ε (simplexPoint y) := fun y => by
    rw [integral_splitAt_of_forall_eq i (simplexPoint y) fun t => by
      rw [paramAt_dbl, paramAt_dbl], paramAt_dbl, Complex.real_smul]
  simp only [hin] at h1 h2
  exact ⟨h1, h2⟩

/-! ### Splitting the combined insertion into lines -/

theorem mulLin_sum (P : LoopQuartic) (w c : Fin (m + 1) → ℂ) (l : Fin (m + 1) → LoopIndex → ℂ) :
    Cubic.mulLin P (∑ i, w i * c i) (fun a => ∑ i, w i * l i a) =
      QED.TwoLoop.LimitCovariance.qsum Finset.univ w fun i => Cubic.mulLin P (c i) (l i) := by
  simp only [Cubic.mulLin, QED.TwoLoop.LimitCovariance.qsum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun _ _ => by ring
  all_goals
    funext
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem ehat_qsum (n : ℕ) {ι : Type*} (s : Finset ι) (w : ι → ℂ) (Q : ι → LoopQuartic)
    (A : Matrix (Fin 2) (Fin 2) ℝ) (X : LoopIndex → ℂ) (W : ℂ) :
    ehat n (QED.TwoLoop.LimitCovariance.qsum s w Q) A X W = ∑ i ∈ s, w i * ehat n (Q i) A X W := by
  simp only [ehat, QED.TwoLoop.LimitCovariance.evalC_qsum,
    QED.TwoLoop.LimitCovariance.contractTwo_qsum, QED.TwoLoop.LimitCovariance.contractFour_qsum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **The combined insertion splits into lines**: `Ê[P·∑ᵢ zᵢ ∂Dᵢ] = ∑ᵢ zᵢ Ê[P·∂Dᵢ]`. -/
theorem ehat_mulLin_sum (n : ℕ) (P : LoopQuartic) (w c : Fin (m + 1) → ℂ)
    (l : Fin (m + 1) → LoopIndex → ℂ) (A : Matrix (Fin 2) (Fin 2) ℝ) (X : LoopIndex → ℂ)
    (W : ℂ) :
    ehat n (Cubic.mulLin P (∑ i, w i * c i) (fun a => ∑ i, w i * l i a)) A X W =
      ∑ i, w i * ehat n (Cubic.mulLin P (c i) (l i)) A X W := by
  rw [mulLin_sum, ehat_qsum]

end QED.GradedProof.WI2

end
