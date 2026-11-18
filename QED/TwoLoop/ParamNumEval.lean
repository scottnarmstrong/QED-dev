/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroExplicitQuartic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Evaluating the canonical parametric numerator: linearity and the shifted expansion

Infrastructure for the link of the explicit `q → 0` class values
(`QED.TwoLoop.PauliZeroExplicit.openZero`) to the Feynman-parameter integrands of
`docs/TWO-LOOP-UNITS.md` (section 8, stage 1). The class values are written through the canonical
parametric numerator `paramNumOf F α p M x = T₁ + T₂ V + T₃ V²` of a numerator function `F`
(`QED.TwoLoop.PauliZeroExplicit.paramNumOf`), with
`T₁ = (m-4)! U⁻² F(-S)`, `T₂ = (m-5)!/2 U⁻² ∑ Hₐ_b(-S) Gₐ_b`, `T₃ = (m-6)!/4 U⁻² ∑ Rₐ_bcd Πₐ_bcd(G)`,
`S` the loop shift and `G = loopMetricInv A` the contraction tensor. This file makes it computable:

* **linearity** (`paramNumOf_sum`, `paramNumOf_add`, `paramNumOf_const_mul`): for numerators with
  quartic representations, `paramNumOf` is linear in the numerator function;
* **the shifted expansion** (`paramNumOf_eq_shifted`): if `Q'` is any quartic representing the
  shifted numerator `D ↦ F(-S + D)`, then
  `paramNumOf F = U⁻² ((m-4)! Q'₀ + (m-5)!/2 · V ∑ₐ_b Q'ₐ_b Gₐ_b + (m-6)!/4 · V² ∑ Q'ₐ_bcd Πₐ_bcd(G))`,
  with `Q'₀, Q'ₐ_b, Q'ₐ_bcd` the constant, quadratic and quartic coefficients of `Q'`: the
  Gaussian-moment (Wick) rule `ℓ ℓ → G` at the shifted point. This is the form used for the
  chains of electron propagators in `QED/TwoLoop/ParamNumEvalChain.lean`.

The proof transports the even-part identity of a quartic along the translation by `-S`
(`hessForm_shift`, `quartPart_shift`), and uses the polarization lemmas of
`QED/TwoLoop/PauliZeroExplicitQuartic.lean`.
-/

@[expose] public section

open Complex Matrix

namespace QED.TwoLoop.ParamNumEval

open QED.Integration.TwoLoop QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.PauliZeroLimit
open QED.TwoLoop.LimitCovariance
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### Linearity -/

section Linear

variable {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) (x : Fin m → ℝ)

/-- Linear combinations of numerators with quartic representations have one. -/
theorem exists_quartic_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    {F : ι → (Fin 2 → Fin 4 → ℝ) → ℂ} (hF : ∀ k, ∃ Q : LoopQuartic, Q.eval = F k) :
    ∃ Q : LoopQuartic, Q.eval = fun ℓ => ∑ k ∈ s, c k * F k ℓ := by
  choose Q hQ using hF
  refine ⟨qsum s c Q, funext fun ℓ => ?_⟩
  rw [eval_qsum]
  simp only [hQ]

/-- **`paramNumOf` is linear** on numerators with quartic representations. -/
theorem paramNumOf_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    {F : ι → (Fin 2 → Fin 4 → ℝ) → ℂ} (hF : ∀ k, ∃ Q : LoopQuartic, Q.eval = F k) :
    paramNumOf (fun ℓ => ∑ k ∈ s, c k * F k ℓ) α p M x =
      ∑ k ∈ s, c k * paramNumOf (F k) α p M x := by
  choose Q hQ using hF
  have hE : (qsum s c Q).eval = fun ℓ => ∑ k ∈ s, c k * F k ℓ := by
    funext ℓ
    rw [eval_qsum]
    simp only [hQ]
  rw [paramNumOf_eq hE, paramNum_qsum]
  exact Finset.sum_congr rfl fun k _ => by rw [paramNumOf_eq (hQ k)]

theorem paramNumOf_add {F G : (Fin 2 → Fin 4 → ℝ) → ℂ} (hF : ∃ Q : LoopQuartic, Q.eval = F)
    (hG : ∃ Q : LoopQuartic, Q.eval = G) :
    paramNumOf (fun ℓ => F ℓ + G ℓ) α p M x = paramNumOf F α p M x + paramNumOf G α p M x := by
  have h := paramNumOf_sum α p M x (Finset.univ : Finset (Fin 2)) (fun _ => 1)
    (F := ![F, G]) (fun k => by fin_cases k <;> assumption)
  simpa [Fin.sum_univ_two] using h

theorem paramNumOf_const_mul (c : ℂ) {F : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (hF : ∃ Q : LoopQuartic, Q.eval = F) :
    paramNumOf (fun ℓ => c * F ℓ) α p M x = c * paramNumOf F α p M x := by
  have h := paramNumOf_sum α p M x (Finset.univ : Finset (Fin 1)) (fun _ => c)
    (F := fun _ => F) (fun _ => hF)
  simpa using h

end Linear

/-! ### Translation of the even part -/

section Shift

open NumeratorCongr

variable {Q Q' : LoopQuartic} {X₀ : Fin 2 → Fin 4 → ℝ}

theorem eval_zero (Q : LoopQuartic) : Q.eval 0 = Q.const := by
  simp [LoopQuartic.eval, LoopQuartic.evalC, loopComp]

theorem hessForm_add_quartPart_shift (h : ∀ D, Q'.eval D = Q.eval (X₀ + D))
    (δ : Fin 2 → Fin 4 → ℝ) :
    hessForm Q X₀ δ + Q.quartPart (loopComp δ) =
      hessForm Q' 0 δ + Q'.quartPart (loopComp δ) := by
  have e1 := Q.eval_add_add_eval_sub X₀ δ
  have e2 := Q'.eval_add_add_eval_sub 0 δ
  have h1 : Q'.eval (0 + δ) = Q.eval (X₀ + δ) := by rw [zero_add, h]
  have h2 : Q'.eval (0 - δ) = Q.eval (X₀ - δ) := by
    rw [zero_sub, h, sub_eq_add_neg]
  have h0 : Q'.eval 0 = Q.eval X₀ := by rw [h, add_zero]
  rw [h1, h2, h0] at e2
  unfold hessForm
  linear_combination (e2 - e1) / 2

/-- **The quadratic form of `H(X₀)` is transported by the translation.** -/
theorem hessForm_shift (h : ∀ D, Q'.eval D = Q.eval (X₀ + D)) (δ : Fin 2 → Fin 4 → ℝ) :
    hessForm Q X₀ δ = hessForm Q' 0 δ := by
  have e1 := hessForm_add_quartPart_shift h δ
  have e2 := hessForm_add_quartPart_shift h ((2 : ℝ) • δ)
  rw [hessForm_two_smul, hessForm_two_smul, quartPart_two_smul, quartPart_two_smul] at e2
  linear_combination (16 * e1 - e2) / 12

/-- **The quartic part is invariant under translation.** -/
theorem quartPart_shift (h : ∀ D, Q'.eval D = Q.eval (X₀ + D)) (δ : Fin 2 → Fin 4 → ℝ) :
    Q.quartPart (loopComp δ) = Q'.quartPart (loopComp δ) := by
  have e1 := hessForm_add_quartPart_shift h δ
  rw [hessForm_shift h δ] at e1
  linear_combination e1

/-- The pure quartic part of a quartic, as a quartic. -/
def quartOnly (Q : LoopQuartic) : LoopQuartic := ⟨0, 0, 0, 0, Q.quart⟩

theorem eval_quartOnly (Q : LoopQuartic) (δ : Fin 2 → Fin 4 → ℝ) :
    (quartOnly Q).eval δ = Q.quartPart (loopComp δ) := by
  simp [quartOnly, LoopQuartic.eval, LoopQuartic.evalC, LoopQuartic.quartPart]

theorem contractFour_quartOnly (Q : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (quartOnly Q).contractFour A = Q.contractFour A := rfl

theorem contractTwo_shift (h : ∀ D, Q'.eval D = Q.eval (X₀ + D)) {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : Aᵀ = A) : Q.contractTwo A (loopComp X₀) = Q'.contractTwo A (loopComp 0) := by
  unfold LoopQuartic.contractTwo
  refine sum_mul_eq_of_quadForm (fun y => ?_) (NumeratorCongr.loopMetricInv_symm hA)
  have := hessForm_shift h (ofIndex y)
  simpa only [hessForm, loopComp_ofIndex] using this

theorem contractFour_shift (h : ∀ D, Q'.eval D = Q.eval (X₀ + D)) {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : Aᵀ = A) : Q.contractFour A = Q'.contractFour A := by
  rw [← contractFour_quartOnly Q, ← contractFour_quartOnly Q']
  refine contractFour_congr (funext fun δ => ?_) hA
  rw [eval_quartOnly, eval_quartOnly, quartPart_shift h]

/-- At the origin the Hessian coefficients are the quadratic coefficients. -/
theorem contractTwo_zero (Q : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Q.contractTwo A (loopComp 0) =
      ∑ a, ∑ b, Q.quad a b * ((loopMetricInv A a b : ℝ) : ℂ) := by
  have h0 : loopComp (0 : Fin 2 → Fin 4 → ℝ) = 0 := by
    funext a
    simp [loopComp]
  simp [LoopQuartic.contractTwo, LoopQuartic.hess, h0]

end Shift

/-! ### The shifted expansion -/

section Expansion

variable {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) (x : Fin m → ℝ)

/-- **The shifted expansion of the canonical parametric numerator.** If `F` has a quartic
representation and `Q'` represents the shifted numerator `D ↦ F(-S + D)` (`S` the loop shift), then
`paramNumOf F = U⁻² ((m-4)! Q'₀ + (m-5)!/2 · V ∑ₐ_b Q'ₐ_b Gₐ_b + (m-6)!/4 · V² ∑ Q'ₐ_bcd Πₐ_bcd(G))`
with `G = loopMetricInv A`. -/
theorem paramNumOf_eq_shifted {F : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (hF : ∃ Q : LoopQuartic, Q.eval = F) {Q' : LoopQuartic}
    (hQ' : ∀ D, Q'.eval D = F (-loopShift α p (simplexPoint x) + D)) :
    paramNumOf F α p M x =
      ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
        (((m - 4).factorial : ℂ) * Q'.const +
          ((m - 5).factorial : ℂ) / 2 *
            (∑ a, ∑ b, Q'.quad a b *
              ((loopMetricInv (symanzikMatrix α (simplexPoint x)) a b : ℝ) : ℂ)) *
            ((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) +
          ((m - 6).factorial : ℂ) / 4 * Q'.contractFour (symanzikMatrix α (simplexPoint x)) *
            ((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) ^ 2) := by
  obtain ⟨Q, hQ⟩ := hF
  have hsh : ∀ D, Q'.eval D = Q.eval (-loopShift α p (simplexPoint x) + D) := fun D => by
    rw [hQ', hQ]
  have hA := symanzikMatrix_transpose α (simplexPoint x)
  have h0 : Q.eval (-loopShift α p (simplexPoint x)) = Q'.const := by
    rw [← eval_zero, hsh, add_zero]
  rw [paramNumOf_eq hQ]
  simp only [paramNum, ClassLimit.coeffOne, ClassLimit.coeffTwo, ClassLimit.coeffThree]
  rw [h0, contractTwo_shift hsh hA, contractTwo_zero, contractFour_shift hsh hA]
  ring

end Expansion

end QED.TwoLoop.ParamNumEval

end
