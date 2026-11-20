/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: polynomials with coefficient vectors

Helper level (no frozen statement). Generic calculus for the generated rational antiderivatives
of the `ρ_X` closed form (scratch `stageK/STATUS.md`, session 26+): a polynomial
`formXPol c z = ∑ᵢ cᵢ zⁱ` with coefficient vector `c`, its derivative vector `formXPolD`
(**`hasDerivAt_formXPol`**), and the quotient by a denominator `c L₁^a L₂^b`
(**`formX_hasDerivAt_den`**, **`formX_hasDerivAt_polDiv`**).
-/

@[expose] public section

namespace QED.ChainProof.SetCK

/-- A polynomial with coefficient vector `c`. -/
noncomputable def formXPol {n : ℕ} (c : Fin n → ℝ) (z : ℝ) : ℝ := ∑ i, c i * z ^ (i : ℕ)

/-- The coefficient vector of the derivative. -/
def formXPolD {n : ℕ} (c : Fin (n + 1) → ℝ) : Fin n → ℝ := fun i => ((i : ℕ) + 1 : ℝ) * c i.succ

theorem hasDerivAt_formXPol {n : ℕ} (c : Fin (n + 1) → ℝ) (z : ℝ) :
    HasDerivAt (formXPol c) (formXPol (formXPolD c) z) z := by
  have h : HasDerivAt (fun y => ∑ i : Fin (n + 1), c i * y ^ (i : ℕ))
      (∑ i : Fin (n + 1), c i * ((i : ℕ) * z ^ ((i : ℕ) - 1))) z :=
    HasDerivAt.fun_sum fun i _ => (hasDerivAt_pow (i : ℕ) z).const_mul (c i)
  refine h.congr_deriv ?_
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.cast_zero, zero_mul, mul_zero, zero_add, Fin.val_succ,
    Nat.add_sub_cancel, formXPol, formXPolD]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

theorem continuous_formXPol {n : ℕ} (c : Fin n → ℝ) : Continuous (formXPol c) := by
  unfold formXPol
  fun_prop

/-- The derivative of a denominator `c L₁^a L₂^b`. -/
theorem formX_hasDerivAt_den (c : ℝ) (a b : ℕ) {L₁ L₂ : ℝ → ℝ} {p₁ p₂ y : ℝ}
    (h₁ : HasDerivAt L₁ p₁ y) (h₂ : HasDerivAt L₂ p₂ y) :
    HasDerivAt (fun z => c * L₁ z ^ a * L₂ z ^ b)
      (c * ((a * L₁ y ^ (a - 1) * p₁) * L₂ y ^ b + L₁ y ^ a * (b * L₂ y ^ (b - 1) * p₂))) y := by
  have h := ((h₁.pow a).const_mul c).mul (h₂.pow b)
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply]
  ring

/-- The quotient rule for `formXPol c / D`. -/
theorem formX_hasDerivAt_polDiv {n : ℕ} (c : Fin (n + 1) → ℝ) {D : ℝ → ℝ} {D' y : ℝ}
    (hD : HasDerivAt D D' y) (h0 : D y ≠ 0) :
    HasDerivAt (fun z => formXPol c z / D z)
      ((formXPol (formXPolD c) y * D y - formXPol c y * D') / D y ^ 2) y :=
  (hasDerivAt_formXPol c y).div hD h0

end QED.ChainProof.SetCK

end
