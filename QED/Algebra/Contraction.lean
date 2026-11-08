/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.Gordon
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Contraction identities

The gamma-matrix contraction identities of the primary source's eqs.
(47.18)–(47.21), specialized to `d = 4` (the project works in four dimensions;
decision D-5). In the mostly-plus conventions of `docs/CONVENTIONS.md`:

* `QED.Dirac.contract_one`: `γ^μ γ_μ = -4`;
* `QED.Dirac.contract_slash`: `γ^μ a̸ γ_μ = 2 a̸`;
* `QED.Dirac.contract_slash_slash`: `γ^μ a̸ b̸ γ_μ = 4 (a·b)`;
* `QED.Dirac.contract_slash_slash_slash`: `γ^μ a̸ b̸ c̸ γ_μ = 2 c̸ b̸ a̸`.

They follow the source's route: they are derived from the anticommutator
`{γ_μ, a̸} = -2 a_μ` through the recursion
`γ^μ X a̸ γ_μ = -(γ^μ X γ_μ) a̸ - 2 a̸ X` (`QED.Dirac.contract_mul_slash`).
The anticommutator `{a̸, b̸} = -2 (a·b)` is `QED.Dirac.slash_anticomm`.
-/

@[expose] public section

open Matrix Complex

namespace QED.Dirac

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- The lowered gamma matrices `γ_μ = g_{μν} γ^ν`. -/
noncomputable def gammaLower (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ ν, ((Minkowski.metric μ ν : ℝ) : ℂ) • gamma ν

/-- Componentwise, `γ_μ = (-γ^0, γ^1, γ^2, γ^3)`. -/
theorem gammaLower_eq : gammaLower = ![-gamma 0, gamma 1, gamma 2, gamma 3] := by
  funext μ; fin_cases μ <;> simp [gammaLower, Minkowski.metric, Fin.sum_univ_four]

/-- `{γ^μ, a̸} = -2 a^μ`. -/
theorem gamma_slash_anticomm (μ : Fin 4) (a : Fin 4 → ℝ) :
    gamma μ * slash a + slash a * gamma μ = ((-2 * a μ : ℝ) : ℂ) • 𝟙 := by
  rw [gamma_mul_slash, slash_mul_gamma]
  push_cast
  module

/-- `{γ_μ, a̸} = -2 a_μ`. -/
theorem gammaLower_slash_anticomm (μ : Fin 4) (a : Fin 4 → ℝ) :
    gammaLower μ * slash a + slash a * gammaLower μ =
      ((-2 * Minkowski.lower a μ : ℝ) : ℂ) • 𝟙 := by
  rw [gammaLower_eq, Minkowski.lower_eq]
  fin_cases μ
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, neg_mul, mul_neg]
    rw [← neg_add, gamma_slash_anticomm]; push_cast; module
  all_goals
    simp only [Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_one, Matrix.cons_val]
    rw [gamma_slash_anticomm]

/-- `γ^μ γ_μ = -4` ((47.18) at `d = 4`). -/
theorem contract_one : ∑ μ, gamma μ * gammaLower μ = (-4 : ℂ) • 𝟙 := by
  rw [gammaLower_eq]
  simp only [Fin.sum_univ_four]
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma] <;> norm_num

/-- `γ^μ a_μ = a̸`. -/
theorem sum_lower_smul_gamma_mul (a : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ μ, ((Minkowski.lower a μ : ℝ) : ℂ) • (gamma μ * X) = slash a * X := by
  simp only [slash, Finset.sum_mul, smul_mul_assoc]

/-- The contraction recursion: `γ^μ X a̸ γ_μ = -(γ^μ X γ_μ) a̸ - 2 a̸ X`. -/
theorem contract_mul_slash (X : Matrix (Fin 4) (Fin 4) ℂ) (a : Fin 4 → ℝ) :
    ∑ μ, gamma μ * X * slash a * gammaLower μ =
      -((∑ μ, gamma μ * X * gammaLower μ) * slash a) - (2 : ℂ) • (slash a * X) := by
  have h : ∀ μ, gamma μ * X * slash a * gammaLower μ =
      -(gamma μ * X * gammaLower μ * slash a)
        - (2 : ℂ) • (((Minkowski.lower a μ : ℝ) : ℂ) • (gamma μ * X)) := by
    intro μ
    have e : slash a * gammaLower μ =
        ((-2 * Minkowski.lower a μ : ℝ) : ℂ) • 𝟙 - gammaLower μ * slash a := by
      rw [← gammaLower_slash_anticomm]; abel
    calc gamma μ * X * slash a * gammaLower μ
        = gamma μ * X * (slash a * gammaLower μ) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [e, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
        push_cast
        module
  rw [Finset.sum_congr rfl fun μ _ => h μ, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.smul_sum, sum_lower_smul_gamma_mul, Finset.sum_mul]

/-- `γ^μ a̸ γ_μ = 2 a̸` ((47.19) at `d = 4`). -/
theorem contract_slash (a : Fin 4 → ℝ) :
    ∑ μ, gamma μ * slash a * gammaLower μ = (2 : ℂ) • slash a := by
  have := contract_mul_slash 𝟙 a
  simp only [Matrix.mul_one] at this
  rw [this, contract_one, smul_mul_assoc, Matrix.one_mul]
  module

/-- `{a̸, b̸} = -2 (a·b)`. -/
theorem slash_anticomm (a b : Fin 4 → ℝ) :
    slash a * slash b + slash b * slash a = ((-2 * Minkowski.dot a b : ℝ) : ℂ) • 𝟙 := by
  have ha : slash a = ∑ μ, ((Minkowski.lower a μ : ℝ) : ℂ) • gamma μ := rfl
  rw [ha, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  simp only [smul_mul_assoc, mul_smul_comm, ← smul_add, gamma_slash_anticomm, smul_smul]
  rw [← Finset.sum_smul, Minkowski.dot_eq_sum_lower]
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun μ _ => by push_cast; ring

/-- `γ^μ a̸ b̸ γ_μ = 4 (a·b)` ((47.20) at `d = 4`). -/
theorem contract_slash_slash (a b : Fin 4 → ℝ) :
    ∑ μ, gamma μ * slash a * slash b * gammaLower μ =
      ((4 * Minkowski.dot a b : ℝ) : ℂ) • 𝟙 := by
  rw [contract_mul_slash, contract_slash, smul_mul_assoc,
    show -((2 : ℂ) • (slash a * slash b)) - (2 : ℂ) • (slash b * slash a)
      = (-2 : ℂ) • (slash a * slash b + slash b * slash a) by module,
    slash_anticomm, smul_smul]
  congr 1
  push_cast
  ring

/-- `γ^μ a̸ b̸ c̸ γ_μ = 2 c̸ b̸ a̸` ((47.21) at `d = 4`). -/
theorem contract_slash_slash_slash (a b c : Fin 4 → ℝ) :
    ∑ μ, gamma μ * slash a * slash b * slash c * gammaLower μ =
      (2 : ℂ) • (slash c * slash b * slash a) := by
  have h := contract_mul_slash (slash a * slash b) c
  simp only [← Matrix.mul_assoc] at h
  rw [h, contract_slash_slash, smul_mul_assoc, Matrix.one_mul]
  have hab : slash a * slash b = ((-2 * Minkowski.dot a b : ℝ) : ℂ) • 𝟙 - slash b * slash a := by
    rw [← slash_anticomm]; abel
  rw [Matrix.mul_assoc (slash c) (slash a) (slash b), hab, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.mul_one, ← Matrix.mul_assoc]
  push_cast
  module

end QED.Dirac

end
