/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.Dirac
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Products of gamma matrices and the Gordon identity

Identities of the primary source's section 38, in the conventions of
`docs/CONVENTIONS.md`:

* `QED.Dirac.gamma_mul_gamma`: `γ^μ γ^ν = -g^{μν} - 2i S^{μν}`, from the Clifford
  relation (36.9) and the definition (40.3) of `S^{μν}`;
* `QED.Dirac.gamma_mul_slash` and `QED.Dirac.slash_mul_gamma`: eqs. (38.19)
  and (38.20);
* `QED.Dirac.gordon`: the Gordon identity (38.18).

The Gordon identity is stated for an arbitrary column vector `u` with
`(p̸ + m) u = 0` and an arbitrary row vector `w` with `w (p̸' + m) = 0`. The
on-shell spinors `u_s(p)` and their Dirac adjoints `ū_{s'}(p')` are particular
cases (eqs. (38.1) and (38.16)).
-/

@[expose] public section

open Matrix Complex

namespace QED.Dirac

/-- `γ^μ γ^ν = -g^{μν} - 2i S^{μν}`. -/
theorem gamma_mul_gamma (μ ν : Fin 4) :
    gamma μ * gamma ν =
      ((-Minkowski.metric μ ν : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - (2 * I) • lorentzGen μ ν := by
  have h := gamma_anticomm μ ν
  unfold lorentzGen
  rw [smul_smul]
  have h2 : (2 * I * (I / 4)) = (-1/2 : ℂ) := by
    field_simp; rw [I_sq]; ring
  rw [h2]
  have : ((-Minkowski.metric μ ν : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) =
      (1/2 : ℂ) • (gamma μ * gamma ν + gamma ν * gamma μ) := by
    rw [h, smul_smul]; congr 1; push_cast; ring
  rw [this]
  module

/-- `g^{μν} p_ν = p^μ`. -/
theorem sum_metric_mul_lower (p : Fin 4 → ℝ) (μ : Fin 4) :
    ∑ ν, Minkowski.metric μ ν * Minkowski.lower p ν = p μ := by
  fin_cases μ <;> simp [Minkowski.metric, Minkowski.lower_eq]

/-- `S^{νμ} = -S^{μν}`. -/
theorem lorentzGen_antisymm (μ ν : Fin 4) : lorentzGen ν μ = -lorentzGen μ ν := by
  unfold lorentzGen
  rw [← smul_neg, neg_sub]

/-- (38.19): `γ^μ p̸ = -p^μ - 2i S^{μν} p_ν`. -/
theorem gamma_mul_slash (μ : Fin 4) (p : Fin 4 → ℝ) :
    gamma μ * slash p =
      -(((p μ : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ))
        - (2 * I) • ∑ ν, ((Minkowski.lower p ν : ℝ) : ℂ) • lorentzGen μ ν := by
  simp only [slash, Finset.mul_sum, mul_smul_comm, gamma_mul_gamma, smul_sub, Finset.sum_sub_distrib,
    smul_smul, Finset.smul_sum]
  have h1 : ∑ ν, (((Minkowski.lower p ν : ℝ) : ℂ) * ((-Minkowski.metric μ ν : ℝ) : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
      = -(((p μ : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
    rw [← Finset.sum_smul, ← neg_smul]
    congr 1
    rw [← sum_metric_mul_lower p μ, Complex.ofReal_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun ν _ => by push_cast; ring
  rw [h1]
  congr 1
  exact Finset.sum_congr rfl fun ν _ => by rw [mul_comm]

/-- (38.20): `p̸ γ^μ = -p^μ + 2i S^{μν} p_ν`. -/
theorem slash_mul_gamma (μ : Fin 4) (p : Fin 4 → ℝ) :
    slash p * gamma μ =
      -(((p μ : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ))
        + (2 * I) • ∑ ν, ((Minkowski.lower p ν : ℝ) : ℂ) • lorentzGen μ ν := by
  simp only [slash, Finset.sum_mul, smul_mul_assoc, gamma_mul_gamma, smul_sub, Finset.sum_sub_distrib,
    smul_smul, Finset.smul_sum]
  have h1 : ∑ ν, (((Minkowski.lower p ν : ℝ) : ℂ) * ((-Minkowski.metric ν μ : ℝ) : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
      = -(((p μ : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
    rw [← Finset.sum_smul, ← neg_smul]
    congr 1
    rw [← sum_metric_mul_lower p μ, Complex.ofReal_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun ν _ => by rw [Minkowski.metric_symm]; push_cast; ring
  rw [h1, sub_eq_add_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun ν _ => by rw [lorentzGen_antisymm]; module

/-- The Gordon identity (38.18): if `(p̸ + m) u = 0` and `w (p̸' + m) = 0`, then
`2m w γ^μ u = w [(p' + p)^μ - 2i S^{μν} (p' - p)_ν] u`. -/
theorem gordon (m : ℝ) (p p' : Fin 4 → ℝ) (u w : Fin 4 → ℂ)
    (hu : slash p *ᵥ u = -((m : ℂ) • u)) (hw : w ᵥ* slash p' = -((m : ℂ) • w)) (μ : Fin 4) :
    (2 * m : ℂ) * (w ⬝ᵥ (gamma μ *ᵥ u)) =
      w ⬝ᵥ ((((p' μ + p μ : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
        - (2 * I) • ∑ ν, ((Minkowski.lower p' ν - Minkowski.lower p ν : ℝ) : ℂ) • lorentzGen μ ν) *ᵥ u) := by
  have key : gamma μ * slash p + slash p' * gamma μ =
      -((((p' μ + p μ : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ))
        - (2 * I) • ∑ ν, ((Minkowski.lower p' ν - Minkowski.lower p ν : ℝ) : ℂ) • lorentzGen μ ν) := by
    rw [gamma_mul_slash, slash_mul_gamma]
    simp only [push_cast, sub_smul, Finset.sum_sub_distrib, smul_sub, add_smul]
    abel
  have lhs : w ⬝ᵥ ((gamma μ * slash p + slash p' * gamma μ) *ᵥ u)
      = -(2 * m : ℂ) * (w ⬝ᵥ (gamma μ *ᵥ u)) := by
    rw [Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_neg,
      Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec w (slash p'), hw,
      dotProduct_neg, dotProduct_smul, neg_dotProduct, smul_dotProduct, smul_eq_mul]
    ring
  rw [key, Matrix.neg_mulVec, dotProduct_neg] at lhs
  linear_combination lhs

end QED.Dirac

end
