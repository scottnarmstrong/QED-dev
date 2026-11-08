/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.Minkowski
public import QED.Frozen.Algebra.Gamma
public import QED.Frozen.Algebra.Slash
public import QED.Frozen.Algebra.LorentzGen
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormMatMul

/-!
# Dirac matrices in the Weyl representation

The gamma matrices of the project's conventions (`docs/CONVENTIONS.md`,
decision D-7), following the primary source:

* the Weyl representation `γ^μ = [[0, σ^μ], [σ̄^μ, 0]]` with `σ^μ = (I, σ⃗)` and
  `σ̄^μ = (I, -σ⃗)` (eqs. (36.7)–(36.8));
* the Clifford relation `{γ^μ, γ^ν} = -2 g^{μν}` for the mostly-plus metric
  (eq. (36.9));
* the matrix `β = [[0, I], [I, 0]]` of the Dirac adjoint `Ψ̄ = Ψ† β`
  (eq. (38.8));
* the Lorentz generators `S^{μν} = (i/4) [γ^μ, γ^ν]` (eq. (40.3)).

The gamma matrices `QED.Dirac.gamma` and the slash `QED.Dirac.slash` (decision D-12) and
the Lorentz generators `QED.Dirac.lorentzGen` (decision D-14) are author-approved frozen
definitions in `QED/Frozen/Algebra/`; this module re-exports them. The slash follows the source's definition (37.24).

## Main statements

* `QED.Dirac.gamma_anticomm`: the Clifford relation.
* `QED.Dirac.slash_mul_slash`: `p̸ p̸ = -(p·p)` for `p̸ = γ^μ p_μ`.
* `QED.Dirac.beta_eq_gamma_zero`: `β` is numerically `γ^0`.
* `QED.Dirac.beta_mul_conjTranspose_gamma_mul_beta`: `β (γ^μ)† β = γ^μ`.
-/

@[expose] public section

open Matrix Complex

namespace QED.Dirac

/-- The matrix `β` of the Dirac adjoint `Ψ̄ = Ψ† β` (eq. (38.8)). -/
def beta : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

/-- The slash is additive: `(a + b)̸ = a̸ + b̸`. -/
theorem slash_add (a b : Fin 4 → ℝ) : slash (a + b) = slash a + slash b := by
  simp only [slash, Minkowski.lower, Pi.add_apply, mul_add, Finset.sum_add_distrib,
    Complex.ofReal_add, add_smul]

/-- The slash is homogeneous: `(c a)̸ = c a̸` for real `c`. -/
theorem slash_smul (c : ℝ) (a : Fin 4 → ℝ) : slash (c • a) = (c : ℂ) • slash a := by
  have h : ∀ μ, Minkowski.lower (c • a) μ = c * Minkowski.lower a μ := fun μ => by
    simp only [Minkowski.lower, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => by ring
  simp only [slash, h, Complex.ofReal_mul, Finset.smul_sum, smul_smul]

/-- The Clifford relation `{γ^μ, γ^ν} = -2 g^{μν}` (eq. (36.9)). -/
theorem gamma_anticomm (μ ν : Fin 4) :
    gamma μ * gamma ν + gamma ν * gamma μ =
      ((-2 * Minkowski.metric μ ν : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  fin_cases μ <;> fin_cases ν <;>
    simp only [gamma, Minkowski.metric, norm_matmul] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> ring_nf

theorem beta_eq_gamma_zero : beta = gamma 0 := rfl

/-- `β (γ^μ)† β = γ^μ`: the gamma matrices are self-adjoint for the Dirac
adjoint. -/
theorem beta_mul_conjTranspose_gamma_mul_beta (μ : Fin 4) :
    beta * (gamma μ)ᴴ * beta = gamma μ := by
  fin_cases μ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp only [beta, gamma, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four] <;>
    simp

/-- `p̸ p̸ = -(p·p)`. Proved by direct computation; it is also a consequence of
`gamma_anticomm`. -/
theorem slash_mul_slash (p : Fin 4 → ℝ) :
    slash p * slash p = ((-Minkowski.dot p p : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [Minkowski.dot_eq]
  simp only [slash, Minkowski.lower_eq, Fin.sum_univ_four]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, Matrix.mul_apply, Fin.sum_univ_four] <;> ring_nf <;> simp [I_sq] <;> ring

end QED.Dirac

end
