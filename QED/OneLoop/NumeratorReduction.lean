/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.OneLoop.VertexAlgebra
public import QED.Algebra.Dirac
import QED.Algebra.Contraction
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
# Reduction of the one-loop vertex numerator

The Dirac numerator `g_{νρ} γ^ρ (m - (p̸' + ℓ̸)) γ^μ (m - (p̸ + ℓ̸)) γ^ν` of the primary source's
(62.40), its gamma-matrix contraction at `d = 4` (the project form of (63.8)–(63.10)), and its
reduction between on-shell spinors after the Feynman-parameter shift (the project form of
(63.13)–(63.17)), in the conventions of `docs/CONVENTIONS.md`.

The project's shift is `ℓ = -K` with `K = y (x p' + (1 - x) p)`, so that
`p' + ℓ = (1 - x₁) p' - x₂ p` and `p + ℓ = (1 - x₂) p - x₁ p'` with `x₁ = y x`, `x₂ = y (1 - x)`
and `x₃ = 1 - y`; the momentum transfer is `q = p' - p`. The source's shifted momentum (62.43)
is `ℓ + x₁ p + x₂ p'`, so its `x₁` and `x₂` are our `x₂` and `x₁`. The coefficients of `γ^μ`
and of `S^{μν} q_ν` are symmetric under this swap; only the coefficient of `(p' - p)^μ` changes
sign.

## Main definitions

* `QED.OneLoop.vertexNumeratorMatrix`: the numerator as a matrix; its entries are
  `QED.OneLoop.vertexNumerator` (`vertexNumerator_eq_vertexNumeratorMatrix_apply`).
* `QED.OneLoop.numeratorAsym`: the coefficient of `(p' - p)^μ (w u)` in the on-shell reduction.

## Main statements

* `QED.OneLoop.vertexNumeratorMatrix_eq`: the contraction
  `γ_ν (m - a̸) γ^μ (m - b̸) γ^ν = 2m² γ^μ - 4m (a + b)^μ + 2 b̸ γ^μ a̸` ((63.10)).
* `QED.OneLoop.sandwich_vertexNumeratorMatrix_neg_shift`: between `w` with `w p̸' = -m w` and
  `u` with `p̸ u = -m u`, and on the mass shell, the shifted numerator reduces to
  `2[(1 - 4x₃ + x₃²) m² - (x₃ + x₁x₂) q²] γ^μ - 4im (x₃ - x₃²) S^{μν} q_ν` plus an
  `x ↔ 1 - x` antisymmetric multiple of `(p' - p)^μ` ((63.14) and (63.17)).
* `QED.OneLoop.numeratorAsym_one_sub`: that multiple is antisymmetric under `x ↦ 1 - x`, so it
  integrates to zero against the symmetric denominator (63.15).
-/

@[expose] public section

open Matrix Complex

namespace QED.OneLoop

/-- Matrix form of the Dirac numerator of (62.40). -/
noncomputable def vertexNumeratorMatrix (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ ν, ∑ ρ, ((Minkowski.metric ν ρ : ℝ) : ℂ) •
    (Dirac.gamma ρ * ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (p' + ℓ)) *
      Dirac.gamma μ * ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (p + ℓ)) *
      Dirac.gamma ν)

/-- The entries of `vertexNumeratorMatrix` are the entries `vertexNumerator`. -/
theorem vertexNumerator_eq_vertexNumeratorMatrix_apply (m : ℝ) (p' p : Fin 4 → ℝ)
    (μ : Fin 4) (ℓ : Fin 4 → ℝ) (i j : Fin 4) :
    vertexNumerator m p' p μ ℓ i j = vertexNumeratorMatrix m p' p μ ℓ i j := by
  simp only [vertexNumerator, vertexNumeratorMatrix, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]

/-! ### Contraction -/

/-- `γ^μ` is the slash of the vector with covariant components `δ_{νμ}`. -/
private theorem gamma_eq_slash (μ : Fin 4) :
    Dirac.gamma μ = Dirac.slash (Minkowski.metric μ μ • Pi.single μ 1) := by
  fin_cases μ <;>
    simp [Dirac.slash, Minkowski.lower_eq, Fin.sum_univ_four, Minkowski.metric]

private theorem dot_metric_smul_single (μ : Fin 4) (a : Fin 4 → ℝ) :
    Minkowski.dot (Minkowski.metric μ μ • Pi.single μ 1) a = a μ := by
  rw [Minkowski.dot_eq]
  fin_cases μ <;> simp [Minkowski.metric]

/-- `g_{νρ} γ^ρ M γ^ν = γ^ρ M γ_ρ`. -/
private theorem sum_metric_smul_gamma_mul_mul (M : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ ν, ∑ ρ, ((Minkowski.metric ν ρ : ℝ) : ℂ) • (Dirac.gamma ρ * M * Dirac.gamma ν) =
      ∑ ρ, Dirac.gamma ρ * M * Dirac.gammaLower ρ := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [Dirac.gammaLower, Finset.mul_sum, mul_smul_comm]
  exact Finset.sum_congr rfl fun ν _ => by rw [Minkowski.metric_symm]

/-- Contraction of `(m - a̸) γ^μ (m - b̸)`. -/
private theorem contract_mass_sub_slash (m : ℝ) (a b : Fin 4 → ℝ) (μ : Fin 4) :
    ∑ ρ, Dirac.gamma ρ * (((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash a) *
        Dirac.gamma μ * ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash b)) *
        Dirac.gammaLower ρ =
      ((2 * m ^ 2 : ℝ) : ℂ) • Dirac.gamma μ
        - ((4 * m * (a μ + b μ) : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
        + (2 : ℂ) • (Dirac.slash b * Dirac.gamma μ * Dirac.slash a) := by
  have hE : Dirac.gamma μ = Dirac.slash (Minkowski.metric μ μ • Pi.single μ 1) :=
    gamma_eq_slash μ
  have h : ∀ ρ, Dirac.gamma ρ * (((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash a) *
      Dirac.gamma μ * ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash b)) *
      Dirac.gammaLower ρ =
      ((m : ℂ) ^ 2) • (Dirac.gamma ρ * Dirac.gamma μ * Dirac.gammaLower ρ)
        - (m : ℂ) • (Dirac.gamma ρ * Dirac.slash a * Dirac.gamma μ * Dirac.gammaLower ρ)
        - (m : ℂ) • (Dirac.gamma ρ * Dirac.gamma μ * Dirac.slash b * Dirac.gammaLower ρ)
        + Dirac.gamma ρ * Dirac.slash a * Dirac.gamma μ * Dirac.slash b *
          Dirac.gammaLower ρ := by
    intro ρ
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    module
  rw [Finset.sum_congr rfl fun ρ _ => h ρ, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum, ← Finset.smul_sum, hE,
    Dirac.contract_slash, Dirac.contract_slash_slash, Dirac.contract_slash_slash,
    Dirac.contract_slash_slash_slash, dot_metric_smul_single, Minkowski.dot_comm,
    dot_metric_smul_single]
  push_cast
  module

/-- The contraction at `d = 4` ((63.10)): with `a = p' + ℓ` and `b = p + ℓ`,
`γ_ν (m - a̸) γ^μ (m - b̸) γ^ν = 2m² γ^μ - 4m (a + b)^μ + 2 b̸ γ^μ a̸`. It follows from
`γ_ν γ^μ γ^ν = 2γ^μ`, `γ_ν a̸ γ^μ γ^ν = 4a^μ`, `γ_ν γ^μ b̸ γ^ν = 4b^μ` and
`γ_ν a̸ γ^μ b̸ γ^ν = 2 b̸ γ^μ a̸`. -/
theorem vertexNumeratorMatrix_eq (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 4 → ℝ) :
    vertexNumeratorMatrix m p' p μ ℓ =
      ((2 * m ^ 2 : ℝ) : ℂ) • Dirac.gamma μ
        - ((4 * m * ((p' + ℓ) μ + (p + ℓ) μ) : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
        + (2 : ℂ) • (Dirac.slash (p + ℓ) * Dirac.gamma μ * Dirac.slash (p' + ℓ)) := by
  rw [← contract_mass_sub_slash, ← sum_metric_smul_gamma_mul_mul, vertexNumeratorMatrix]
  simp only [Matrix.mul_assoc]

/-! ### On-shell sandwich -/

/-- The coefficient of `(p' - p)^μ (w u)` in the on-shell reduction of the shifted numerator.
With `x₁ = y x` and `x₂ = y (1 - x)` (the coefficients of `p'` and `p` in the shift) it is
`2m[(x₁ + x₁²) - (x₂ + x₂²)]`. This is the source's `-2m[(x₁ + x₁²) - (x₂ + x₂²)]` of (63.14)
with the source's labels, whose `x₁` multiplies `p` and `x₂` multiplies `p'`. -/
noncomputable def numeratorAsym (m x y : ℝ) : ℝ :=
  2 * m * ((y * x + (y * x) ^ 2) - (y * (1 - x) + (y * (1 - x)) ^ 2))

/-- `numeratorAsym m x y = 2m y (1 + y) (2x - 1)`. -/
theorem numeratorAsym_eq (m x y : ℝ) :
    numeratorAsym m x y = 2 * m * y * (1 + y) * (2 * x - 1) := by
  unfold numeratorAsym
  ring

/-- `numeratorAsym` is antisymmetric under `x ↦ 1 - x`, which exchanges `x₁` and `x₂`. -/
theorem numeratorAsym_one_sub (m x y : ℝ) : numeratorAsym m (1 - x) y = -numeratorAsym m x y := by
  unfold numeratorAsym
  ring

section Sandwich

variable {m : ℝ} {p' p : Fin 4 → ℝ} {u w : Fin 4 → ℂ}

private theorem sandwich_slash_mul (hw : w ᵥ* Dirac.slash p' = -((m : ℂ) • w))
    (X : Matrix (Fin 4) (Fin 4) ℂ) :
    w ⬝ᵥ ((Dirac.slash p' * X) *ᵥ u) = -(m : ℂ) * (w ⬝ᵥ (X *ᵥ u)) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hw, neg_dotProduct, smul_dotProduct,
    smul_eq_mul, neg_mul]

private theorem sandwich_mul_slash (hu : Dirac.slash p *ᵥ u = -((m : ℂ) • u))
    (X : Matrix (Fin 4) (Fin 4) ℂ) :
    w ⬝ᵥ ((X * Dirac.slash p) *ᵥ u) = -(m : ℂ) * (w ⬝ᵥ (X *ᵥ u)) := by
  rw [← Matrix.mulVec_mulVec, hu, Matrix.mulVec_neg, Matrix.mulVec_smul, dotProduct_neg,
    dotProduct_smul, smul_eq_mul, neg_mul]

/-- `γ^μ a̸ = -2a^μ - a̸ γ^μ`. -/
private theorem gamma_mul_slash_eq (μ : Fin 4) (a : Fin 4 → ℝ) :
    Dirac.gamma μ * Dirac.slash a =
      ((-2 * a μ : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash a * Dirac.gamma μ := by
  rw [← Dirac.gamma_slash_anticomm]
  abel

/-- `a̸ γ^μ = -2a^μ - γ^μ a̸`. -/
private theorem slash_mul_gamma_eq (μ : Fin 4) (a : Fin 4 → ℝ) :
    Dirac.slash a * Dirac.gamma μ =
      ((-2 * a μ : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.gamma μ * Dirac.slash a := by
  rw [← Dirac.gamma_slash_anticomm]
  abel

private theorem sandwich_slash'_gamma_slash (hu : Dirac.slash p *ᵥ u = -((m : ℂ) • u))
    (hw : w ᵥ* Dirac.slash p' = -((m : ℂ) • w)) (μ : Fin 4) :
    w ⬝ᵥ ((Dirac.slash p' * Dirac.gamma μ * Dirac.slash p) *ᵥ u) =
      (m : ℂ) ^ 2 * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)) := by
  rw [sandwich_mul_slash hu, sandwich_slash_mul hw]
  ring

private theorem sandwich_slash'_gamma_slash' (hw : w ᵥ* Dirac.slash p' = -((m : ℂ) • w))
    (μ : Fin 4) :
    w ⬝ᵥ ((Dirac.slash p' * Dirac.gamma μ * Dirac.slash p') *ᵥ u) =
      -(m : ℂ) ^ 2 * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)) + 2 * m * p' μ * (w ⬝ᵥ u) := by
  rw [Matrix.mul_assoc, sandwich_slash_mul hw, gamma_mul_slash_eq, Matrix.sub_mulVec,
    dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, Matrix.one_mulVec, sandwich_slash_mul hw,
    smul_eq_mul]
  push_cast
  ring

private theorem sandwich_slash_gamma_slash (hu : Dirac.slash p *ᵥ u = -((m : ℂ) • u))
    (μ : Fin 4) :
    w ⬝ᵥ ((Dirac.slash p * Dirac.gamma μ * Dirac.slash p) *ᵥ u) =
      -(m : ℂ) ^ 2 * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)) + 2 * m * p μ * (w ⬝ᵥ u) := by
  rw [sandwich_mul_slash hu, slash_mul_gamma_eq, Matrix.sub_mulVec, dotProduct_sub,
    Matrix.smul_mulVec, dotProduct_smul, Matrix.one_mulVec, sandwich_mul_slash hu, smul_eq_mul]
  push_cast
  ring

private theorem sandwich_slash_gamma_slash' (hu : Dirac.slash p *ᵥ u = -((m : ℂ) • u))
    (hw : w ᵥ* Dirac.slash p' = -((m : ℂ) • w)) (μ : Fin 4) :
    w ⬝ᵥ ((Dirac.slash p * Dirac.gamma μ * Dirac.slash p') *ᵥ u) =
      ((2 * Minkowski.dot p p' : ℝ) : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u))
        - (m : ℂ) ^ 2 * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)) + 2 * m * (p μ + p' μ) * (w ⬝ᵥ u) := by
  have e : Dirac.slash p * Dirac.gamma μ * Dirac.slash p' =
      Dirac.slash p * (Dirac.gamma μ * Dirac.slash p' + Dirac.slash p' * Dirac.gamma μ)
        - (Dirac.slash p * Dirac.slash p' + Dirac.slash p' * Dirac.slash p) * Dirac.gamma μ
        + Dirac.slash p' * (Dirac.gamma μ * Dirac.slash p + Dirac.slash p * Dirac.gamma μ)
        - Dirac.slash p' * Dirac.gamma μ * Dirac.slash p := by
    noncomm_ring
  rw [e, Dirac.gamma_slash_anticomm, Dirac.gamma_slash_anticomm, Dirac.slash_anticomm,
    Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec, dotProduct_sub, dotProduct_add,
    dotProduct_sub, sandwich_slash'_gamma_slash hu hw, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_smul, dotProduct_smul, dotProduct_smul,
    hu, Matrix.dotProduct_mulVec w (Dirac.slash p'), hw]
  simp only [dotProduct_neg, neg_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  push_cast
  ring

/-- On-shell reduction of the shifted numerator (project form of (63.14)–(63.17)): with
`x₁ = y x`, `x₂ = y (1 - x)`, `x₃ = 1 - y`, `K = y (x p' + (1 - x) p)` and `q = p' - p`,
between `w` with `w p̸' = -m w` and `u` with `p̸ u = -m u`,
`w N^μ(-K) u = w [2((1 - 4x₃ + x₃²) m² - (x₃ + x₁x₂) q²) γ^μ - 4im (x₃ - x₃²) S^{μν} q_ν] u
  + numeratorAsym m x y (p' - p)^μ (w u)`. -/
theorem sandwich_vertexNumeratorMatrix_neg_shift
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hu : Dirac.slash p *ᵥ u = -((m : ℂ) • u))
    (hw : w ᵥ* Dirac.slash p' = -((m : ℂ) • w)) (x y : ℝ) (μ : Fin 4) :
    w ⬝ᵥ (vertexNumeratorMatrix m p' p μ (-(y • (x • p' + (1 - x) • p))) *ᵥ u) =
      ((2 * ((1 - 4 * (1 - y) + (1 - y) ^ 2) * m ^ 2
          - ((1 - y) + (y * x) * (y * (1 - x))) * Minkowski.dot (p' - p) (p' - p)) : ℝ) : ℂ)
          * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u))
        - (4 * I * m * ((1 - y) - (1 - y) ^ 2))
          * (w ⬝ᵥ ((∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • Dirac.lorentzGen μ ν) *ᵥ u))
        + ((numeratorAsym m x y * (p' μ - p μ) : ℝ) : ℂ) * (w ⬝ᵥ u) := by
  have ha : p' + -(y • (x • p' + (1 - x) • p)) = (1 - y * x) • p' + (-(y * (1 - x))) • p := by
    funext k
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hb : p + -(y • (x • p' + (1 - x) • p)) = (-(y * x)) • p' + (1 - y * (1 - x)) • p := by
    funext k
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hlow : ∀ ν, Minkowski.lower (p' - p) ν = Minkowski.lower p' ν - Minkowski.lower p ν :=
    fun ν => by simp only [Minkowski.lower, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hq : Minkowski.dot (p' - p) (p' - p) = -2 * m ^ 2 - 2 * Minkowski.dot p p' := by
    have e : Minkowski.dot (p' - p) (p' - p) =
        Minkowski.dot p' p' - 2 * Minkowski.dot p p' + Minkowski.dot p p := by
      simp only [Minkowski.dot_eq, Pi.sub_apply]
      ring
    rw [e, hp', hp]
    ring
  have hG := Dirac.gordon m p p' u w hu hw μ
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.smul_mulVec,
    dotProduct_smul, dotProduct_smul, Matrix.one_mulVec, smul_eq_mul, smul_eq_mul] at hG
  rw [vertexNumeratorMatrix_eq, ha, hb]
  simp only [Dirac.slash_add, Dirac.slash_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mulVec,
    Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_sub, dotProduct_smul,
    Matrix.one_mulVec, hlow]
  rw [sandwich_slash'_gamma_slash' hw, sandwich_slash'_gamma_slash hu hw,
    sandwich_slash_gamma_slash' hu hw, sandwich_slash_gamma_slash hu]
  have hq' : ((Minkowski.dot (p' - p) (p' - p) : ℝ) : ℂ) =
      -2 * (m : ℂ) ^ 2 - 2 * ((Minkowski.dot p p' : ℝ) : ℂ) := by
    rw [hq]; push_cast; ring
  unfold numeratorAsym
  push_cast at hG hq' ⊢
  linear_combination (2 * (m : ℂ) * ((1 - y) - (1 - y) ^ 2)) * hG
    + (2 * ((1 - y) + (y * x) * (y * (1 - x))) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u))) * hq'

end Sandwich

end QED.OneLoop

end
