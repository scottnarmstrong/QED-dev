/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.Gordon
public import QED.Frozen.Algebra.Bar
public import QED.Frozen.Algebra.Spinor
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dirac adjoint and on-shell spinors

Spinor technology of the primary source's section 38, in the conventions of
`docs/CONVENTIONS.md`:

* `QED.Dirac.bar`: the Dirac adjoint `ū = u† β` as a row vector (eq. (38.7));
* `QED.Dirac.restSpinor`: the rest spinors `u_±(0)` of eq. (38.6);
* `QED.Dirac.spinor`: the on-shell spinor in closed form,
  `u_s(p) = (m - p̸) u_s(0) / √(2m(m + p⁰))`.

## Main statements

* `QED.Dirac.slash_mulVec_spinor`: the Dirac equation `(p̸ + m) u_s(p) = 0`
  (eq. (38.1)).
* `QED.Dirac.bar_vecMul_slash`: `(p̸ + m) u = 0` implies `ū (p̸ + m) = 0`
  (eq. (38.16)).
* `QED.Dirac.bar_spinor_dotProduct_spinor`: `ū_{s'}(p) u_s(p) = 2m δ_{s's}`
  (eq. (38.17)).
* `QED.Dirac.gordon_spinor`: the Gordon identity (38.18) for these spinors.

## Relation to the source's definition

The source defines `u_s(p)` by a boost, `u_s(p) = exp(iη p̂·K) u_s(0)`
(eq. (38.12)). This module uses the closed form instead. The two agree:
`QED.Dirac.spinor_eq_exp_boost` (`QED/Algebra/SpinorBoost.lean`) proves the equality for
`p⃗ ≠ 0`, as the source's magnetic-moment computation (64.11)–(64.12) needs. No physical
statement depends on the spinor basis, because form factors are defined for all spin
labels.
-/

@[expose] public section

open Matrix Complex

namespace QED.Dirac

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- `β² = 1`. -/
theorem beta_mul_beta : beta * beta = 𝟙 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [beta, Matrix.mul_apply, Fin.sum_univ_four]

/-- `β† = β`. -/
theorem conjTranspose_beta : betaᴴ = beta := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [beta]

/-- `β p̸† β = p̸` for a real four-vector. -/
theorem beta_mul_conjTranspose_slash_mul_beta (p : Fin 4 → ℝ) :
    beta * (slash p)ᴴ * beta = slash p := by
  simp only [slash, conjTranspose_sum, conjTranspose_smul, Finset.mul_sum, Finset.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, Complex.star_def, Complex.conj_ofReal,
    beta_mul_conjTranspose_gamma_mul_beta]

/-- `bar (A u) = bar u (β A† β)`. -/
theorem bar_mulVec (A : Matrix (Fin 4) (Fin 4) ℂ) (u : Fin 4 → ℂ) :
    bar (A *ᵥ u) = bar u ᵥ* (beta * Aᴴ * beta) := by
  simp only [bar, star_mulVec, vecMul_vecMul]
  congr 1
  simp only [← Matrix.mul_assoc, beta_mul_beta, Matrix.one_mul]

/-- The Dirac adjoint commutes with real scalars. -/
theorem bar_smul (c : ℝ) (u : Fin 4 → ℂ) : bar ((c : ℂ) • u) = (c : ℂ) • bar u := by
  have h : star ((c : ℂ) • u) = (c : ℂ) • star u := by
    funext i; simp [Pi.star_apply, Complex.conj_ofReal]
  rw [bar, bar, h, smul_vecMul]

/-- If `(p̸ + m) u = 0`, then `ū (p̸ + m) = 0` (eq. (38.16) from (38.1)). -/
theorem bar_vecMul_slash (m : ℝ) (p : Fin 4 → ℝ) (u : Fin 4 → ℂ)
    (hu : slash p *ᵥ u = -((m : ℂ) • u)) :
    bar u ᵥ* slash p = -((m : ℂ) • bar u) := by
  have := bar_mulVec (slash p) u
  rw [beta_mul_conjTranspose_slash_mul_beta, hu] at this
  rw [← this, show -((m : ℂ) • u) = ((-m : ℝ) : ℂ) • u by push_cast; module, bar_smul]
  push_cast; module

/-- `p̸ (m - p̸) = -m (m - p̸)` on shell. -/
theorem slash_mul_mass_sub_slash (m : ℝ) (p : Fin 4 → ℝ) (hp : Minkowski.dot p p = -m ^ 2) :
    slash p * ((m : ℂ) • 𝟙 - slash p) = (-(m : ℂ)) • ((m : ℂ) • 𝟙 - slash p) := by
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, slash_mul_slash, hp]
  push_cast
  module

/-- The Dirac equation `(p̸ + m) u_s(p) = 0` (eq. (38.1)) on shell. -/
theorem slash_mulVec_spinor (m : ℝ) (p : Fin 4 → ℝ) (hp : Minkowski.dot p p = -m ^ 2)
    (s : Fin 2) : slash p *ᵥ spinor m p s = -((m : ℂ) • spinor m p s) := by
  unfold spinor
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, slash_mul_mass_sub_slash m p hp,
    Matrix.smul_mulVec]
  module

/-- `(m - p̸)² = 2m (m - p̸)` on shell. -/
theorem mass_sub_slash_sq (m : ℝ) (p : Fin 4 → ℝ) (hp : Minkowski.dot p p = -m ^ 2) :
    ((m : ℂ) • 𝟙 - slash p) * ((m : ℂ) • 𝟙 - slash p) = (2 * m : ℂ) • ((m : ℂ) • 𝟙 - slash p) := by
  rw [Matrix.sub_mul, slash_mul_mass_sub_slash m p hp, Matrix.smul_mul, Matrix.one_mul]
  module

/-- `β (m - p̸)† β = m - p̸` for real `m` and `p`. -/
theorem beta_mul_conjTranspose_mass_sub_slash_mul_beta (m : ℝ) (p : Fin 4 → ℝ) :
    beta * ((m : ℂ) • 𝟙 - slash p)ᴴ * beta = (m : ℂ) • 𝟙 - slash p := by
  rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, beta_mul_beta,
    beta_mul_conjTranspose_slash_mul_beta, Complex.star_def, Complex.conj_ofReal]

/-- Rest-frame products: `ū_{s'}(0) (m - p̸) u_s(0) = 2m(m + p⁰) δ_{s's}`. -/
theorem bar_restSpinor_mulVec (m : ℝ) (hm : 0 ≤ m) (p : Fin 4 → ℝ) (s s' : Fin 2) :
    bar (restSpinor m s') ⬝ᵥ (((m : ℂ) • 𝟙 - slash p) *ᵥ restSpinor m s) =
      if s' = s then ((2 * m * (m + p 0) : ℝ) : ℂ) else 0 := by
  have hsq : (Real.sqrt m : ℂ) ^ 2 = (m : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hm]
  fin_cases s <;> fin_cases s' <;>
    simp [bar, restSpinor, beta, slash, Minkowski.lower_eq, gamma, Fin.sum_univ_four, vecMul,
      dotProduct, mulVec, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply] <;>
    ring_nf
  all_goals rw [hsq]; ring

/-- The normalization `ū_{s'}(p) u_s(p) = 2m δ_{s's}` (eq. (38.17)) on shell, with
positive energy. -/
theorem bar_spinor_dotProduct_spinor (m : ℝ) (hm : 0 < m) (p : Fin 4 → ℝ)
    (hp : Minkowski.dot p p = -m ^ 2) (hp0 : 0 < p 0) (s s' : Fin 2) :
    bar (spinor m p s') ⬝ᵥ spinor m p s = if s' = s then (2 * m : ℂ) else 0 := by
  set c : ℝ := (Real.sqrt (2 * m * (m + p 0)))⁻¹ with hc
  set M : Matrix (Fin 4) (Fin 4) ℂ := (m : ℂ) • 𝟙 - slash p with hM
  have hX : 0 < 2 * m * (m + p 0) := by positivity
  have hc2 : c * c * (2 * m * (m + p 0)) = 1 := by
    rw [hc, ← mul_inv, Real.mul_self_sqrt hX.le, inv_mul_cancel₀ hX.ne']
  have hbar : bar (spinor m p s') = (c : ℂ) • (bar (restSpinor m s') ᵥ* M) := by
    simp only [spinor, ← hc, ← hM]
    rw [bar_smul, bar_mulVec, hM, beta_mul_conjTranspose_mass_sub_slash_mul_beta]
  have hu : spinor m p s = (c : ℂ) • (M *ᵥ restSpinor m s) := rfl
  rw [hbar, hu, smul_dotProduct, dotProduct_smul, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hM, mass_sub_slash_sq m p hp, Matrix.smul_mulVec, dotProduct_smul,
    bar_restSpinor_mulVec m hm.le p s s']
  split_ifs
  · simp only [smul_eq_mul]
    have : ((c * c * (2 * m * (m + p 0)) : ℝ) : ℂ) = 1 := by rw [hc2]; simp
    push_cast at this ⊢
    linear_combination (2 * (m : ℂ)) * this
  · simp

/-- The Gordon identity (38.18) for the on-shell spinors:
`2m ū_{s'}(p') γ^μ u_s(p) = ū_{s'}(p') [(p' + p)^μ - 2i S^{μν} (p' - p)_ν] u_s(p)`. -/
theorem gordon_spinor (m : ℝ) (p p' : Fin 4 → ℝ) (hp : Minkowski.dot p p = -m ^ 2)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (s s' : Fin 2) (μ : Fin 4) :
    (2 * m : ℂ) * (bar (spinor m p' s') ⬝ᵥ (gamma μ *ᵥ spinor m p s)) =
      bar (spinor m p' s') ⬝ᵥ ((((p' μ + p μ : ℝ) : ℂ) • 𝟙
        - (2 * I) • ∑ ν, ((Minkowski.lower p' ν - Minkowski.lower p ν : ℝ) : ℂ) • lorentzGen μ ν)
          *ᵥ spinor m p s) :=
  gordon m p p' _ _ (slash_mulVec_spinor m p hp s)
    (bar_vecMul_slash m p' _ (slash_mulVec_spinor m p' hp' s')) μ

end QED.Dirac

end
