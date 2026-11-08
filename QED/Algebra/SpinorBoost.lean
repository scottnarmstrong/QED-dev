/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.Spinor
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Topology.Instances.Matrix
import QED.Algebra.Contraction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The on-shell spinors as boosted rest spinors

The primary source defines the on-shell spinors by a boost of the rest spinors,
`u_s(p) = exp(iη p̂·K) u_s(0)` (eqs. (38.11)–(38.12)), where `p̂` is the unit vector along `p⃗`,
`K^j = (i/4)[γ^j, γ^0] = S^{j0}` is the boost matrix, and `η = sinh⁻¹(|p⃗|/m)` is the rapidity.
The module `QED.Algebra.Spinor` uses the closed form
`u_s(p) = (m - p̸) u_s(0) / √(2m(m + p⁰))` instead. This module proves that the two agree for
on-shell `p` with `p⁰ > 0` and `p⃗ ≠ 0`.

The exponential is `NormedSpace.exp` on `Matrix (Fin 4) (Fin 4) ℂ`. It needs only the
canonical (entrywise) topology on matrices; no matrix norm is chosen, here or in the proofs.

## Main definitions

* `QED.Dirac.boostGen`: the boost generator `p⃗·K = Σ_j p^j S^{j0}`.

## Main statements

* `QED.Dirac.exp_smul_of_mul_self_eq_one`: if `N² = 1`, then
  `exp(c N) = cosh c + sinh c · N`.
* `QED.Dirac.boostGen_eq_half`: `p⃗·K = (i/2) (0, p⃗)̸ γ^0`.
* `QED.Dirac.spinor_eq_exp_boost`: the closed-form spinor is the boosted rest spinor (38.12).

## Proof outline

Write `M = (0, p⃗)̸ γ^0`, so that `p⃗·K = (i/2) M` and `M² = |p⃗|²`. With `N = -M/|p⃗|`, the
exponent is `iη p̂·K = (η/2) N` and `N² = 1`, so `exp(iη p̂·K) = cosh(η/2) + sinh(η/2) N`. On
shell, `cosh(η/2) √(2m(m + p⁰)) = m + p⁰` and `sinh(η/2) √(2m(m + p⁰)) = |p⃗|`. Finally
`γ^0 u_s(0) = u_s(0)` and `(0, p⃗)̸ = p̸ + p⁰ γ^0` turn `N u_s(0)` into
`-(p̸ + p⁰) u_s(0) / |p⃗|`, which gives the closed form.
-/

@[expose] public section

open Matrix Complex

namespace QED.Dirac

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- The boost generator `p̂·K = Σ_j p̂_j S^{j0}` along the spatial direction of `p`, here not
normalized: `boostGen p = Σ_j p^j S^{j0} = |p⃗| p̂·K`. -/
noncomputable def boostGen (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ j : Fin 3, ((p j.succ : ℝ) : ℂ) • lorentzGen j.succ 0

/-- The spatial part `(0, p⃗)` of a four-vector `p`. -/
def spatialPart (p : Fin 4 → ℝ) : Fin 4 → ℝ := ![0, p 1, p 2, p 3]

/-- The closed form of the exponential of `c N` for `N² = 1`:
`exp(c N) = cosh c + sinh c · N`. -/
theorem exp_smul_of_mul_self_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {N : Matrix n n ℂ} (hN : N * N = 1) (c : ℂ) :
    NormedSpace.exp (c • N) = Complex.cosh c • (1 : Matrix n n ℂ) + Complex.sinh c • N := by
  have hN2 : N ^ 2 = 1 := by rw [sq, hN]
  rw [NormedSpace.exp_eq_tsum ℂ]
  refine HasSum.tsum_eq (HasSum.even_add_odd ?_ ?_)
  · convert (Complex.hasSum_cosh c).smul_const (1 : Matrix n n ℂ) using 1
    funext k
    rw [smul_pow, pow_mul N, hN2, one_pow, smul_smul, div_eq_inv_mul]
  · convert (Complex.hasSum_sinh c).smul_const N using 1
    funext k
    rw [smul_pow, pow_succ N, pow_mul N, hN2, one_pow, one_mul, smul_smul, div_eq_inv_mul]

/-- `(γ^0)² = 1`. -/
theorem gamma_zero_mul_gamma_zero : gamma 0 * gamma 0 = 𝟙 := by
  have h := gamma_anticomm 0 0
  rw [show Minkowski.metric 0 0 = -1 by simp only [Minkowski.metric, ↓reduceIte]] at h
  have h2 : (2 : ℂ) • (gamma 0 * gamma 0) = (2 : ℂ) • 𝟙 := by
    rw [two_smul, h]; norm_num
  exact smul_right_injective _ two_ne_zero h2

/-- `γ^0` anticommutes with the slash of a purely spatial vector. -/
theorem gamma_zero_mul_slash_spatialPart (p : Fin 4 → ℝ) :
    gamma 0 * slash (spatialPart p) = -(slash (spatialPart p) * gamma 0) := by
  have h := gamma_slash_anticomm 0 (spatialPart p)
  simp only [spatialPart, Matrix.cons_val_zero, mul_zero, Complex.ofReal_zero, zero_smul] at h
  exact eq_neg_of_add_eq_zero_left h

/-- `p⃗·K = (i/4) [(0, p⃗)̸, γ^0]`. -/
theorem boostGen_eq_commutator (p : Fin 4 → ℝ) :
    boostGen p =
      (I / 4) • (slash (spatialPart p) * gamma 0 - gamma 0 * slash (spatialPart p)) := by
  simp only [boostGen, lorentzGen, slash, Minkowski.lower_eq, spatialPart, Fin.sum_univ_three,
    Fin.sum_univ_four]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.reduceSucc, neg_zero, Complex.ofReal_zero, zero_smul, zero_add,
    add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  module

/-- `p⃗·K = (i/2) (0, p⃗)̸ γ^0`. -/
theorem boostGen_eq_half (p : Fin 4 → ℝ) :
    boostGen p = (I / 2) • (slash (spatialPart p) * gamma 0) := by
  rw [boostGen_eq_commutator, gamma_zero_mul_slash_spatialPart, sub_neg_eq_add, ← two_smul ℂ,
    smul_smul]
  congr 1
  ring

/-- `(0, p⃗)̸ = p̸ + p⁰ γ^0`. -/
theorem slash_spatialPart (p : Fin 4 → ℝ) :
    slash (spatialPart p) = slash p + ((p 0 : ℝ) : ℂ) • gamma 0 := by
  simp only [slash, Minkowski.lower_eq, spatialPart, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
    Matrix.vecTail, Function.comp_apply, Fin.reduceSucc, neg_zero, Complex.ofReal_zero,
    zero_smul, zero_add, Complex.ofReal_neg, neg_smul]
  abel

/-- `(0, p⃗)·(0, p⃗) = |p⃗|²`. -/
theorem dot_spatialPart (p : Fin 4 → ℝ) :
    Minkowski.dot (spatialPart p) (spatialPart p) = ∑ j : Fin 3, p j.succ ^ 2 := by
  simp only [spatialPart, Minkowski.dot_eq, Matrix.cons_val_zero, mul_zero, neg_zero,
    Matrix.cons_val_one, zero_add, Matrix.cons_val, Fin.sum_univ_three, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Fin.reduceSucc]
  ring

/-- `((0, p⃗)̸ γ^0)² = |p⃗|²`. -/
theorem slash_spatialPart_mul_gamma_zero_sq (p : Fin 4 → ℝ) :
    slash (spatialPart p) * gamma 0 * (slash (spatialPart p) * gamma 0) =
      ((∑ j : Fin 3, p j.succ ^ 2 : ℝ) : ℂ) • 𝟙 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (gamma 0), gamma_zero_mul_slash_spatialPart,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, gamma_zero_mul_gamma_zero, Matrix.mul_one,
    slash_mul_slash, dot_spatialPart, Complex.ofReal_neg, neg_smul, neg_neg]

/-- The rest spinors are fixed by `γ^0`: `γ^0 u_s(0) = u_s(0)`. -/
theorem gamma_zero_mulVec_restSpinor (m : ℝ) (s : Fin 2) :
    gamma 0 *ᵥ restSpinor m s = restSpinor m s := by
  fin_cases s <;> funext i <;> fin_cases i <;>
    simp only [mulVec, dotProduct, gamma, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, restSpinor, Fin.sum_univ_four, zero_mul, mul_zero, add_zero, one_mul,
      zero_add]

/-- Half-rapidity identities: with `η = arsinh(n/m)`, `p⁰² = m² + n²`, `p⁰ > 0`, and
`D = √(2m(m + p⁰))`, we have `cosh(η/2) D = m + p⁰` and `sinh(η/2) D = n`. -/
theorem cosh_sinh_half_arsinh {m n p0 : ℝ} (hm : 0 < m) (hp0 : 0 < p0)
    (hshell : p0 ^ 2 = m ^ 2 + n ^ 2) :
    Real.cosh (Real.arsinh (n / m) / 2) * √(2 * m * (m + p0)) = m + p0 ∧
      Real.sinh (Real.arsinh (n / m) / 2) * √(2 * m * (m + p0)) = n := by
  set x := Real.arsinh (n / m) / 2 with hx
  set C := Real.cosh x
  set S := Real.sinh x
  set D := √(2 * m * (m + p0))
  have hD2 : D ^ 2 = 2 * m * (m + p0) := Real.sq_sqrt (by positivity)
  have hC0 : 0 < C := Real.cosh_pos x
  have h2x : Real.arsinh (n / m) = 2 * x := by rw [hx]; ring
  have hcosh : C ^ 2 + S ^ 2 = p0 / m := by
    rw [← Real.cosh_two_mul, ← h2x, Real.cosh_arsinh,
      Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
    field_simp
    linarith
  have hsinh : 2 * S * C = n / m := by
    rw [← Real.sinh_two_mul, ← h2x, Real.sinh_arsinh]
  have hCS : C ^ 2 = S ^ 2 + 1 := Real.cosh_sq x
  have hC2 : 2 * m * C ^ 2 = m + p0 := by
    have hpm : m * (p0 / m) = p0 := by field_simp
    linear_combination m * hcosh + m * hCS + hpm
  have hCD : C * D = m + p0 := by
    have h1 : (C * D) ^ 2 = (m + p0) ^ 2 := by
      rw [mul_pow, hD2]; linear_combination (m + p0) * hC2
    exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp h1
  refine ⟨hCD, ?_⟩
  have hmp : 0 < m + p0 := by positivity
  have h2 : S * D * (m + p0) = n * (m + p0) := by
    have hnm : m * (n / m) = n := by field_simp
    have : 2 * m * (S * C) = n := by linear_combination m * hsinh + hnm
    linear_combination (-(S * D)) * hCD + (S * C) * hD2 + (m + p0) * this
  exact mul_right_cancel₀ hmp.ne' h2

/-- (38.12): for on-shell `p` with `p⁰ > 0` and `p⃗ ≠ 0`, the closed-form spinor is the boosted
rest spinor `exp(i η p̂·K) u_s(0)`, with `η = arsinh(|p⃗|/m)` and `|p⃗| = √(Σ p_j²)`. -/
theorem spinor_eq_exp_boost {m : ℝ} (hm : 0 < m) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -m ^ 2) (hp0 : 0 < p 0)
    (hpv : 0 < ∑ j : Fin 3, p j.succ ^ 2) (s : Fin 2) :
    spinor m p s = NormedSpace.exp ((I * (Real.arsinh (√(∑ j : Fin 3, p j.succ ^ 2) / m)
        / √(∑ j : Fin 3, p j.succ ^ 2) : ℝ)) • boostGen p) *ᵥ restSpinor m s := by
  set n := √(∑ j : Fin 3, p j.succ ^ 2)
  set η := Real.arsinh (n / m)
  set D := √(2 * m * (m + p 0)) with hD
  set M := slash (spatialPart p) * gamma 0 with hM
  have hn0 : 0 < n := Real.sqrt_pos.mpr hpv
  have hn2 : n ^ 2 = ∑ j : Fin 3, p j.succ ^ 2 := Real.sq_sqrt hpv.le
  have hshell : p 0 ^ 2 = m ^ 2 + n ^ 2 := by
    rw [hn2, Fin.sum_univ_three]
    rw [Minkowski.dot_eq] at hp
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc]
    linear_combination -hp
  obtain ⟨hCD, hSD⟩ : Real.cosh (η / 2) * D = m + p 0 ∧ Real.sinh (η / 2) * D = n :=
    cosh_sinh_half_arsinh hm hp0 hshell
  -- The normalized generator `N = -M/|p⃗|` squares to one, and the exponent is `(η/2) N`.
  set N : Matrix (Fin 4) (Fin 4) ℂ := (-(1 / n : ℝ) : ℂ) • M with hN
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hNN : N * N = 𝟙 := by
    rw [hN, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hM,
      slash_spatialPart_mul_gamma_zero_sq, ← hn2, smul_smul]
    convert one_smul ℂ 𝟙 using 2
    push_cast
    field_simp
  have hA : ((I * (η / n : ℝ) : ℂ)) • boostGen p = ((η / 2 : ℝ) : ℂ) • N := by
    rw [boostGen_eq_half, ← hM, hN, smul_smul, smul_smul]
    congr 1
    push_cast
    linear_combination (η / (2 * n) : ℂ) * I_sq
  rw [hA, exp_smul_of_mul_self_eq_one hNN, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.smul_mulVec, hN, Matrix.smul_mulVec, hM, ← Matrix.mulVec_mulVec,
    gamma_zero_mulVec_restSpinor, slash_spatialPart, Matrix.add_mulVec, Matrix.smul_mulVec,
    gamma_zero_mulVec_restSpinor, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  simp only [spinor, ← hD, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  -- Compare coefficients using the half-rapidity identities.
  have hD0 : D ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hC : Real.cosh (η / 2) = (m + p 0) * D⁻¹ := by
    rw [← hCD]; field_simp
  have hS : Real.sinh (η / 2) * (1 / n) = D⁻¹ := by
    have hS' : Real.sinh (η / 2) = n * D⁻¹ := by rw [← hSD]; field_simp
    rw [hS']; field_simp
  have hCc : (Real.cosh (η / 2) : ℂ) = ((m : ℂ) + (p 0 : ℂ)) * ((D⁻¹ : ℝ) : ℂ) := by
    rw [hC]; push_cast; ring
  have hSc : (Real.sinh (η / 2) : ℂ) * ((1 / n : ℝ) : ℂ) = ((D⁻¹ : ℝ) : ℂ) := by
    rw [← hS]; push_cast; ring
  linear_combination (norm := module) -(hCc • restSpinor m s) +
    hSc • (slash p *ᵥ restSpinor m s + ((p 0 : ℝ) : ℂ) • restSpinor m s)

end QED.Dirac

end
