/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.Spinor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Spinor matrix elements in the Breit frame

Matrix elements of `γ^i` and of `S^{iν} q_ν` between on-shell spinors in the Breit frame
`p = (E, -q⃗/2)`, `p' = (E, q⃗/2)` (obligation O-22 of `docs/ONE-LOOP-DERIVATION.md`), in the
conventions of `docs/CONVENTIONS.md`. For general `q⃗` and spin labels these are
`ū_{s'}(p') γ^i u_s(p) = -i ε^{ijk} q^j (σ^k)_{s's}` and
`ū_{s'}(p') S^{iν} q_ν u_s(p) = m ε^{ijk} q^j (σ^k)_{s's}`, independent of `E`. This module
proves the case used for the magnetic moment: `q⃗ = (q, 0, 0)`, the `y` component `i = 2`, and
spin up for both spinors, where `ε^{2jk} q^j (σ^k)_{++} = -q`.

## Main statements

* `QED.Dirac.breit_energy`: on shell with positive energy, `p'⁰ = p⁰ = √(m² + q²/4)`.
* `QED.Dirac.spinor_zero_eq_of_along_x`: the explicit spin-up spinor for `p⃗` along `x`.
* `QED.Dirac.breit_bar_spinor_gamma_two_spinor`: `ū₊(p') γ² u₊(p) = i q`.
* `QED.Dirac.breit_bar_spinor_lorentzGen_two_spinor`: `ū₊(p') S^{2ν} q_ν u₊(p) = -m q`.

## Proof outline

For `p⃗` along `x`, `(m - p̸) u₊(0) = √m (m + p⁰, -p¹, m + p⁰, p¹)`, so both spinors are
explicit real vectors with the common normalization `c = √m / √(2m(m + E))`. A direct
computation gives `ū₊(p') γ² u₊(p) = c² · 2i (m + E) q = i q`. The Gordon identity at
`μ = 2`, where `p'² + p² = 0`, turns this into the matrix element of `S^{2ν} q_ν`.
-/

@[expose] public section

open Matrix Complex

namespace QED.Dirac

/-- In the Breit frame along `x`, on shell with positive energies, both energies equal
`E = √(m² + q²/4)`. -/
theorem breit_energy {m q : ℝ} {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (h1' : p' 1 = q / 2) (h1 : p 1 = -(q / 2)) (h2' : p' 2 = 0) (h2 : p 2 = 0)
    (h3' : p' 3 = 0) (h3 : p 3 = 0) :
    p' 0 = p 0 ∧ p 0 = Real.sqrt (m ^ 2 + q ^ 2 / 4) := by
  rw [Minkowski.dot_eq, h1', h2', h3'] at hp'
  rw [Minkowski.dot_eq, h1, h2, h3] at hp
  have hE : p 0 = Real.sqrt (m ^ 2 + q ^ 2 / 4) := by
    rw [← Real.sqrt_sq hp0.le]
    congr 1
    linear_combination -hp
  have hE' : p' 0 = Real.sqrt (m ^ 2 + q ^ 2 / 4) := by
    rw [← Real.sqrt_sq hp0'.le]
    congr 1
    linear_combination -hp'
  exact ⟨hE'.trans hE.symm, hE⟩

/-- For `p⃗` along `x`, the spin-up spinor is
`u₊(p) = √m / √(2m(m + p⁰)) · (m + p⁰, -p¹, m + p⁰, p¹)`. -/
theorem spinor_zero_eq_of_along_x (m : ℝ) {p : Fin 4 → ℝ} (h2 : p 2 = 0) (h3 : p 3 = 0) :
    spinor m p 0 = (((Real.sqrt (2 * m * (m + p 0)))⁻¹ * Real.sqrt m : ℝ) : ℂ) •
      fun i => ((![m + p 0, -p 1, m + p 0, p 1] i : ℝ) : ℂ) := by
  ext i
  fin_cases i <;>
    simp [spinor, restSpinor, slash, Minkowski.lower_eq, gamma, Fin.sum_univ_four, mulVec,
      dotProduct, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, h2, h3] <;> ring

/-- Breit frame along `x`: `ū₊(p') γ² u₊(p) = i q`. -/
theorem breit_bar_spinor_gamma_two_spinor {m : ℝ} (hm : 0 < m) {q : ℝ} {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (h1' : p' 1 = q / 2) (h1 : p 1 = -(q / 2)) (h2' : p' 2 = 0) (h2 : p 2 = 0)
    (h3' : p' 3 = 0) (h3 : p 3 = 0) :
    bar (spinor m p' 0) ⬝ᵥ (gamma 2 *ᵥ spinor m p 0) = I * q := by
  obtain ⟨hE', -⟩ := breit_energy hp' hp hp0' hp0 h1' h1 h2' h2 h3' h3
  set c : ℝ := (Real.sqrt (2 * m * (m + p 0)))⁻¹ * Real.sqrt m with hc
  have hX : 0 < 2 * m * (m + p 0) := by positivity
  -- The normalization: `c² = 1 / (2(m + E))`.
  have hc2 : c * c * (2 * (m + p 0)) = 1 := by
    rw [hc, show (Real.sqrt (2 * m * (m + p 0)))⁻¹ * Real.sqrt m *
        ((Real.sqrt (2 * m * (m + p 0)))⁻¹ * Real.sqrt m) * (2 * (m + p 0)) =
        (Real.sqrt m * Real.sqrt m) * (2 * (m + p 0)) *
          (Real.sqrt (2 * m * (m + p 0)) * Real.sqrt (2 * m * (m + p 0)))⁻¹ by ring,
      Real.mul_self_sqrt hX.le, Real.mul_self_sqrt hm.le]
    field_simp
  have hc2C : (c : ℂ) * (c : ℂ) * (2 * ((m : ℂ) + (p 0 : ℂ))) = 1 := by
    exact_mod_cast hc2
  rw [spinor_zero_eq_of_along_x m h2' h3', spinor_zero_eq_of_along_x m h2 h3, hE', ← hc,
    bar_smul, smul_dotProduct, mulVec_smul, dotProduct_smul]
  -- The explicit product is `c² · 2i (m + E) q`.
  simp only [dotProduct, bar, vecMul, Fin.isValue, h1', Pi.star_apply, star_def, conj_ofReal,
    beta, of_apply, cons_val', cons_val_fin_one, Fin.sum_univ_four, cons_val_zero, ofReal_add,
    cons_val_one, ofReal_neg, ofReal_div, ofReal_ofNat, neg_mul, cons_val, mulVec, gamma, h1,
    neg_neg, mul_neg, mul_zero, neg_zero, add_zero, mul_one, zero_add, zero_mul, smul_eq_mul]
  linear_combination (I * q) * hc2C

/-- Breit frame along `x`: `ū₊(p') S^{2ν} q_ν u₊(p) = -m q`. -/
theorem breit_bar_spinor_lorentzGen_two_spinor {m : ℝ} (hm : 0 < m) {q : ℝ} {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (h1' : p' 1 = q / 2) (h1 : p 1 = -(q / 2)) (h2' : p' 2 = 0) (h2 : p 2 = 0)
    (h3' : p' 3 = 0) (h3 : p 3 = 0) :
    bar (spinor m p' 0) ⬝ᵥ ((∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • lorentzGen 2 ν)
      *ᵥ spinor m p 0) = -((m * q : ℝ) : ℂ) := by
  have hl : ∀ ν, Minkowski.lower (p' - p) ν = Minkowski.lower p' ν - Minkowski.lower p ν :=
    fun ν => by simp only [Minkowski.lower, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  -- Gordon at `μ = 2`, with `p'² + p² = 0`: `2m · (i q) = -2i · ū₊(p') S^{2ν} q_ν u₊(p)`.
  have hG := gordon_spinor m p p' hp hp' 0 0 2
  rw [breit_bar_spinor_gamma_two_spinor hm hp' hp hp0' hp0 h1' h1 h2' h2 h3' h3, h2', h2,
    add_zero, ofReal_zero, zero_smul, zero_sub, neg_mulVec, dotProduct_neg, smul_mulVec,
    dotProduct_smul, smul_eq_mul] at hG
  simp only [← hl] at hG
  push_cast
  linear_combination (-I / 2) * hG
    + (bar (spinor m p' 0) ⬝ᵥ ((∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • lorentzGen 2 ν)
      *ᵥ spinor m p 0) + m * q) * I_sq

end QED.Dirac

end
