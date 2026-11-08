/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.Contraction
public import QED.Algebra.Dirac
public import Mathlib.LinearAlgebra.Matrix.Trace
import QED.Algebra.Spinor
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Gamma-matrix traces and independence of the on-shell vertex structures

Trace identities for the gamma matrices of `docs/CONVENTIONS.md`, and the
linear independence of the two on-shell vertex structures `ū'γ^μu` and
`ū'S^{μν}q_νu` for `q² > 0`. The independence is the uniqueness half of
obligation O-15 (`docs/ONE-LOOP-DERIVATION.md`): the form factors of (63.18)
are determined by the vertex sandwiches.

## Main statements

* `QED.Dirac.trace_slash`: `tr a̸ = 0`.
* `QED.Dirac.trace_slash_mul_slash`: `tr(a̸ b̸) = -4 (a·b)`.
* `QED.Dirac.trace_slash_mul_slash_mul_slash`: `tr(a̸ b̸ c̸) = 0`.
* `QED.Dirac.eq_zero_of_sandwich_formFactor_eq_zero`: if
  `w [A γ^μ - (i/m) B S^{μν} q_ν] u = 0` for every `μ`, every column vector `u`
  with `(p̸ + m) u = 0` and every row vector `w` with `w (p̸' + m) = 0`, on shell
  with `q = p' - p` and `q² > 0`, then `A = B = 0`.

## Proof outline

The odd traces vanish because the chirality matrix `diag(-1, -1, 1, 1)` squares
to one and anticommutes with every `γ^μ`. The two-slash trace is half the trace
of the anticommutator `{a̸, b̸} = -2 (a·b)`.

For the independence, put `P = m - p̸` and `P' = m - p̸'`. Every `P x` solves
`(p̸ + m) u = 0` and every `y P'` solves `w (p̸' + m) = 0`, so the hypothesis
gives the matrix identity `P' X^μ P = 0`. The Gordon identity turns it into
`(A + B) P' γ^μ P = (B / 2m) (p' + p)^μ P' P`. Contracting with `(p' + p)_μ`,
and separately multiplying by `γ_μ` on the right and contracting, then taking
traces, gives two linear equations for `A` and `B`. Their determinant is a
nonzero multiple of `q² (4m² + q²)`.
-/

@[expose] public section

open Matrix Complex

namespace QED.Dirac

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- The chirality matrix `diag(-1, -1, 1, 1)` of the Weyl representation. -/
local notation "Γ" => Matrix.diagonal ![(-1 : ℂ), -1, 1, 1]

/-- The chirality matrix anticommutes with every `γ^μ`. -/
theorem chirality_mul_gamma (μ : Fin 4) : Γ * gamma μ = -(gamma μ * Γ) := by
  ext i j
  rw [Matrix.neg_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases μ <;> fin_cases i <;> fin_cases j <;> simp [gamma]

/-- The chirality matrix anticommutes with every slash. -/
theorem chirality_mul_slash (a : Fin 4 → ℝ) : Γ * slash a = -(slash a * Γ) := by
  simp only [slash, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    chirality_mul_gamma, smul_neg, Finset.sum_neg_distrib]

/-- The chirality matrix squares to one. -/
theorem chirality_mul_chirality : Γ * Γ = 𝟙 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

/-- A matrix that anticommutes with the chirality matrix is traceless. -/
theorem trace_eq_zero_of_chirality_anticomm (X : Matrix (Fin 4) (Fin 4) ℂ)
    (h : Γ * X = -(X * Γ)) : trace X = 0 := by
  have e : trace X = -trace X :=
    calc trace X = trace (Γ * (Γ * X)) := by
          rw [← Matrix.mul_assoc, chirality_mul_chirality, Matrix.one_mul]
      _ = trace (Γ * X * Γ) := trace_mul_comm _ _
      _ = -trace X := by
          rw [h, Matrix.neg_mul, trace_neg, Matrix.mul_assoc, chirality_mul_chirality,
            Matrix.mul_one]
  linear_combination e / 2

/-- `tr a̸ = 0`. -/
theorem trace_slash (a : Fin 4 → ℝ) : Matrix.trace (slash a) = 0 :=
  trace_eq_zero_of_chirality_anticomm _ (chirality_mul_slash a)

/-- `tr(a̸ b̸) = -4 (a·b)`. -/
theorem trace_slash_mul_slash (a b : Fin 4 → ℝ) :
    Matrix.trace (slash a * slash b) = -4 * (Minkowski.dot a b : ℂ) := by
  have h := congrArg trace (slash_anticomm a b)
  rw [trace_add, trace_mul_comm (slash b), trace_smul, trace_one, Fintype.card_fin,
    smul_eq_mul] at h
  push_cast at h
  linear_combination h / 2

/-- `tr(a̸ b̸ c̸) = 0`. -/
theorem trace_slash_mul_slash_mul_slash (a b c : Fin 4 → ℝ) :
    Matrix.trace (slash a * slash b * slash c) = 0 := by
  refine trace_eq_zero_of_chirality_anticomm _ ?_
  calc Γ * (slash a * slash b * slash c) = Γ * slash a * slash b * slash c := by
        simp only [Matrix.mul_assoc]
    _ = -(slash a * (Γ * slash b) * slash c) := by
        rw [chirality_mul_slash]; simp only [Matrix.neg_mul, Matrix.mul_assoc]
    _ = slash a * slash b * (Γ * slash c) := by
        rw [chirality_mul_slash]; simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg,
          Matrix.mul_assoc]
    _ = -(slash a * slash b * slash c * Γ) := by
        rw [chirality_mul_slash]; simp only [Matrix.mul_neg, Matrix.mul_assoc]

/-- On shell, `(m - p̸) p̸ = -m (m - p̸)`. -/
theorem mass_sub_slash_mul_slash (m : ℝ) (p : Fin 4 → ℝ) (hp : Minkowski.dot p p = -m ^ 2) :
    ((m : ℂ) • 𝟙 - slash p) * slash p = (-(m : ℂ)) • ((m : ℂ) • 𝟙 - slash p) := by
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, slash_mul_slash, hp]
  push_cast
  module

/-- `a^μ γ_μ = a̸`. -/
theorem sum_smul_gammaLower (a : Fin 4 → ℝ) :
    ∑ μ, ((a μ : ℝ) : ℂ) • gammaLower μ = slash a := by
  simp only [gammaLower, slash, Minkowski.lower, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Complex.ofReal_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Minkowski.metric_symm]
  push_cast
  ring_nf

/-- If `(y L) M (R x) = 0` for all vectors `x` and `y`, then `L M R = 0`. -/
theorem mul_mul_eq_zero_of_sandwich {L M R : Matrix (Fin 4) (Fin 4) ℂ}
    (h : ∀ x y : Fin 4 → ℂ, (y ᵥ* L) ⬝ᵥ (M *ᵥ (R *ᵥ x)) = 0) : L * M * R = 0 := by
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  rw [← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, single_one_dotProduct,
    mulVec_single_one] at this
  exact this

/-- The Gordon identity on the vertex structure: if `(p̸ + m) u = 0` and `w (p̸' + m) = 0`,
then `w [A γ^μ - (i/m) B S^{μν} q_ν] u = w [(A + B) γ^μ - (B / 2m) (p' + p)^μ] u`
with `q = p' - p`. -/
theorem sandwich_formFactor_eq {m : ℝ} (hm : m ≠ 0) {p' p : Fin 4 → ℝ} {u w : Fin 4 → ℂ}
    (hu : slash p *ᵥ u = -((m : ℂ) • u)) (hw : w ᵥ* slash p' = -((m : ℂ) • w)) (A B : ℂ)
    (μ : Fin 4) :
    w ⬝ᵥ ((A • gamma μ - (I / (m : ℂ) * B) •
        ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • lorentzGen μ ν) *ᵥ u) =
      w ⬝ᵥ (((A + B) • gamma μ - (B / (2 * m) * ((p' μ + p μ : ℝ) : ℂ)) • 𝟙) *ᵥ u) := by
  have hg := gordon m p p' u w hu hw μ
  have hl : ∀ ν, Minkowski.lower (p' - p) ν = Minkowski.lower p' ν - Minkowski.lower p ν := by
    intro ν
    simp only [Minkowski.lower, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hm' : (m : ℂ) * (m : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast hm)
  simp only [hl]
  simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul] at hg ⊢
  linear_combination (-B / (2 * m)) * hg + B * (w ⬝ᵥ (gamma μ *ᵥ u)) * hm'

/-- Linear independence of `ū'γ^μu` and `ū'S^{μν}q_νu` on shell for `q² > 0`. -/
theorem eq_zero_of_sandwich_formFactor_eq_zero {m : ℝ} (hm : 0 < m) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) {A B : ℂ}
    (h : ∀ (μ : Fin 4) (u w : Fin 4 → ℂ), slash p *ᵥ u = -((m : ℂ) • u) →
      w ᵥ* slash p' = -((m : ℂ) • w) →
      w ⬝ᵥ ((A • gamma μ - (I / (m : ℂ) * B) •
        ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • lorentzGen μ ν) *ᵥ u) = 0) :
    A = 0 ∧ B = 0 := by
  set P : Matrix (Fin 4) (Fin 4) ℂ := (m : ℂ) • 𝟙 - slash p with hP
  set P' : Matrix (Fin 4) (Fin 4) ℂ := (m : ℂ) • 𝟙 - slash p' with hP'
  have hPs : slash p * P = (-(m : ℂ)) • P := slash_mul_mass_sub_slash m p hp
  have hP's : P' * slash p' = (-(m : ℂ)) • P' := mass_sub_slash_mul_slash m p' hp'
  clear_value P P'
  have hu : ∀ x, slash p *ᵥ (P *ᵥ x) = -((m : ℂ) • (P *ᵥ x)) := fun x => by
    rw [mulVec_mulVec, hPs, smul_mulVec, neg_smul]
  have hw : ∀ y, (y ᵥ* P') ᵥ* slash p' = -((m : ℂ) • (y ᵥ* P')) := fun y => by
    rw [vecMul_vecMul, hP's, vecMul_smul, neg_smul]
  have hE : ∀ μ, (A + B) • (P' * gamma μ * P) =
      (B / (2 * m) * ((p' μ + p μ : ℝ) : ℂ)) • (P' * P) := by
    intro μ
    have h0 : P' * ((A + B) • gamma μ - (B / (2 * m) * ((p' μ + p μ : ℝ) : ℂ)) • 𝟙) * P = 0 :=
      mul_mul_eq_zero_of_sandwich fun x y =>
        (sandwich_formFactor_eq hm.ne' (hu x) (hw y) A B μ).symm.trans (h μ _ _ (hu x) (hw y))
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one] at h0
    exact sub_eq_zero.mp h0
  -- Contract with `(p' + p)_μ`; on shell `P' (p̸' + p̸) P = -2m P' P`.
  have E1 : (A + B) • (P' * slash (p' + p) * P) =
      (B / (2 * m) * (Minkowski.dot (p' + p) (p' + p) : ℂ)) • (P' * P) := by
    calc (A + B) • (P' * slash (p' + p) * P)
        = ∑ μ, ((Minkowski.lower (p' + p) μ : ℝ) : ℂ) • ((A + B) • (P' * gamma μ * P)) := by
          simp only [slash, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
            Finset.smul_sum]
          exact Finset.sum_congr rfl fun μ _ => smul_comm _ _ _
      _ = ∑ μ, ((Minkowski.lower (p' + p) μ : ℝ) : ℂ) •
            ((B / (2 * m) * ((p' μ + p μ : ℝ) : ℂ)) • (P' * P)) := by
          simp only [hE]
      _ = _ := by
          rw [Minkowski.dot_eq_sum_lower]
          simp only [smul_smul, ← Finset.sum_smul]
          congr 1
          push_cast [Complex.ofReal_sum, Pi.add_apply]
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun μ _ => by ring
  have E1' : (A + B) * (-(2 * m : ℂ) * trace (P' * P)) =
      B / (2 * m) * (Minkowski.dot (p' + p) (p' + p) : ℂ) * trace (P' * P) := by
    have e : P' * slash (p' + p) * P = (-(2 * m : ℂ)) • (P' * P) := by
      rw [slash_add, Matrix.mul_add, Matrix.add_mul, hP's, Matrix.mul_assoc P' (slash p) P, hPs]
      simp only [Matrix.smul_mul, Matrix.mul_smul]
      module
    have := congrArg trace E1
    rw [e, smul_smul, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul] at this
    linear_combination this
  -- Multiply by `γ_μ` on the right and contract over `μ`.
  have E2 : (A + B) * trace (P' * ((m : ℂ) • ((-4 : ℂ) • 𝟙) - (2 : ℂ) • slash p)) =
      B / (2 * m) * trace (P' * P * slash (p' + p)) := by
    have hcontr : ∑ μ, gamma μ * P * gammaLower μ =
        (m : ℂ) • ((-4 : ℂ) • 𝟙) - (2 : ℂ) • slash p := by
      rw [← contract_one, ← contract_slash, hP, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    have hsum : ∑ μ, (A + B) • (P' * gamma μ * P * gammaLower μ) =
        ∑ μ, (B / (2 * m) * ((p' μ + p μ : ℝ) : ℂ)) • (P' * P * gammaLower μ) :=
      Finset.sum_congr rfl fun μ _ => by rw [← Matrix.smul_mul, hE μ, Matrix.smul_mul]
    have hl : ∑ μ, (A + B) • (P' * gamma μ * P * gammaLower μ) =
        (A + B) • (P' * ((m : ℂ) • ((-4 : ℂ) • 𝟙) - (2 : ℂ) • slash p)) := by
      rw [← hcontr, Finset.mul_sum, Finset.smul_sum]
      simp only [Matrix.mul_assoc]
    have hr : ∑ μ, (B / (2 * m) * ((p' μ + p μ : ℝ) : ℂ)) • (P' * P * gammaLower μ) =
        (B / (2 * m)) • (P' * P * slash (p' + p)) := by
      rw [← sum_smul_gammaLower, Finset.mul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [Matrix.mul_smul, smul_smul, Pi.add_apply]
    have := congrArg trace (hl.symm.trans (hsum.trans hr))
    rwa [trace_smul, trace_smul, smul_eq_mul, smul_eq_mul] at this
  -- The traces of the three matrices that appear.
  have T1 : trace (P' * P) = 4 * (m : ℂ) ^ 2 - 4 * (Minkowski.dot p' p : ℂ) := by
    rw [hP, hP']
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, trace_sub, trace_smul, trace_one, Fintype.card_fin, trace_slash,
      trace_slash_mul_slash, smul_eq_mul]
    push_cast
    ring
  have T2 : trace (P' * ((m : ℂ) • ((-4 : ℂ) • 𝟙) - (2 : ℂ) • slash p)) =
      -16 * (m : ℂ) ^ 2 - 8 * (Minkowski.dot p' p : ℂ) := by
    rw [hP']
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, trace_sub, trace_smul, trace_one, Fintype.card_fin, trace_slash,
      trace_slash_mul_slash, smul_eq_mul]
    push_cast
    ring
  have T3 : trace (P' * P * slash (p' + p)) =
      4 * (m : ℂ) * (Minkowski.dot (p' + p) (p' + p) : ℂ) := by
    have hk : Minkowski.dot (p' + p) (p' + p) =
        Minkowski.dot p' (p' + p) + Minkowski.dot p (p' + p) := by
      simp only [Minkowski.dot_eq, Pi.add_apply]
      ring
    rw [hP, hP', hk]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, trace_sub, trace_smul, trace_slash, trace_slash_mul_slash,
      trace_slash_mul_slash_mul_slash, smul_eq_mul]
    push_cast
    ring
  -- Kinematics: `q² = -2m² - 2 p'·p` and `(p' + p)² = -2m² + 2 p'·p`.
  have hQ : Minkowski.dot (p' - p) (p' - p) = -2 * m ^ 2 - 2 * Minkowski.dot p' p := by
    have e : Minkowski.dot (p' - p) (p' - p) =
        Minkowski.dot p' p' - 2 * Minkowski.dot p' p + Minkowski.dot p p := by
      simp only [Minkowski.dot_eq, Pi.sub_apply]
      ring
    rw [e, hp, hp']
    ring
  have hK : Minkowski.dot (p' + p) (p' + p) = -2 * m ^ 2 + 2 * Minkowski.dot p' p := by
    have e : Minkowski.dot (p' + p) (p' + p) =
        Minkowski.dot p' p' + 2 * Minkowski.dot p' p + Minkowski.dot p p := by
      simp only [Minkowski.dot_eq, Pi.add_apply]
      ring
    rw [e, hp, hp']
    ring
  have hm2 : 0 < m ^ 2 := pow_pos hm 2
  have hT1 : trace (P' * P) ≠ 0 := by
    rw [T1]
    have e : 4 * (m : ℂ) ^ 2 - 4 * (Minkowski.dot p' p : ℂ) =
        ((4 * m ^ 2 - 4 * Minkowski.dot p' p : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.ofReal_ne_zero]
    linarith
  have e1 : (A + B) * (-(2 * m : ℂ)) =
      B / (2 * m) * (-2 * (m : ℂ) ^ 2 + 2 * (Minkowski.dot p' p : ℂ)) := by
    have e : ((A + B) * (-(2 * m : ℂ)) -
        B / (2 * m) * (-2 * (m : ℂ) ^ 2 + 2 * (Minkowski.dot p' p : ℂ))) * trace (P' * P) = 0 := by
      rw [hK] at E1'
      push_cast at E1'
      linear_combination E1'
    rcases mul_eq_zero.mp e with e | e
    · linear_combination e
    · exact absurd e hT1
  have e2 : (A + B) * (-16 * (m : ℂ) ^ 2 - 8 * (Minkowski.dot p' p : ℂ)) =
      B / (2 * m) * (4 * (m : ℂ) * (-2 * (m : ℂ) ^ 2 + 2 * (Minkowski.dot p' p : ℂ))) := by
    rw [← T2, E2, T3, hK]
    push_cast
    ring
  have key : B / (2 * m) * ((((-2 * m ^ 2 + 2 * Minkowski.dot p' p) *
      (-2 * m ^ 2 - 2 * Minkowski.dot p' p)) : ℝ) : ℂ) = 0 := by
    push_cast
    linear_combination (-1 / 4 : ℂ) *
      ((-16 * (m : ℂ) ^ 2 - 8 * (Minkowski.dot p' p : ℂ)) * e1 + 2 * (m : ℂ) * e2)
  have hKQ : (-2 * m ^ 2 + 2 * Minkowski.dot p' p) * (-2 * m ^ 2 - 2 * Minkowski.dot p' p) ≠ 0 :=
    mul_ne_zero (by linarith) (by linarith)
  have hm' : (2 * m : ℂ) ≠ 0 := by
    have : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
    exact mul_ne_zero two_ne_zero this
  have hB : B = 0 := by
    rcases mul_eq_zero.mp key with h1 | h1
    · rcases div_eq_zero_iff.mp h1 with h2 | h2
      · exact h2
      · exact absurd h2 hm'
    · exact absurd (Complex.ofReal_eq_zero.mp h1) hKQ
  have hA : A = 0 := by
    rw [hB, add_zero, zero_div, zero_mul] at e1
    rcases mul_eq_zero.mp e1 with h1 | h1
    · exact h1
    · exact absurd (neg_eq_zero.mp h1) hm'
  exact ⟨hA, hB⟩

end QED.Dirac

end
