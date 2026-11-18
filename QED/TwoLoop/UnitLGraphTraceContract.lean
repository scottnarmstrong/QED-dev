/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLGraphTracePlanar
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# The Lorentz contractions of the ladder chain

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the L link, graph half. After the Pauli
projection the ladder numerator is a combination of the traces
`tr(γ^ν P_μ γ_ν Y₀ γ^ρ Y₁ γ^μ Y₂ γ_ρ Y₃)` summed over `μ, ν, ρ` (`lw`), with `P_μ` the Pauli
matrix and `Y₀, …, Y₃` the electron numerators, or, after Wick's rule, with one or two of the
`Yₖ` replaced by a contracted pair `γ_σ, γ^σ`. This file reduces all of them to the planar
subalgebra of `QED/TwoLoop/UnitLGraphTracePlanar.lean`:

* `lw_planar`, `omL_planar`, `omR_planar`, `f3_planar`: when `P_μ` is planar for `μ = 0, 1` and
  of the form `R γ^μ` (`R` planar) for `μ = 2, 3` (`PlanarPauli`), and the inserted matrices are
  planar, the four contraction patterns are explicit planar expressions (`lwPl`, …). The
  transverse indices are moved to the right by `γⁱ X = X̄ γⁱ` and the contractions use
  `γ^ν X γ_ν = Γ(X)`, `γ^ν X γⁱ γ_ν = Γ_T(X) γⁱ`;
* the six single contractions of slots and the three double contractions are reduced to these
  patterns by the identities `γ_σ γ^ρ γ^σ = 2 γ^ρ`, `γ_σ γ^ρ a̸ γ^μ γ^σ γ_ρ = -8 γ^μ a̸`,
  `γ_σ γ^ρ γ^μ γ^σ γ_ρ = 4 γ^μ` and their mirror images (`sum_lw_01`, …, `sum_lw_0312`).
-/

@[expose] public section

open Complex Matrix

namespace QED.TwoLoop.UnitLGraphTrace

open QED.Dirac
open QED.TwoLoop.Bridge (electronNumerator)
open Pl

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-! ### The contraction patterns -/

section Patterns

variable (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₁ Y₂ Y₃ Z : Matrix (Fin 4) (Fin 4) ℂ)

/-- **The ladder contraction** `∑_{μνρ} tr(γ^ν P_μ γ_ν Y₀ γ^ρ Y₁ γ^μ Y₂ γ_ρ Y₃)`. -/
noncomputable def lw : ℂ :=
  ∑ μ, ∑ ν, ∑ ρ, trace (gamma ν * P μ * gammaLower ν * Y₀ * gamma ρ * Y₁ * gamma μ * Y₂ *
    gammaLower ρ * Y₃)

/-- The pattern `∑_{μν} tr(γ^ν P_μ γ_ν γ^μ Z)`. -/
noncomputable def omL : ℂ := ∑ μ, ∑ ν, trace (gamma ν * P μ * gammaLower ν * gamma μ * Z)

/-- The pattern `∑_{μν} tr(γ^ν P_μ γ_ν Z γ^μ)`. -/
noncomputable def omR : ℂ := ∑ μ, ∑ ν, trace (gamma ν * P μ * gammaLower ν * Z * gamma μ)

/-- The pattern `∑_{μσνρ} tr(γ^σ γ^ν P_μ γ_ν γ_σ γ^ρ Y₁ γ^μ Y₂ γ_ρ)`. -/
noncomputable def f3 : ℂ :=
  ∑ μ, ∑ σ, ∑ ν, ∑ ρ, trace (gamma σ * gamma ν * P μ * gammaLower ν * gammaLower σ * gamma ρ * Y₁ *
    gamma μ * Y₂ * gammaLower ρ)

end Patterns

/-! ### The planar evaluation -/

/-- `P_μ` is planar for `μ = 0, 1` and `R γ^μ` with `R` planar for `μ = 2, 3`. -/
def PlanarPauli (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Q₀ Q₁ R : Pl) : Prop :=
  P 0 = toMat Q₀ ∧ P 1 = toMat Q₁ ∧ P 2 = toMat R * gamma 2 ∧ P 3 = toMat R * gamma 3

section Planar

variable (Q₀ Q₁ R y₀ y₁ y₂ y₃ z : Pl)

/-- The planar value of `lw`. -/
def lwPl : ℂ :=
  4 * (gam Q₀ * y₀ * gam (y₁ * g0 * y₂) * y₃).s + 4 * (gam Q₁ * y₀ * gam (y₁ * g1 * y₂) * y₃).s -
    8 * (gamT R * bar y₀ * bar (gamT (y₁ * bar y₂)) * y₃).s

/-- The planar value of `omL`. -/
def omLPl : ℂ := 4 * (gam Q₀ * g0 * z).s + 4 * (gam Q₁ * g1 * z).s - 8 * (gamT R * z).s

/-- The planar value of `omR`. -/
def omRPl : ℂ := 4 * (gam Q₀ * z * g0).s + 4 * (gam Q₁ * z * g1).s - 8 * (gamT R * bar z).s

/-- The planar value of `f3`. -/
def f3Pl : ℂ :=
  4 * (gam (gam Q₀) * gam (y₁ * g0 * y₂)).s + 4 * (gam (gam Q₁) * gam (y₁ * g1 * y₂)).s -
    8 * (gamT (gamT R) * bar (gamT (y₁ * bar y₂))).s

end Planar

/-- Pulling the two inner sums of `lw` into the trace. -/
theorem lw_term (X Y₀ Y₁ M Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ ν, ∑ ρ, trace (gamma ν * X * gammaLower ν * Y₀ * gamma ρ * Y₁ * M * Y₂ * gammaLower ρ * Y₃) =
      trace ((∑ ν, gamma ν * X * gammaLower ν) * Y₀ *
        (∑ ρ, gamma ρ * (Y₁ * M * Y₂) * gammaLower ρ) * Y₃) := by
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
  exact Finset.sum_comm

theorem omL_term (X M Z : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ ν, trace (gamma ν * X * gammaLower ν * M * Z) =
      trace ((∑ ν, gamma ν * X * gammaLower ν) * M * Z) := by
  simp only [Matrix.sum_mul, Matrix.trace_sum]

/-- **The planar evaluation of the ladder contraction.** -/
theorem lw_planar {P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {Q₀ Q₁ R : Pl} (hP : PlanarPauli P Q₀ Q₁ R)
    (y₀ y₁ y₂ y₃ : Pl) :
    lw P (toMat y₀) (toMat y₁) (toMat y₂) (toMat y₃) = lwPl Q₀ Q₁ R y₀ y₁ y₂ y₃ := by
  obtain ⟨h0, h1, h2, h3⟩ := hP
  unfold lw
  rw [Fin.sum_univ_four]
  simp only [lw_term]
  rw [h0, h1, h2, h3]
  simp only [gamma_zero, gamma_one, toMat_mul, toMat_mul_gamma_two_mul, toMat_mul_gamma_three_mul,
    sum_gamma_toMat, sum_gamma_toMat_gamma_two, sum_gamma_toMat_gamma_three,
    toMat_gamma_two_mul_toMat_gamma_two, toMat_gamma_three_mul_toMat_gamma_three, trace_toMat,
    neg_mul', neg_s, lwPl]
  ring

/-- **The planar evaluation of `omL`.** -/
theorem omL_planar {P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {Q₀ Q₁ R : Pl}
    (hP : PlanarPauli P Q₀ Q₁ R)
    (z : Pl) : omL P (toMat z) = omLPl Q₀ Q₁ R z := by
  obtain ⟨h0, h1, h2, h3⟩ := hP
  unfold omL
  rw [Fin.sum_univ_four]
  simp only [omL_term]
  rw [h0, h1, h2, h3]
  simp only [gamma_zero, gamma_one, toMat_mul,
    sum_gamma_toMat, sum_gamma_toMat_gamma_two, sum_gamma_toMat_gamma_three, toMat_gamma_two_sq,
    toMat_gamma_three_sq, trace_toMat, neg_mul', neg_s, omLPl]
  ring

/-- **The planar evaluation of `omR`.** -/
theorem omR_planar {P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {Q₀ Q₁ R : Pl}
    (hP : PlanarPauli P Q₀ Q₁ R)
    (z : Pl) : omR P (toMat z) = omRPl Q₀ Q₁ R z := by
  obtain ⟨h0, h1, h2, h3⟩ := hP
  unfold omR
  rw [Fin.sum_univ_four]
  simp only [omL_term]
  rw [h0, h1, h2, h3]
  simp only [gamma_zero, gamma_one, toMat_mul, toMat_mul_gamma_two_mul, toMat_mul_gamma_three_mul,
    sum_gamma_toMat, sum_gamma_toMat_gamma_two, sum_gamma_toMat_gamma_three, toMat_gamma_two_sq,
    toMat_gamma_three_sq, trace_toMat, neg_s, omRPl]
  ring

theorem f3_term (X Y₁ M Y₂ : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ σ, ∑ ν, ∑ ρ, trace (gamma σ * gamma ν * X * gammaLower ν * gammaLower σ * gamma ρ * Y₁ * M *
      Y₂ * gammaLower ρ) =
    trace ((∑ σ, gamma σ * (∑ ν, gamma ν * X * gammaLower ν) * gammaLower σ) *
      (∑ ρ, gamma ρ * (Y₁ * M * Y₂) * gammaLower ρ)) := by
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
  exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

/-- **The planar evaluation of `f3`.** -/
theorem f3_planar {P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {Q₀ Q₁ R : Pl} (hP : PlanarPauli P Q₀ Q₁ R)
    (y₁ y₂ : Pl) : f3 P (toMat y₁) (toMat y₂) = f3Pl Q₀ Q₁ R y₁ y₂ := by
  obtain ⟨h0, h1, h2, h3⟩ := hP
  unfold f3
  rw [Fin.sum_univ_four]
  simp only [f3_term]
  rw [h0, h1, h2, h3]
  simp only [gamma_zero, gamma_one, toMat_mul, toMat_mul_gamma_two_mul, toMat_mul_gamma_three_mul,
    sum_gamma_toMat, sum_gamma_toMat_gamma_two, sum_gamma_toMat_gamma_three,
    toMat_gamma_two_mul_toMat_gamma_two, toMat_gamma_three_mul_toMat_gamma_three, trace_toMat,
    neg_s, f3Pl]
  ring

/-! ### The contracted slot pairs -/

theorem sum_gammaLower_swap (X : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ σ, gammaLower σ * X * gamma σ = ∑ σ, gamma σ * X * gammaLower σ := by
  simp only [Fin.sum_univ_four, gammaLower_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    Matrix.neg_mul, Matrix.mul_neg]

theorem sum_gammaLower_swap3 (A B C : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ σ, gammaLower σ * A * B * C * gamma σ = ∑ σ, gamma σ * A * B * C * gammaLower σ := by
  simpa only [Matrix.mul_assoc] using sum_gammaLower_swap (A * B * C)

theorem sum_gammaLower_swap2 (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ σ, gammaLower σ * A * B * gamma σ = ∑ σ, gamma σ * A * B * gammaLower σ := by
  simpa only [Matrix.mul_assoc] using sum_gammaLower_swap (A * B)

theorem toMat_eq_gamma_two : gamma 2 = toMat 1 * gamma 2 := by rw [toMat_one, Matrix.one_mul]

theorem toMat_eq_gamma_three : gamma 3 = toMat 1 * gamma 3 := by rw [toMat_one, Matrix.one_mul]

/-- `γ_σ γ^ρ γ^σ = 2 γ^ρ`. -/
theorem sum_gammaLower_gamma_gamma (ρ : Fin 4) :
    ∑ σ, gammaLower σ * gamma ρ * gamma σ = (2 : ℂ) • gamma ρ := by
  rw [sum_gammaLower_swap]
  fin_cases ρ
  · simp only [Fin.zero_eta, gamma_zero, sum_gamma_toMat, ← toMat_smul]
    congr 1; ext <;> simp [g0]
  · simp only [Fin.mk_one, gamma_one, sum_gamma_toMat, ← toMat_smul]
    congr 1; ext <;> simp [g1]
  · simp only [Fin.reduceFinMk]
    conv_lhs => rw [toMat_eq_gamma_two]
    rw [sum_gamma_toMat_gamma_two, show gamT 1 = (2 : ℂ) • 1 by ext <;> simp, toMat_smul,
      toMat_one, Matrix.smul_mul, Matrix.one_mul]
  · simp only [Fin.reduceFinMk]
    conv_lhs => rw [toMat_eq_gamma_three]
    rw [sum_gamma_toMat_gamma_three, show gamT 1 = (2 : ℂ) • 1 by ext <;> simp, toMat_smul,
      toMat_one, Matrix.smul_mul, Matrix.one_mul]

/-- `γ_σ γ_ρ γ^σ = 2 γ_ρ`. -/
theorem sum_gammaLower_gammaLower_gamma (ρ : Fin 4) :
    ∑ σ, gammaLower σ * gammaLower ρ * gamma σ = (2 : ℂ) • gammaLower ρ := by
  have h : gammaLower ρ = ((Minkowski.metric ρ ρ : ℝ) : ℂ) • gamma ρ := by
    fin_cases ρ <;> simp [gammaLower_eq, Minkowski.metric]
  rw [h]
  simp only [Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum, sum_gammaLower_gamma_gamma,
    smul_comm ((Minkowski.metric ρ ρ : ℝ) : ℂ) (2 : ℂ)]

/-- The vector with `slash = γ^ρ`. -/
def upV (ρ : Fin 4) : Fin 4 → ℝ := fun ν => if ν = ρ then Minkowski.metric ρ ρ else 0

/-- The vector with `slash = γ_ρ`. -/
def loV (ρ : Fin 4) : Fin 4 → ℝ := fun ν => if ν = ρ then 1 else 0

theorem slash_upV (ρ : Fin 4) : slash (upV ρ) = gamma ρ := by
  fin_cases ρ <;> simp [slash, Fin.sum_univ_four, Minkowski.lower_eq, upV, Minkowski.metric]

theorem slash_loV (ρ : Fin 4) : slash (loV ρ) = gammaLower ρ := by
  fin_cases ρ <;> simp [slash, Fin.sum_univ_four, Minkowski.lower_eq, loV, gammaLower_eq]

theorem sum_dot_upV_smul_gammaLower (μ : Fin 4) :
    ∑ ρ, ((Minkowski.dot (upV ρ) (upV μ) : ℝ) : ℂ) • gammaLower ρ = gamma μ := by
  fin_cases μ <;>
    simp [upV, Minkowski.dot_eq, Minkowski.metric, gammaLower_eq]

theorem sum_dot_loV_smul_gamma (μ : Fin 4) :
    ∑ ρ, ((Minkowski.dot (upV μ) (loV ρ) : ℝ) : ℂ) • gamma ρ = gamma μ := by
  fin_cases μ <;> simp [upV, loV, Minkowski.dot_eq, Minkowski.metric]

/-- `γ_σ γ^ρ γ^μ γ^σ γ_ρ = 4 γ^μ`. -/
theorem sum_contract02_one (μ : Fin 4) :
    ∑ ρ, ∑ σ, gammaLower σ * gamma ρ * gamma μ * gamma σ * gammaLower ρ = (4 : ℂ) • gamma μ := by
  have h : ∀ ρ, ∑ σ, gammaLower σ * gamma ρ * gamma μ * gamma σ =
      ((4 * Minkowski.dot (upV ρ) (upV μ) : ℝ) : ℂ) • 𝟙 := fun ρ => by
    rw [sum_gammaLower_swap2, ← contract_slash_slash, slash_upV, slash_upV]
  simp only [← Matrix.sum_mul, h, Matrix.smul_mul, Matrix.one_mul]
  rw [← sum_dot_upV_smul_gammaLower μ, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [smul_smul]
  push_cast
  rfl

/-- `γ_σ γ^ρ a̸ γ^μ γ^σ γ_ρ = -8 γ^μ a̸`. -/
theorem sum_contract02_slash (μ : Fin 4) (a : Fin 4 → ℝ) :
    ∑ ρ, ∑ σ, gammaLower σ * gamma ρ * slash a * gamma μ * gamma σ * gammaLower ρ =
      (-8 : ℂ) • (gamma μ * slash a) := by
  have h : ∀ ρ, ∑ σ, gammaLower σ * gamma ρ * slash a * gamma μ * gamma σ =
      (2 : ℂ) • (gamma μ * slash a * gamma ρ) := fun ρ => by
    rw [sum_gammaLower_swap3]
    have := contract_slash_slash_slash (upV ρ) a (upV μ)
    rwa [slash_upV, slash_upV] at this
  simp only [← Matrix.sum_mul, h, Matrix.smul_mul, ← Finset.smul_sum]
  simp only [Matrix.mul_assoc, ← Matrix.mul_sum, contract_one, Matrix.mul_smul, Matrix.mul_one,
    smul_smul]
  norm_num

/-- `γ^ρ γ_σ γ^μ γ_ρ γ^σ = 4 γ^μ`. -/
theorem sum_contract13_one (μ : Fin 4) :
    ∑ ρ, ∑ σ, gamma ρ * gammaLower σ * gamma μ * gammaLower ρ * gamma σ = (4 : ℂ) • gamma μ := by
  have h : ∀ ρ, ∑ σ, gammaLower σ * gamma μ * gammaLower ρ * gamma σ =
      ((4 * Minkowski.dot (upV μ) (loV ρ) : ℝ) : ℂ) • 𝟙 := fun ρ => by
    rw [sum_gammaLower_swap2, ← contract_slash_slash, slash_upV, slash_loV]
  have e : ∀ ρ, ∑ σ, gamma ρ * gammaLower σ * gamma μ * gammaLower ρ * gamma σ =
      gamma ρ * ∑ σ, gammaLower σ * gamma μ * gammaLower ρ * gamma σ := fun ρ => by
    simp only [Matrix.mul_sum, Matrix.mul_assoc]
  simp only [e, h, Matrix.mul_smul, Matrix.mul_one]
  rw [← sum_dot_loV_smul_gamma μ, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [smul_smul]
  push_cast
  rfl

/-- `γ^ρ γ_σ γ^μ a̸ γ_ρ γ^σ = -8 a̸ γ^μ`. -/
theorem sum_contract13_slash (μ : Fin 4) (a : Fin 4 → ℝ) :
    ∑ ρ, ∑ σ, gamma ρ * gammaLower σ * gamma μ * slash a * gammaLower ρ * gamma σ =
      (-8 : ℂ) • (slash a * gamma μ) := by
  have h : ∀ ρ, ∑ σ, gammaLower σ * gamma μ * slash a * gammaLower ρ * gamma σ =
      (2 : ℂ) • (gammaLower ρ * slash a * gamma μ) := fun ρ => by
    rw [sum_gammaLower_swap3]
    have := contract_slash_slash_slash (upV μ) a (loV ρ)
    rwa [slash_upV, slash_loV] at this
  have e : ∀ ρ, ∑ σ, gamma ρ * gammaLower σ * gamma μ * slash a * gammaLower ρ * gamma σ =
      gamma ρ * ∑ σ, gammaLower σ * gamma μ * slash a * gammaLower ρ * gamma σ := fun ρ => by
    simp only [Matrix.mul_sum, Matrix.mul_assoc]
  simp only [e, h, Matrix.mul_smul, ← Finset.smul_sum]
  simp only [← Matrix.mul_assoc, ← Matrix.sum_mul, contract_one, Matrix.smul_mul, Matrix.one_mul,
    smul_smul]
  norm_num

/-- The electron numerator in the pattern `(0, 2)`: `γ_σ γ^ρ (m - k̸) γ^μ γ^σ γ_ρ = γ^μ (4m +
8k̸)`. -/
theorem sum_contract02_elec (μ : Fin 4) (m : ℝ) (k : Fin 4 → ℝ) :
    ∑ ρ, ∑ σ, gammaLower σ * gamma ρ * electronNumerator m k * gamma μ * gamma σ * gammaLower ρ =
      gamma μ * ((4 * (m : ℂ)) • 𝟙 + (8 : ℂ) • slash k) := by
  have e : ∀ ρ σ, gammaLower σ * gamma ρ * electronNumerator m k * gamma μ * gamma σ *
      gammaLower ρ = (m : ℂ) • (gammaLower σ * gamma ρ * gamma μ * gamma σ * gammaLower ρ) -
        gammaLower σ * gamma ρ * slash k * gamma μ * gamma σ * gammaLower ρ := fun ρ σ => by
    simp only [electronNumerator, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one]
  simp only [e, Finset.sum_sub_distrib, ← Finset.smul_sum, sum_contract02_one,
    sum_contract02_slash, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  module

/-- The electron numerator in the pattern `(1, 3)`: `γ^ρ γ_σ γ^μ (m - k̸) γ_ρ γ^σ = (4m + 8k̸)
γ^μ`. -/
theorem sum_contract13_elec (μ : Fin 4) (m : ℝ) (k : Fin 4 → ℝ) :
    ∑ ρ, ∑ σ, gamma ρ * gammaLower σ * gamma μ * electronNumerator m k * gammaLower ρ * gamma σ =
      ((4 * (m : ℂ)) • 𝟙 + (8 : ℂ) • slash k) * gamma μ := by
  have e : ∀ ρ σ, gamma ρ * gammaLower σ * gamma μ * electronNumerator m k * gammaLower ρ *
      gamma σ = (m : ℂ) • (gamma ρ * gammaLower σ * gamma μ * gammaLower ρ * gamma σ) -
        gamma ρ * gammaLower σ * gamma μ * slash k * gammaLower ρ * gamma σ := fun ρ σ => by
    simp only [electronNumerator, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one]
  simp only [e, Finset.sum_sub_distrib, ← Finset.smul_sum, sum_contract13_one,
    sum_contract13_slash, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, smul_smul]
  module

theorem sum_comm4 (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

section Slots

variable (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ)

/-- **Slots `0, 1` contracted**: the pattern reduces to `lw` with `Y₀ = 2`, `Y₁ = 1`. -/
theorem sum_lw_01 : ∑ σ, lw P (gammaLower σ) (gamma σ) Y₂ Y₃ = lw P ((2 : ℂ) • 𝟙) 𝟙 Y₂ Y₃ := by
  unfold lw
  rw [sum_comm4]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun ρ _ => ?_
  calc _ = trace (gamma ν * P μ * gammaLower ν * (∑ σ, gammaLower σ * gamma ρ * gamma σ) *
        gamma μ * Y₂ * gammaLower ρ * Y₃) := by
        simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
    _ = _ := by
        rw [sum_gammaLower_gamma_gamma]
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
          Matrix.mul_assoc]

/-- **Slots `1, 2` contracted**: the pattern reduces to `lw` with `Y₁ = 2`, `Y₂ = 1`. -/
theorem sum_lw_12 : ∑ σ, lw P Y₀ (gammaLower σ) (gamma σ) Y₃ = lw P Y₀ ((2 : ℂ) • 𝟙) 𝟙 Y₃ := by
  unfold lw
  rw [sum_comm4]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun ρ _ => ?_
  calc _ = trace (gamma ν * P μ * gammaLower ν * Y₀ * gamma ρ *
        (∑ σ, gammaLower σ * gamma μ * gamma σ) * gammaLower ρ * Y₃) := by
        simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
    _ = _ := by
        rw [sum_gammaLower_gamma_gamma]
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
          Matrix.mul_assoc]

/-- **Slots `2, 3` contracted**: the pattern reduces to `lw` with `Y₂ = 2`, `Y₃ = 1`. -/
theorem sum_lw_23 : ∑ σ, lw P Y₀ Y₁ (gammaLower σ) (gamma σ) = lw P Y₀ Y₁ ((2 : ℂ) • 𝟙) 𝟙 := by
  unfold lw
  rw [sum_comm4]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun ρ _ => ?_
  calc _ = trace (gamma ν * P μ * gammaLower ν * Y₀ * gamma ρ * Y₁ * gamma μ *
        (∑ σ, gammaLower σ * gammaLower ρ * gamma σ)) := by
        simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
    _ = _ := by
        rw [sum_gammaLower_gammaLower_gamma]
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
          Matrix.mul_assoc]

/-- **Slots `0, 2` contracted**, for any `Y₁` with `γ_σ γ^ρ Y₁ γ^μ γ^σ γ_ρ = γ^μ W`. -/
theorem sum_lw_02 (W : Matrix (Fin 4) (Fin 4) ℂ)
    (hW : ∀ μ, ∑ ρ, ∑ σ, gammaLower σ * gamma ρ * Y₁ * gamma μ * gamma σ * gammaLower ρ =
      gamma μ * W) :
    ∑ σ, lw P (gammaLower σ) Y₁ (gamma σ) Y₃ = omL P (W * Y₃) := by
  unfold lw omL
  rw [sum_comm4]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  calc _ = trace (gamma ν * P μ * gammaLower ν *
        (∑ ρ, ∑ σ, gammaLower σ * gamma ρ * Y₁ * gamma μ * gamma σ * gammaLower ρ) * Y₃) := by
        simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
    _ = _ := by
        rw [hW]
        simp only [Matrix.mul_assoc]

/-- **Slots `1, 3` contracted**, for any `Y₂` with `γ^ρ γ_σ γ^μ Y₂ γ_ρ γ^σ = W γ^μ`. -/
theorem sum_lw_13 (W : Matrix (Fin 4) (Fin 4) ℂ)
    (hW : ∀ μ, ∑ ρ, ∑ σ, gamma ρ * gammaLower σ * gamma μ * Y₂ * gammaLower ρ * gamma σ =
      W * gamma μ) :
    ∑ σ, lw P Y₀ (gammaLower σ) Y₂ (gamma σ) = omR P (Y₀ * W) := by
  unfold lw omR
  rw [sum_comm4]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  calc _ = trace (gamma ν * P μ * gammaLower ν * Y₀ *
        (∑ ρ, ∑ σ, gamma ρ * gammaLower σ * gamma μ * Y₂ * gammaLower ρ * gamma σ)) := by
        simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
    _ = _ := by
        rw [hW]
        simp only [Matrix.mul_assoc]

/-- **Slots `0, 3` contracted**: the pattern `f3`. -/
theorem sum_lw_03 : ∑ σ, lw P (gammaLower σ) Y₁ Y₂ (gamma σ) = f3 P Y₁ Y₂ := by
  unfold lw f3
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun σ _ =>
    Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => ?_
  rw [← Matrix.trace_mul_comm (gamma σ)]
  simp only [Matrix.mul_assoc]

end Slots

theorem omL_sum (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Z : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    omL P (∑ τ, Z τ) = ∑ τ, omL P (Z τ) := by
  unfold omL
  simp only [Matrix.mul_sum, Matrix.trace_sum]
  exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

theorem omL_smul (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (c : ℂ) (Z : Matrix (Fin 4) (Fin 4) ℂ) :
    omL P (c • Z) = c * omL P Z := by
  unfold omL
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]

theorem sum_gammaLower_mul_gamma : ∑ τ, gammaLower τ * gamma τ = (-4 : ℂ) • 𝟙 := by
  have h := sum_gammaLower_swap 𝟙
  simp only [Matrix.mul_one] at h
  rw [h, contract_one]

section Pairings

variable (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)

/-- **The double contraction `(01)(23)`.** -/
theorem sum_lw_0123 : ∑ σ, ∑ τ, lw P (gammaLower σ) (gamma σ) (gammaLower τ) (gamma τ) =
    lw P ((2 : ℂ) • 𝟙) 𝟙 ((2 : ℂ) • 𝟙) 𝟙 := by
  rw [Finset.sum_comm]
  simp only [sum_lw_01, sum_lw_23]

/-- **The double contraction `(02)(13)`.** -/
theorem sum_lw_0213 : ∑ σ, ∑ τ, lw P (gammaLower σ) (gammaLower τ) (gamma σ) (gamma τ) =
    32 * omL P 𝟙 := by
  rw [Finset.sum_comm]
  have h : ∀ τ, ∑ σ, lw P (gammaLower σ) (gammaLower τ) (gamma σ) (gamma τ) =
      omL P ((-8 : ℂ) • gammaLower τ * gamma τ) := fun τ =>
    sum_lw_02 P _ _ _ fun μ => by
      rw [← slash_loV, sum_contract02_slash, Matrix.mul_smul]
  rw [Finset.sum_congr rfl fun τ _ => h τ]
  calc ∑ τ, omL P ((-8 : ℂ) • gammaLower τ * gamma τ)
      = (-8 : ℂ) * omL P (∑ τ, gammaLower τ * gamma τ) := by
        simp only [Matrix.smul_mul, omL_smul, omL_sum, Finset.mul_sum]
    _ = 32 * omL P 𝟙 := by
        rw [sum_gammaLower_mul_gamma, omL_smul]
        ring

/-- **The double contraction `(03)(12)`.** -/
theorem sum_lw_0312 : ∑ σ, ∑ τ, lw P (gammaLower σ) (gammaLower τ) (gamma τ) (gamma σ) =
    f3 P ((2 : ℂ) • 𝟙) 𝟙 := by
  simp only [sum_lw_12, sum_lw_03]

end Pairings

end QED.TwoLoop.UnitLGraphTrace

end
