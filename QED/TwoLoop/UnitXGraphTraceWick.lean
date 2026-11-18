/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXGraphTraceReduce
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# The non-adjacent Wick contractions of the crossed contraction

Section 8 of `docs/TWO-LOOP-UNITS.md`, the graph half of the X unit. The contractions of the
slots `(0, 2)`, `(1, 3)`, `(0, 3)` of the crossed contraction `xw` and the three double
contractions, reduced by the Clifford relations to the nested patterns of
`QED/TwoLoop/UnitXGraphTraceReduce.lean` (valid for arbitrary matrices `P_μ`):

* `sum_xw_02`: for `Y₁ = c - k̸`,
  `∑_τ xw(P; γ_τ, Y₁, γ^τ, Y₃) = -16 c om0(P; Y₃, 1) - 4 omG(P; k̸, Y₃)`;
* `sum_xw_13`: for `Y₀ = c - k̸₀`, `Y₂ = c' - k̸₂`,
  `∑_τ xw(P; Y₀, γ_τ, Y₂, γ^τ) = -16 c' om0(P; 1, Y₀) - 4 c omG(P; k̸₂, 1) + 8 om0(P; k̸₂, k̸₀)`;
* `sum_xw_03`: `∑_τ xw(P; γ_τ, Y₁, Y₂, γ^τ) = 4 hg(P; Y₁, Y₂, 1) + 16 omG(P; Y₁, Y₂) - f3(P; Y₁, Y₂)`;
* `sum_xw_0123`, `sum_xw_0213`, `sum_xw_0312`: the double contractions.
-/

@[expose] public section

open Complex Matrix

namespace QED.TwoLoop.UnitXGraph

open QED.Dirac QED.TwoLoop.UnitLGraphTrace

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-! ### Clifford identities in sandwich form -/

theorem sig_slash_slash (a b : Fin 4 → ℝ) :
    sig (slash a * slash b) = ((4 * Minkowski.dot a b : ℝ) : ℂ) • 𝟙 := by
  have h := contract_slash_slash a b
  simp only [sig, Matrix.mul_assoc] at h ⊢
  exact h

theorem sig_slash_slash_slash (a b c : Fin 4 → ℝ) :
    sig (slash a * slash b * slash c) = (2 : ℂ) • (slash c * slash b * slash a) := by
  have h := contract_slash_slash_slash a b c
  simp only [sig, Matrix.mul_assoc] at h ⊢
  exact h

theorem sig_slash (a : Fin 4 → ℝ) : sig (slash a) = (2 : ℂ) • slash a := contract_slash a

theorem dot_loV (k : Fin 4 → ℝ) (ν : Fin 4) : Minkowski.dot k (loV ν) = Minkowski.lower k ν := by
  fin_cases ν <;> simp [Minkowski.dot_eq, Minkowski.lower_eq, loV]

theorem sum_dot_loV_smul_gamma' (k : Fin 4 → ℝ) :
    ∑ ν, ((Minkowski.dot k (loV ν) : ℝ) : ℂ) • gamma ν = slash k := by
  simp only [dot_loV]
  rfl

theorem sum_dot_loV_upV_smul_gamma (μ : Fin 4) :
    ∑ ν, ((Minkowski.dot (loV ν) (upV μ) : ℝ) : ℂ) • gamma ν = gamma μ := by
  simp only [Minkowski.dot_comm (loV _)]
  exact sum_dot_loV_smul_gamma μ

theorem sum_gammaLower_mul_mul_gamma (X : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ τ, gammaLower τ * X * gamma τ = sig X :=
  sum_gammaLower_swap X

/-- `Σ(γ_ν (c - k̸) γ^μ) = 4c (e_ν·e^μ) - 2 γ^μ k̸ γ_ν`. -/
theorem sig_block (ν μ : Fin 4) (c : ℂ) (k : Fin 4 → ℝ) :
    sig (gammaLower ν * (c • 𝟙 - slash k) * gamma μ) =
      (c * ((4 * Minkowski.dot (loV ν) (upV μ) : ℝ) : ℂ)) • 𝟙 -
        (2 : ℂ) • (gamma μ * slash k * gammaLower ν) := by
  rw [← slash_loV, ← slash_upV]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, sig_sub,
    sig_smul, sig_slash_slash, sig_slash_slash_slash, smul_smul]

/-- `Σ((c - k̸) γ_ν) = 2c γ_ν - 4 (k·e_ν)`. -/
theorem sig_block' (ν : Fin 4) (c : ℂ) (k : Fin 4 → ℝ) :
    sig ((c • 𝟙 - slash k) * gammaLower ν) =
      (2 * c) • gammaLower ν - ((4 * Minkowski.dot k (loV ν) : ℝ) : ℂ) • 𝟙 := by
  rw [← slash_loV, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sig_sub, sig_smul, sig_slash,
    sig_slash_slash, smul_smul, mul_comm c 2]

/-! ### The contraction `(0, 2)` -/

theorem sum_xw_02_sig (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₁ Y₃ : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ τ, xw P (gammaLower τ) Y₁ (gamma τ) Y₃ =
      ∑ μ, ∑ ν, ∑ σ, trace (gamma ν * P μ * gamma σ * sig (gammaLower ν * Y₁ * gamma μ) *
        gammaLower σ * Y₃) := by
  unfold xw
  rw [sum_comm4]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun σ _ => ?_
  calc _ = trace (gamma ν * P μ * gamma σ * (∑ τ, gammaLower τ * gammaLower ν * Y₁ * gamma μ *
        gamma τ) * gammaLower σ * Y₃) := by
        simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
    _ = _ := by rw [sum_gammaLower_swap3]; simp only [sig, Matrix.mul_assoc]

/-- **The contraction of the slots `0, 2`**: for `Y₁ = c - k̸`,
`∑_τ xw(P; γ_τ, Y₁, γ^τ, Y₃) = -16 c om0(P; Y₃, 1) - 4 omG(P; k̸, Y₃)`. -/
theorem sum_xw_02 (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (c : ℂ) (k : Fin 4 → ℝ)
    (Y₃ : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ τ, xw P (gammaLower τ) (c • 𝟙 - slash k) (gamma τ) Y₃ =
      -16 * c * om0 P Y₃ 𝟙 - 4 * omG P (slash k) Y₃ := by
  rw [sum_xw_02_sig]
  unfold om0 omG
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hσ : ∀ ν, ∑ σ, trace (gamma ν * P μ * gamma σ *
      sig (gammaLower ν * (c • 𝟙 - slash k) * gamma μ) * gammaLower σ * Y₃) =
      (c * ((4 * Minkowski.dot (loV ν) (upV μ) : ℝ) : ℂ)) * trace (gamma ν * P μ * sig 𝟙 * Y₃) -
        2 * trace (gamma ν * P μ * sig (gamma μ * slash k * gammaLower ν) * Y₃) := by
    intro ν
    rw [← sum_trace_sig, ← sum_trace_sig, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [sig_block]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sub,
      Matrix.trace_smul, smul_eq_mul, Matrix.mul_one]
  rw [Finset.sum_congr rfl fun ν _ => hσ ν, Finset.sum_sub_distrib]
  simp only [sig_one, sig_slash_slash_slash, ← slash_upV, ← slash_loV]
  have e1 : ∀ ν, c * ((4 * Minkowski.dot (loV ν) (upV μ) : ℝ) : ℂ) *
      trace (slash (upV ν) * P μ * ((-4 : ℂ) • 𝟙) * Y₃) =
      -16 * c * trace ((((Minkowski.dot (loV ν) (upV μ) : ℝ) : ℂ) • slash (upV ν)) * P μ * Y₃) := by
    intro ν
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
    push_cast
    ring
  have e2 : ∀ ν, 2 * trace (slash (upV ν) * P μ * ((2 : ℂ) • (slash (loV ν) * slash k *
      slash (upV μ))) * Y₃) = 4 * trace (slash (upV ν) * P μ * slash (loV ν) *
        (slash k * slash (upV μ) * Y₃)) := by
    intro ν
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
    ring
  simp only [e1, e2, ← Finset.mul_sum]
  rw [← Matrix.trace_sum]
  simp only [← Matrix.sum_mul]
  simp only [slash_upV, slash_loV, sum_dot_loV_upV_smul_gamma]
  have e3 := sum_trace_sig 𝟙 (P μ) (slash k * gamma μ * Y₃)
  simp only [Matrix.one_mul] at e3
  rw [e3]
  congr 2
  · rw [Matrix.mul_one, Matrix.trace_mul_comm (P μ * Y₃), Matrix.mul_assoc]
  · simp only [Matrix.mul_assoc]

/-! ### The contraction `(1, 3)` -/

theorem sig_block_upV (μ σ : Fin 4) (c : ℂ) (k : Fin 4 → ℝ) :
    sig (gamma μ * (c • 𝟙 - slash k) * gammaLower σ) =
      (c * ((4 * Minkowski.dot (upV μ) (loV σ) : ℝ) : ℂ)) • 𝟙 -
        (2 : ℂ) • (gammaLower σ * slash k * gamma μ) := by
  rw [← slash_loV, ← slash_upV]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, sig_sub,
    sig_smul, sig_slash_slash, sig_slash_slash_slash, smul_smul]

theorem sum_xw_13_sig (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₂ : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ τ, xw P Y₀ (gammaLower τ) Y₂ (gamma τ) =
      ∑ μ, ∑ ν, ∑ σ, trace (gamma ν * P μ * gamma σ * Y₀ * gammaLower ν *
        sig (gamma μ * Y₂ * gammaLower σ)) := by
  unfold xw
  rw [sum_comm4]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun σ _ => ?_
  calc _ = trace (gamma ν * P μ * gamma σ * Y₀ * gammaLower ν *
        (∑ τ, gammaLower τ * gamma μ * Y₂ * gammaLower σ * gamma τ)) := by
        simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
    _ = _ := by rw [sum_gammaLower_swap3]; simp only [sig, Matrix.mul_assoc]

/-- `∑_ν tr(γ^ν M γ_ν) = -4 tr M`. -/
theorem sum_trace_gamma_mul_gammaLower (M : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ ν, trace (gamma ν * M * gammaLower ν) = -4 * trace M := by
  rw [← trace_sig, sig, Matrix.trace_sum]

/-- **The contraction of the slots `1, 3`**: for `Y₀ = c - k̸₀`, `Y₂ = c' - k̸₂`,
`∑_τ xw(P; Y₀, γ_τ, Y₂, γ^τ) = -16 c' om0(P; 1, Y₀) - 4 c omG(P; k̸₂, 1) + 8 om0(P; k̸₂, k̸₀)`. -/
theorem sum_xw_13 (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (c c' : ℂ) (k₀ k₂ : Fin 4 → ℝ) :
    ∑ τ, xw P (c • 𝟙 - slash k₀) (gammaLower τ) (c' • 𝟙 - slash k₂) (gamma τ) =
      -16 * c' * om0 P 𝟙 (c • 𝟙 - slash k₀) - 4 * c * omG P (slash k₂) 𝟙 +
        8 * om0 P (slash k₂) (slash k₀) := by
  rw [sum_xw_13_sig]
  unfold om0 omG
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  set Y₀ := c • 𝟙 - slash k₀ with hY₀
  -- the sum over `σ`
  have hσ : ∀ ν, ∑ σ, trace (gamma ν * P μ * gamma σ * Y₀ * gammaLower ν *
      sig (gamma μ * (c' • 𝟙 - slash k₂) * gammaLower σ)) =
      4 * c' * trace (gamma ν * (P μ * gamma μ * Y₀) * gammaLower ν) -
        2 * trace (gamma ν * P μ * sig (Y₀ * gammaLower ν) * (slash k₂ * gamma μ)) := by
    intro ν
    rw [← sum_trace_sig]
    have e : ∀ σ, trace (gamma ν * P μ * gamma σ * Y₀ * gammaLower ν *
        sig (gamma μ * (c' • 𝟙 - slash k₂) * gammaLower σ)) =
        4 * c' * trace (gamma ν * P μ * ((((Minkowski.dot (upV μ) (loV σ) : ℝ) : ℂ)) • gamma σ) *
          Y₀ * gammaLower ν) -
        2 * trace (gamma ν * P μ * gamma σ * (Y₀ * gammaLower ν) * gammaLower σ *
          (slash k₂ * gamma μ)) := by
      intro σ
      rw [sig_block_upV]
      simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sub,
        Matrix.trace_smul, smul_eq_mul, Matrix.mul_one, Matrix.mul_assoc]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun σ _ => e σ, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    congr 2
    rw [← Matrix.trace_sum]
    simp only [← Matrix.sum_mul, ← Matrix.mul_sum, sum_dot_loV_smul_gamma, Matrix.mul_assoc]
  rw [Finset.sum_congr rfl fun ν _ => hσ ν, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_trace_gamma_mul_gammaLower]
  -- the sum over `ν` in the second term
  have hν : ∀ ν, trace (gamma ν * P μ * sig (Y₀ * gammaLower ν) * (slash k₂ * gamma μ)) =
      2 * c * trace (gamma ν * P μ * gammaLower ν * (slash k₂ * gamma μ)) -
        4 * trace ((((Minkowski.dot k₀ (loV ν) : ℝ) : ℂ) • gamma ν) * P μ * (slash k₂ * gamma μ)) := by
    intro ν
    rw [hY₀, sig_block']
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sub,
      Matrix.trace_smul, smul_eq_mul, Matrix.mul_one]
    push_cast
    ring
  have e3 := sum_trace_sig 𝟙 (P μ) (slash k₂ * gamma μ)
  simp only [Matrix.one_mul] at e3
  rw [Finset.sum_congr rfl fun ν _ => hν ν, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, e3, ← Matrix.trace_sum]
  simp only [← Matrix.sum_mul, sum_dot_loV_smul_gamma', Matrix.mul_one]
  have e1 : trace (slash k₀ * P μ * (slash k₂ * gamma μ)) =
      trace (P μ * slash k₂ * gamma μ * slash k₀) := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm (slash k₀)]
    simp only [Matrix.mul_assoc]
  rw [e1]
  simp only [Matrix.mul_assoc]
  ring

/-! ### The contraction `(0, 3)` -/

theorem sum_xw_03_sig (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₁ Y₂ : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ τ, xw P (gammaLower τ) Y₁ Y₂ (gamma τ) =
      ∑ μ, ∑ ν, ∑ σ, trace (sig (gamma ν * P μ * gamma σ) * gammaLower ν * Y₁ * gamma μ * Y₂ *
        gammaLower σ) := by
  unfold xw
  rw [sum_comm4]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun σ _ => ?_
  have e : ∀ τ, trace (gamma ν * P μ * gamma σ * gammaLower τ * gammaLower ν * Y₁ * gamma μ * Y₂ *
      gammaLower σ * gamma τ) = trace (𝟙 * gamma τ * (gamma ν * P μ * gamma σ) * gammaLower τ *
        (gammaLower ν * Y₁ * gamma μ * Y₂ * gammaLower σ)) := by
    intro τ
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.one_mul, Matrix.mul_assoc]
  rw [Finset.sum_congr rfl fun τ _ => e τ, sum_trace_sig, Matrix.one_mul]
  simp only [Matrix.mul_assoc]

/-- `Σ(γ^ν X γ^σ) = γ^ν Σ(X) γ^σ + 2 X γ^ν γ^σ - 2 γ^σ γ^ν X`. -/
theorem sig_gamma_mul_gamma (X : Matrix (Fin 4) (Fin 4) ℂ) (ν σ : Fin 4) :
    sig (gamma ν * X * gamma σ) =
      gamma ν * sig X * gamma σ + (2 : ℂ) • (X * gamma ν * gamma σ) -
        (2 : ℂ) • (gamma σ * gamma ν * X) := by
  have h1 := sig_mul_slash (gamma ν * X) (upV σ)
  have h2 := sig_slash_mul X (upV ν)
  rw [slash_upV] at h1 h2
  rw [h1, h2]
  simp only [Matrix.neg_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc]
  module

/-- **The contraction of the slots `0, 3`**:
`∑_τ xw(P; γ_τ, Y₁, Y₂, γ^τ) = 4 hg(P; Y₁, Y₂, 1) + 16 omG(P; Y₁, Y₂) - f3(P; Y₁, Y₂)`. -/
theorem sum_xw_03 (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₁ Y₂ : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ τ, xw P (gammaLower τ) Y₁ Y₂ (gamma τ) =
      4 * hg P Y₁ Y₂ 𝟙 + 16 * omG P Y₁ Y₂ - f3 P Y₁ Y₂ := by
  rw [sum_xw_03_sig, f3_eq_sig]
  unfold hg omG
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  set S := sig (P μ)
  set W := Y₁ * gamma μ * Y₂
  have hW : ∀ ν σ, trace (sig (gamma ν * P μ * gamma σ) * gammaLower ν * Y₁ * gamma μ * Y₂ *
      gammaLower σ) =
      trace (𝟙 * gamma ν * (S * gamma σ) * gammaLower ν * (W * gammaLower σ)) +
        2 * trace (P μ * gamma ν * gamma σ * gammaLower ν * (W * gammaLower σ)) -
        2 * trace (gamma σ * gamma ν * P μ * gammaLower ν * (W * gammaLower σ)) := by
    intro ν σ
    rw [sig_gamma_mul_gamma]
    simp only [S, W, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_add,
      Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, Matrix.one_mul, Matrix.mul_assoc]
  simp only [hW]
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  -- the sums over `ν`
  have hν₁ : ∀ σ, ∑ ν, trace (𝟙 * gamma ν * (S * gamma σ) * gammaLower ν * (W * gammaLower σ)) =
      -trace (𝟙 * gamma σ * W * gammaLower σ * sig S) -
        2 * trace (𝟙 * gamma σ * (S * W) * gammaLower σ * 𝟙) := by
    intro σ
    rw [sum_trace_sig, ← slash_upV, sig_mul_slash]
    simp only [Matrix.sub_mul, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_sub, Matrix.trace_sub,
      Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc]
    congr 1
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hν₂ : ∀ σ, ∑ ν, trace (P μ * gamma ν * gamma σ * gammaLower ν * (W * gammaLower σ)) =
      2 * trace (P μ * gamma σ * W * gammaLower σ * 𝟙) := by
    intro σ
    rw [sum_trace_sig, sig_gamma]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_one,
      Matrix.mul_assoc]
  have hν₃ : ∀ σ, ∑ ν, trace (gamma σ * gamma ν * P μ * gammaLower ν * (W * gammaLower σ)) =
      trace (𝟙 * gamma σ * (S * W) * gammaLower σ * 𝟙) := by
    intro σ
    rw [sum_trace_sig]
    simp only [S, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  simp only [hν₁, hν₂, hν₃, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  rw [sum_trace_sig, sum_trace_sig, sum_trace_sig]
  simp only [Matrix.one_mul, Matrix.mul_one]
  rw [trace_sig, Matrix.trace_mul_comm (sig W) (sig S)]
  simp only [W, Matrix.mul_assoc]
  ring

/-! ### The double contractions -/

theorem slash_neg_loV (ρ : Fin 4) : (0 : ℂ) • 𝟙 - slash (-loV ρ) = gammaLower ρ := by
  rw [QED.Dirac.slash_neg, slash_loV, zero_smul, zero_sub, neg_neg]

/-- **The double contraction `(01)(23)`.** -/
theorem sum_xw_0123 (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ ν, ∑ ρ, xw P (gammaLower ν) (gamma ν) (gammaLower ρ) (gamma ρ) =
      xw P ((2 : ℂ) • 𝟙) 𝟙 ((2 : ℂ) • 𝟙) 𝟙 := by
  rw [Finset.sum_comm]
  simp only [sum_xw_01, sum_xw_23]

/-- **The double contraction `(02)(13)`.** -/
theorem sum_xw_0213 (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ ν, ∑ ρ, xw P (gammaLower ν) (gammaLower ρ) (gamma ν) (gamma ρ) = 8 * omG P 𝟙 𝟙 := by
  rw [Finset.sum_comm]
  have h : ∀ ρ, ∑ ν, xw P (gammaLower ν) (gammaLower ρ) (gamma ν) (gamma ρ) =
      4 * omG P (gammaLower ρ) (gamma ρ) := by
    intro ρ
    have h0 := sum_xw_02 P 0 (-loV ρ) (gamma ρ)
    rw [slash_neg_loV, QED.Dirac.slash_neg, slash_loV] at h0
    rw [h0]
    unfold omG
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.trace_neg, Finset.sum_neg_distrib]
    ring
  simp only [h, ← Finset.mul_sum]
  unfold omG
  rw [Finset.sum_comm]
  have e : ∀ μ, ∑ ρ, trace (sig (P μ) * gammaLower ρ * gamma μ * gamma ρ) =
      2 * trace (sig (P μ) * 𝟙 * gamma μ * 𝟙) := by
    intro μ
    rw [← Matrix.trace_sum]
    simp only [Matrix.mul_assoc, ← Matrix.mul_sum, Matrix.mul_one]
    simp only [← Matrix.mul_assoc, sum_gammaLower_gamma_gamma, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul]
  simp only [e, ← Finset.mul_sum]
  ring

/-- **The double contraction `(03)(12)`.** -/
theorem sum_xw_0312 (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ ν, ∑ ρ, xw P (gammaLower ν) (gammaLower ρ) (gamma ρ) (gamma ν) =
      4 * hg P ((2 : ℂ) • 𝟙) 𝟙 𝟙 + 16 * omG P ((2 : ℂ) • 𝟙) 𝟙 - f3 P ((2 : ℂ) • 𝟙) 𝟙 := by
  simp only [sum_xw_12, sum_xw_03]

end QED.TwoLoop.UnitXGraph

end
