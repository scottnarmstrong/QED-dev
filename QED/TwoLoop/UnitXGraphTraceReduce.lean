/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXGraphTraceSum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# The crossed contractions reduced to nested ones

Section 8 of `docs/TWO-LOOP-UNITS.md`, the graph half of the X unit. The crossed contraction
`xw(P; Y) = ∑_{μνσ} tr(γ^ν P_μ γ^σ Y₀ γ_ν Y₁ γ^μ Y₂ γ_σ Y₃)` of
`QED/TwoLoop/UnitXGraphTraceSum.lean` interleaves the two photon contractions. Here it and its
Wick contractions are reduced, by the Clifford relations alone, to contractions in which each
sandwich `Σ(M) = ∑_ν γ^ν M γ_ν` (`sig`) encloses a block whose only open index is the external
`μ`: the ladder patterns `lw`, `f3` of `QED/TwoLoop/UnitLGraphTraceContract.lean` and

* `bs P A B Z = ∑_μ tr(Σ(P_μ A γ^μ B) Z)`, `hg P Y₁ Y₂ Z = ∑_μ tr(P_μ Σ(Y₁ γ^μ Y₂) Z)`,
* `omG P A B = ∑_μ tr(Σ(P_μ) A γ^μ B)`, `om0 P A B = ∑_μ tr(P_μ A γ^μ B)`.

The reductions hold for arbitrary matrices `P_μ`:

* `xw_elec`: for `Y₀ = c - k̸`, with `Ȳ₀ = c + k̸`,
  `xw(P; Y) = -lw(P; 1, Ȳ₀ Y₁, Y₂, Y₃) - 2 bs(P; Ȳ₀ Y₁, Y₂, Y₃) + 2 hg(P; Y₁, Y₂, Y₃ k̸)`,
  from the contraction recursion `Σ(X a̸) = -Σ(X) a̸ - 2 a̸ X` applied to `a̸ = γ^σ` and `a̸ = k̸`;
* `sum_xw_01`, `sum_xw_12`, `sum_xw_23`: the contractions of adjacent slots insert `2, 1`;
* `sum_xw_02`, `sum_xw_13`: for electron-type slots `c - k̸`, by `γ^τ a̸ b̸ γ_τ = 4 a·b` and
  `γ^τ a̸ b̸ c̸ γ_τ = 2 c̸ b̸ a̸`;
* `sum_xw_03`: `∑_τ xw(P; γ_τ, Y₁, Y₂, γ^τ) = 4 hg(P; Y₁, Y₂, 1) + 16 omG(P; Y₁, Y₂) - f3(P; Y₁, Y₂)`.
-/

@[expose] public section

open Complex Matrix

namespace QED.TwoLoop.UnitXGraph

open QED.Dirac QED.TwoLoop.UnitLGraphTrace

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-! ### The sandwich and the patterns -/

/-- The sandwich `Σ(M) = ∑_ν γ^ν M γ_ν`. -/
noncomputable def sig (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ ν, gamma ν * M * gammaLower ν

section Patterns

variable (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (A B Z : Matrix (Fin 4) (Fin 4) ℂ)

/-- The pattern `∑_μ tr(Σ(P_μ A γ^μ B) Z)`. -/
noncomputable def bs : ℂ := ∑ μ, trace (sig (P μ * A * gamma μ * B) * Z)

/-- The pattern `∑_μ tr(P_μ Σ(Y₁ γ^μ Y₂) Z)`. -/
noncomputable def hg (Y₁ Y₂ Z : Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  ∑ μ, trace (P μ * sig (Y₁ * gamma μ * Y₂) * Z)

/-- The pattern `∑_μ tr(Σ(P_μ) A γ^μ B)`. -/
noncomputable def omG : ℂ := ∑ μ, trace (sig (P μ) * A * gamma μ * B)

/-- The pattern `∑_μ tr(P_μ A γ^μ B)`. -/
noncomputable def om0 : ℂ := ∑ μ, trace (P μ * A * gamma μ * B)

end Patterns

/-! ### Calculus of the sandwich -/

theorem sig_add (M N : Matrix (Fin 4) (Fin 4) ℂ) : sig (M + N) = sig M + sig N := by
  simp only [sig, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

theorem sig_sub (M N : Matrix (Fin 4) (Fin 4) ℂ) : sig (M - N) = sig M - sig N := by
  simp only [sig, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

theorem sig_neg (M : Matrix (Fin 4) (Fin 4) ℂ) : sig (-M) = -sig M := by
  simp only [sig, Matrix.mul_neg, Matrix.neg_mul, Finset.sum_neg_distrib]

theorem sig_smul (c : ℂ) (M : Matrix (Fin 4) (Fin 4) ℂ) : sig (c • M) = c • sig M := by
  simp only [sig, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

theorem sig_one : sig 𝟙 = (-4 : ℂ) • 𝟙 := by
  simp only [sig, Matrix.mul_one, contract_one]

/-- The contraction recursion `Σ(X a̸) = -Σ(X) a̸ - 2 a̸ X`. -/
theorem sig_mul_slash (X : Matrix (Fin 4) (Fin 4) ℂ) (a : Fin 4 → ℝ) :
    sig (X * slash a) = -(sig X * slash a) - (2 : ℂ) • (slash a * X) := by
  have h := contract_mul_slash X a
  simp only [sig, Matrix.mul_assoc] at h ⊢
  exact h

/-- The mirror recursion `Σ(a̸ X) = -a̸ Σ(X) - 2 X a̸`. -/
theorem sig_slash_mul (X : Matrix (Fin 4) (Fin 4) ℂ) (a : Fin 4 → ℝ) :
    sig (slash a * X) = -(slash a * sig X) - (2 : ℂ) • (X * slash a) := by
  have h : ∀ μ, gamma μ * (slash a * X) * gammaLower μ =
      -(slash a * (gamma μ * X * gammaLower μ))
        - (2 : ℂ) • (X * (((a μ : ℝ) : ℂ) • gammaLower μ)) := by
    intro μ
    have e : gamma μ * slash a = ((-2 * a μ : ℝ) : ℂ) • 𝟙 - slash a * gamma μ := by
      rw [← gamma_slash_anticomm]; abel
    calc gamma μ * (slash a * X) * gammaLower μ = (gamma μ * slash a) * X * gammaLower μ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [e, Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
          simp only [Matrix.mul_assoc, Matrix.mul_smul]
          push_cast
          module
  have hs : ∑ μ, ((a μ : ℝ) : ℂ) • gammaLower μ = slash a := by
    simp [slash, Fin.sum_univ_four, gammaLower_eq, Minkowski.lower_eq]
  rw [sig, Finset.sum_congr rfl fun μ _ => h μ, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.smul_sum, ← Matrix.mul_sum, ← Matrix.mul_sum, hs]
  rfl

/-- The trace of a sandwich: `tr Σ(M) = -4 tr M`. -/
theorem trace_sig (M : Matrix (Fin 4) (Fin 4) ℂ) : trace (sig M) = -4 * trace M := by
  have h : trace (sig M) = trace ((∑ ν, gammaLower ν * gamma ν) * M) := by
    simp only [sig, Matrix.trace_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  rw [h, sum_gammaLower_mul_gamma, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
    smul_eq_mul]

/-- Pulling a contracted pair into a sandwich. -/
theorem sum_trace_sig (A M Z : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ σ, trace (A * gamma σ * M * gammaLower σ * Z) = trace (A * sig M * Z) := by
  simp only [sig, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, Matrix.mul_assoc]

/-- `Σ(γ^σ) = 2 γ^σ`. -/
theorem sig_gamma (σ : Fin 4) : sig (gamma σ) = (2 : ℂ) • gamma σ := by
  rw [← slash_upV]; exact contract_slash _

/-- `Σ(X γ^σ (c - k̸)) = -Σ(X) γ^σ (c + k̸) - 2 γ^σ X (c + k̸) + 2 k̸ X γ^σ`. -/
theorem sig_gamma_mul_elec (X : Matrix (Fin 4) (Fin 4) ℂ) (σ : Fin 4) (c : ℂ) (k : Fin 4 → ℝ) :
    sig (X * gamma σ * (c • 𝟙 - slash k)) =
      -(sig X * gamma σ * (c • 𝟙 + slash k)) - (2 : ℂ) • (gamma σ * X * (c • 𝟙 + slash k)) +
        (2 : ℂ) • (slash k * X * gamma σ) := by
  have h1 : sig (X * gamma σ) = -(sig X * gamma σ) - (2 : ℂ) • (gamma σ * X) := by
    have := sig_mul_slash X (upV σ)
    rwa [slash_upV] at this
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, sig_sub, sig_smul, sig_mul_slash, h1]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_mul, Matrix.neg_mul,
    Matrix.smul_mul, Matrix.mul_assoc]
  module

/-! ### The patterns through the sandwich -/

theorem xw_eq_sig (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ) :
    xw P Y₀ Y₁ Y₂ Y₃ = ∑ μ, ∑ σ, trace (sig (P μ * gamma σ * Y₀) * Y₁ * gamma μ * Y₂ *
      gammaLower σ * Y₃) := by
  unfold xw sig
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.sum_mul, Matrix.trace_sum, Matrix.mul_assoc]

theorem lw_eq_sig (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ) :
    lw P Y₀ Y₁ Y₂ Y₃ = ∑ μ, trace (sig (P μ) * Y₀ * sig (Y₁ * gamma μ * Y₂) * Y₃) := by
  unfold lw
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [lw_term]
  rfl

theorem f3_eq_sig (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₁ Y₂ : Matrix (Fin 4) (Fin 4) ℂ) :
    f3 P Y₁ Y₂ = ∑ μ, trace (sig (sig (P μ)) * sig (Y₁ * gamma μ * Y₂)) := by
  unfold f3
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [f3_term]
  rfl

/-! ### The crossed contraction with an electron-type first slot -/

/-- **The crossed contraction reduced**: for `Y₀ = c - k̸` and `Ȳ₀ = c + k̸`,
`xw(P; Y) = -lw(P; 1, Ȳ₀ Y₁, Y₂, Y₃) - 2 bs(P; Ȳ₀ Y₁, Y₂, Y₃) + 2 hg(P; Y₁, Y₂, Y₃ k̸)`. -/
theorem xw_elec (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (c : ℂ) (k : Fin 4 → ℝ)
    (Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ) :
    xw P (c • 𝟙 - slash k) Y₁ Y₂ Y₃ =
      -lw P 𝟙 ((c • 𝟙 + slash k) * Y₁) Y₂ Y₃ - 2 * bs P ((c • 𝟙 + slash k) * Y₁) Y₂ Y₃ +
        2 * hg P Y₁ Y₂ (Y₃ * slash k) := by
  rw [xw_eq_sig, lw_eq_sig]
  unfold bs hg
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hσ : ∀ σ, trace (sig (P μ * gamma σ * (c • 𝟙 - slash k)) * Y₁ * gamma μ * Y₂ *
      gammaLower σ * Y₃) =
      -trace (sig (P μ) * gamma σ * ((c • 𝟙 + slash k) * Y₁ * gamma μ * Y₂) * gammaLower σ * Y₃) -
        2 * trace (𝟙 * gamma σ * (P μ * ((c • 𝟙 + slash k) * Y₁) * gamma μ * Y₂) * gammaLower σ *
          Y₃) +
        2 * trace ((slash k * P μ) * gamma σ * (Y₁ * gamma μ * Y₂) * gammaLower σ * Y₃) := by
    intro σ
    rw [sig_gamma_mul_elec]
    simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.neg_mul, Matrix.smul_mul, Matrix.trace_sub,
      Matrix.trace_add, Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc,
      Matrix.one_mul]
  rw [Finset.sum_congr rfl fun σ _ => hσ σ, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_trace_sig, sum_trace_sig,
    sum_trace_sig, Matrix.one_mul, Matrix.mul_one]
  congr 2
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (slash k)]
  simp only [Matrix.mul_assoc]

/-! ### The single contractions -/

section Single

variable (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ)

/-- **Slots `0, 1` contracted**: `2, 1` inserted. -/
theorem sum_xw_01 : ∑ τ, xw P (gammaLower τ) (gamma τ) Y₂ Y₃ = xw P ((2 : ℂ) • 𝟙) 𝟙 Y₂ Y₃ := by
  unfold xw
  rw [sum_comm4]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun σ _ => ?_
  calc _ = trace (gamma ν * P μ * gamma σ * (∑ τ, gammaLower τ * gammaLower ν * gamma τ) *
        gamma μ * Y₂ * gammaLower σ * Y₃) := by
        simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
    _ = _ := by
        rw [sum_gammaLower_gammaLower_gamma]
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc]

/-- **Slots `1, 2` contracted**: `2, 1` inserted. -/
theorem sum_xw_12 : ∑ τ, xw P Y₀ (gammaLower τ) (gamma τ) Y₃ = xw P Y₀ ((2 : ℂ) • 𝟙) 𝟙 Y₃ := by
  unfold xw
  rw [sum_comm4]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun σ _ => ?_
  calc _ = trace (gamma ν * P μ * gamma σ * Y₀ * gammaLower ν *
        (∑ τ, gammaLower τ * gamma μ * gamma τ) * gammaLower σ * Y₃) := by
        simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
    _ = _ := by
        rw [sum_gammaLower_gamma_gamma]
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc]

/-- **Slots `2, 3` contracted**: `2, 1` inserted. -/
theorem sum_xw_23 : ∑ τ, xw P Y₀ Y₁ (gammaLower τ) (gamma τ) = xw P Y₀ Y₁ ((2 : ℂ) • 𝟙) 𝟙 := by
  unfold xw
  rw [sum_comm4]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun σ _ => ?_
  calc _ = trace (gamma ν * P μ * gamma σ * Y₀ * gammaLower ν * Y₁ * gamma μ *
        (∑ τ, gammaLower τ * gammaLower σ * gamma τ)) := by
        simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
    _ = _ := by
        rw [sum_gammaLower_gammaLower_gamma]
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc]

end Single

end QED.TwoLoop.UnitXGraph

end
