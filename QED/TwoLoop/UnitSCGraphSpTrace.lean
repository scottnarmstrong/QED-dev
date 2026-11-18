/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCGraphPauli
import Mathlib.Tactic.Ring

/-!
# The contractions of the self-energy class `S₊`

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the `S + C` link, graph half. The class `S₊`
has the external photon at vertex `1` and the internal photons `(0 4)` (outer) and `(2 3)`
(inner, the self-energy subgraph), the pairing `permSp`. After the Pauli projection its numerator
is a combination of the traces (`spw`)

`spw(P; Y₀, Y₁, Y₂, Y₃) = ∑_{μνρ} tr(γ^ν P_μ γ_ν Y₀ γ^ρ Y₁ γ_ρ Y₂ γ^μ Y₃)`

(`isWeightPattern_Sp`), with `P` the Pauli matrices and `Y₀, …, Y₃` the electron numerators of
the lines `3, 2, 1, 0`, or, after Wick's rule, with one or two of the `Yₖ` replaced by a
contracted pair `γ_σ, γ^σ`. All of these are base patterns `pw` of
`QED/TwoLoop/UnitSCGraphPauli.lean` of a contracted Pauli family (`spw_eq_pw`, `sum_spw_01`, …,
`sum_spw_0312`), so the three coefficients `T₁, T₂, T₃` of the projected numerator are explicit
combinations of base patterns (`classT1_Sp_eq`, `classT2_Sp_eq`, `classT3_Sp_eq`).
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.TwoLoop.UnitSCGraph

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.Bridge QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.ParamNumEval QED.TwoLoop.UnitLGraph QED.TwoLoop.UnitLGraphTrace
open QED.Integration.TwoLoop (symanzikU symanzikMatrix)

/-- The identity matrix. -/
local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-! ### The pattern and the photon weights -/

/-- **The `S₊` contraction** `∑_{μνρ} tr(γ^ν P_μ γ_ν Y₀ γ^ρ Y₁ γ_ρ Y₂ γ^μ Y₃)`. -/
noncomputable def spw (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ) :
    ℂ :=
  ∑ μ, ∑ ν, ∑ ρ, trace (gamma ν * P μ * gammaLower ν * Y₀ * gamma ρ * Y₁ * gammaLower ρ * Y₂ *
    gamma μ * Y₃)

theorem permSp_zero : permSp 0 = 1 := rfl
theorem permSp_one : permSp 1 = 0 := rfl
theorem permSp_two : permSp 2 = 4 := rfl
theorem permSp_three : permSp 3 = 2 := rfl
theorem permSp_four : permSp 4 = 3 := rfl

/-- **The `S₊` chain sum is the `S₊` contraction**: `∑_μ ∑_l c_{μ,l} ch(B_{μ,l}; Y) = η² spw(P; Y)`. -/
theorem isWeightPattern_Sp (P : Params) : IsWeightPattern permSp P spw := by
  intro p' p Y₀ Y₁ Y₂ Y₃
  unfold spw
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [sum_fin5]
  simp only [classWeight, ladderB, ch, permSp_zero, permSp_one, permSp_two, permSp_three,
    permSp_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single μ (fun b _ hb => by simp [kron, hb]) (by simp)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single c (fun d _ hd => by simp [pvEta, Minkowski.metric, Ne.symm hd]) (by simp),
    Finset.sum_eq_single a (fun e _ he => by simp [pvEta, Minkowski.metric, Ne.symm he]) (by simp)]
  simp only [kron, ite_true, one_mul, pvEta, pvConst, gammaLower_eq_metric_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  push_cast
  ring

/-! ### Reduction to the base pattern -/

section Slots

variable (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ)

/-- **`spw` is a base pattern of the contracted family**:
`spw(P; Y) = pw(ΓP; Y₀ Γ(Y₁) Y₂, Y₃)`. -/
theorem spw_eq_pw :
    spw P Y₀ Y₁ Y₂ Y₃ = pw (contractP P) (Y₀ * (∑ ρ, gamma ρ * Y₁ * gammaLower ρ) * Y₂) Y₃ := by
  unfold spw pw contractP
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
  exact Finset.sum_comm

theorem pw_sum_left (Q : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (Z : Matrix (Fin 4) (Fin 4) ℂ) : ∑ σ, pw Q (W σ) Z = pw Q (∑ σ, W σ) Z := by
  unfold pw
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum]

theorem sum_gammaLower_two_gamma :
    ∑ σ, gammaLower σ * ((2 : ℂ) • gamma σ) = (-8 : ℂ) • 𝟙 := by
  simp only [Matrix.mul_smul, ← Finset.smul_sum, sum_gammaLower_mul_gamma, smul_smul]
  norm_num

theorem sum_two_gammaLower_gamma :
    ∑ σ, (2 : ℂ) • gammaLower σ * gamma σ = (-8 : ℂ) • 𝟙 := by
  simp only [Matrix.smul_mul, ← Finset.smul_sum, sum_gammaLower_mul_gamma, smul_smul]
  norm_num

/-- **Slots `0, 1` contracted.** -/
theorem sum_spw_01 : ∑ σ, spw P (gammaLower σ) (gamma σ) Y₂ Y₃ = -8 * pw (contractP P) Y₂ Y₃ := by
  simp only [spw_eq_pw, sum_gamma_gamma_gammaLower, pw_sum_left, ← Finset.sum_mul,
    sum_gammaLower_two_gamma, Matrix.smul_mul, Matrix.one_mul, pw_smul_left]

/-- **Slots `0, 2` contracted.** -/
theorem sum_spw_02 : ∑ σ, spw P (gammaLower σ) Y₁ (gamma σ) Y₃ =
    pw (contractP P) (∑ σ, gamma σ * (∑ ρ, gamma ρ * Y₁ * gammaLower ρ) * gammaLower σ) Y₃ := by
  simp only [spw_eq_pw, pw_sum_left, sum_gammaLower_swap]

/-- **Slots `0, 3` contracted.** -/
theorem sum_spw_03 : ∑ σ, spw P (gammaLower σ) Y₁ Y₂ (gamma σ) =
    pw (contractP (contractP P)) ((∑ ρ, gamma ρ * Y₁ * gammaLower ρ) * Y₂) 𝟙 := by
  simp only [spw_eq_pw]
  set X := ∑ ρ, gamma ρ * Y₁ * gammaLower ρ
  set P' := contractP P
  unfold pw
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [show contractP P' μ = ∑ σ, gamma σ * P' μ * gammaLower σ from rfl, Matrix.mul_one]
  simp only [Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Matrix.trace_mul_comm (gamma σ)]
  simp only [Matrix.mul_assoc]

/-- **Slots `1, 2` contracted.** -/
theorem sum_spw_12 : ∑ σ, spw P Y₀ (gammaLower σ) (gamma σ) Y₃ = -8 * pw (contractP P) Y₀ Y₃ := by
  simp only [spw_eq_pw, sum_gamma_gammaLower_gammaLower, pw_sum_left]
  have h : ∑ σ, Y₀ * ((2 : ℂ) • gammaLower σ) * gamma σ = (-8 : ℂ) • Y₀ := by
    have e : ∀ σ, Y₀ * ((2 : ℂ) • gammaLower σ) * gamma σ =
        (2 : ℂ) • (Y₀ * (gammaLower σ * gamma σ)) := fun σ => by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [Finset.sum_congr rfl fun σ _ => e σ, ← Finset.smul_sum, ← Matrix.mul_sum,
      sum_gammaLower_mul_gamma, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    norm_num
  rw [h, pw_smul_left]

/-- **Slots `1, 3` contracted.** -/
theorem sum_spw_13 : ∑ σ, spw P Y₀ (gammaLower σ) Y₂ (gamma σ) =
    2 * pw (contractP (mulRightP (contractP P) Y₀)) Y₂ 𝟙 := by
  simp only [spw_eq_pw, sum_gamma_gammaLower_gammaLower, Matrix.mul_smul, Matrix.smul_mul,
    pw_smul_left]
  rw [← Finset.mul_sum]
  congr 1
  set P' := contractP P
  unfold pw
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [show contractP (mulRightP P' Y₀) μ = ∑ σ, gamma σ * (P' μ * Y₀) * gammaLower σ from rfl,
    Matrix.mul_one]
  simp only [Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Matrix.trace_mul_comm (gamma σ)]
  simp only [Matrix.mul_assoc]

/-- **Slots `2, 3` contracted.** -/
theorem sum_spw_23 : ∑ σ, spw P Y₀ Y₁ (gammaLower σ) (gamma σ) =
    2 * pw (contractP P) (Y₀ * (∑ ρ, gamma ρ * Y₁ * gammaLower ρ)) 𝟙 := by
  simp only [spw_eq_pw]
  rw [← sum_pw_gammaLower_gamma]
  simp only [Matrix.mul_one]

end Slots

section Pairings

variable (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)

/-- `∑_τ pw(P; γ_τ, γ^τ) = 2 pw(P; 1, 1)`. -/
theorem sum_pw_gammaLower_gamma' (Q : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ τ, pw Q (gammaLower τ) (gamma τ) = 2 * pw Q 𝟙 𝟙 := by
  have h := sum_pw_gammaLower_gamma Q 𝟙 𝟙
  simp only [Matrix.one_mul, Matrix.mul_one] at h
  exact h

/-- **The double contraction `(01)(23)`.** -/
theorem sum_spw_0123 : ∑ σ, ∑ τ, spw P (gammaLower σ) (gamma σ) (gammaLower τ) (gamma τ) =
    -16 * pw (contractP P) 𝟙 𝟙 := by
  rw [Finset.sum_comm]
  simp only [sum_spw_01, ← Finset.mul_sum, sum_pw_gammaLower_gamma']
  ring

/-- **The double contraction `(02)(13)`.** -/
theorem sum_spw_0213 : ∑ σ, ∑ τ, spw P (gammaLower σ) (gammaLower τ) (gamma σ) (gamma τ) =
    8 * pw (contractP P) 𝟙 𝟙 := by
  rw [Finset.sum_comm]
  simp only [sum_spw_02, sum_gamma_gammaLower_gammaLower, Matrix.mul_smul, Matrix.smul_mul,
    ← Finset.smul_sum, smul_smul, pw_smul_left]
  rw [← Finset.mul_sum, sum_pw_gammaLower_gamma']
  ring

/-- **The double contraction `(03)(12)`.** -/
theorem sum_spw_0312 : ∑ σ, ∑ τ, spw P (gammaLower σ) (gammaLower τ) (gamma τ) (gamma σ) =
    -16 * pw (contractP P) 𝟙 𝟙 := by
  simp only [sum_spw_12, ← Finset.mul_sum, sum_pw_gammaLower_gamma']
  ring

end Pairings

/-! ### The three coefficients of `S₊` -/

section Coeff

variable (P : Params) (z : Fin 8 → ℝ) (u : ℝ)

/-- The contraction `Γ(X) = γ^ρ X γ_ρ` of a matrix. -/
noncomputable abbrev gamM (X : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ ρ, gamma ρ * X * gammaLower ρ

/-- **`T₁` of `S₊`**: `T₁ = -π⁴ κ η² U⁻² · 6 pw(ΓP; Ē₀ Γ(Ē₁) Ē₂, Ē₃)`. -/
theorem classT1_Sp_eq : classT1 .Sp permSp P z u =
    ladderK P * ((symanzikU (classAlpha .Sp) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (6 * pw (contractP (ladderPauli P u))
        (classE .Sp P z u 0 * gamM (classE .Sp P z u 1) * classE .Sp P z u 2)
        (classE .Sp P z u 3)) := by
  rw [classT1_eq_of_pat (isWeightPattern_Sp P), spw_eq_pw]

/-- **`T₂` of `S₊`** through base patterns. -/
theorem classT2_Sp_eq : classT2 .Sp permSp P z u =
    ladderK P * ((symanzikU (classAlpha .Sp) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 1 *
          (-8 * pw (contractP (ladderPauli P u)) (classE .Sp P z u 2) (classE .Sp P z u 3)) +
        classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 2 *
          pw (contractP (ladderPauli P u)) (gamM (gamM (classE .Sp P z u 1))) (classE .Sp P z u 3) +
        classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 3 *
          pw (contractP (contractP (ladderPauli P u)))
            (gamM (classE .Sp P z u 1) * classE .Sp P z u 2) 𝟙 +
        classC .Sp (symanzikMatrix (classAlpha .Sp) z) 1 2 *
          (-8 * pw (contractP (ladderPauli P u)) (classE .Sp P z u 0) (classE .Sp P z u 3)) +
        classC .Sp (symanzikMatrix (classAlpha .Sp) z) 1 3 *
          (2 * pw (contractP (mulRightP (contractP (ladderPauli P u)) (classE .Sp P z u 0)))
            (classE .Sp P z u 2) 𝟙) +
        classC .Sp (symanzikMatrix (classAlpha .Sp) z) 2 3 *
          (2 * pw (contractP (ladderPauli P u))
            (classE .Sp P z u 0 * gamM (classE .Sp P z u 1)) 𝟙)) := by
  rw [classT2_eq_of_pat (isWeightPattern_Sp P), sum_spw_01, sum_spw_02, sum_spw_03, sum_spw_12,
    sum_spw_13, sum_spw_23]

/-- **`T₃` of `S₊`** through base patterns. -/
theorem classT3_Sp_eq : classT3 .Sp permSp P z u =
    ladderK P * ((symanzikU (classAlpha .Sp) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (1 / 4 * (classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 1 *
          classC .Sp (symanzikMatrix (classAlpha .Sp) z) 2 3 *
            (-16 * pw (contractP (ladderPauli P u)) 𝟙 𝟙) +
        classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 2 *
          classC .Sp (symanzikMatrix (classAlpha .Sp) z) 1 3 *
            (8 * pw (contractP (ladderPauli P u)) 𝟙 𝟙) +
        classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 3 *
          classC .Sp (symanzikMatrix (classAlpha .Sp) z) 1 2 *
            (-16 * pw (contractP (ladderPauli P u)) 𝟙 𝟙))) := by
  rw [classT3_eq_of_pat (isWeightPattern_Sp P), sum_spw_0123, sum_spw_0213, sum_spw_0312]

end Coeff

end QED.TwoLoop.UnitSCGraph

end
