/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCGraphSpTrace
import Mathlib.Tactic.Ring

/-!
# The contractions of the self-energy class `S₋`

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the `S + C` link, graph half, the analogue of
`QED/TwoLoop/UnitSCGraphSpTrace.lean` for `S₋`. The class `S₋` has the external photon at
vertex `3` and the internal photons `(0 4)` (outer) and `(1 2)` (inner, the self-energy
subgraph), the pairing `permSm`. After the Pauli projection its numerator is a combination of
the traces (`smw`)

`smw(P; Y₀, Y₁, Y₂, Y₃) = ∑_{μνρ} tr(γ^ν P_μ γ_ν Y₀ γ^μ Y₁ γ^ρ Y₂ γ_ρ Y₃)`

(`isWeightPattern_Sm`), with `P` the Pauli matrices and `Y₀, …, Y₃` the electron numerators of
the lines `3, 2, 1, 0`, or, after Wick's rule, with one or two of the `Yₖ` replaced by a
contracted pair `γ_σ, γ^σ`. All of these are base patterns `pw` of a contracted Pauli family
(`smw_eq_pw`, `sum_smw_01`, …, `sum_smw_0312`), so the three coefficients `T₁, T₂, T₃` of the
projected numerator are explicit combinations of base patterns (`classT1_Sm_eq`,
`classT2_Sm_eq`, `classT3_Sm_eq`).
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

/-- **The `S₋` contraction** `∑_{μνρ} tr(γ^ν P_μ γ_ν Y₀ γ^μ Y₁ γ^ρ Y₂ γ_ρ Y₃)`. -/
noncomputable def smw (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ) :
    ℂ :=
  ∑ μ, ∑ ν, ∑ ρ, trace (gamma ν * P μ * gammaLower ν * Y₀ * gamma μ * Y₁ * gamma ρ * Y₂ *
    gammaLower ρ * Y₃)

theorem permSm_zero : permSm 0 = 3 := rfl
theorem permSm_one : permSm 1 = 0 := rfl
theorem permSm_two : permSm 2 = 4 := rfl
theorem permSm_three : permSm 3 = 1 := rfl
theorem permSm_four : permSm 4 = 2 := rfl

/-- **The `S₋` chain sum is the `S₋` contraction**: `∑_μ ∑_l c_{μ,l} ch(B_{μ,l}; Y) = η² smw(P; Y)`. -/
theorem isWeightPattern_Sm (P : Params) : IsWeightPattern permSm P smw := by
  intro p' p Y₀ Y₁ Y₂ Y₃
  unfold smw
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [sum_fin5]
  simp only [classWeight, ladderB, ch, permSm_zero, permSm_one, permSm_two, permSm_three,
    permSm_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single b (fun c _ hc => by simp [pvEta, Minkowski.metric, Ne.symm hc]) (by simp),
    Finset.sum_eq_single μ (fun d _ hd => by simp [kron, hd]) (by simp),
    Finset.sum_eq_single a (fun e _ he => by simp [pvEta, Minkowski.metric, Ne.symm he]) (by simp)]
  simp only [kron, ite_true, one_mul, pvEta, pvConst, gammaLower_eq_metric_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  push_cast
  ring

/-! ### Reduction to the base pattern -/

section Slots

variable (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ)

/-- **`smw` is a base pattern of the contracted family**:
`smw(P; Y) = pw(ΓP; Y₀, Y₁ Γ(Y₂) Y₃)`. -/
theorem smw_eq_pw :
    smw P Y₀ Y₁ Y₂ Y₃ = pw (contractP P) Y₀ (Y₁ * (∑ ρ, gamma ρ * Y₂ * gammaLower ρ) * Y₃) := by
  unfold smw pw contractP
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
  exact Finset.sum_comm

theorem pw_sum_right (Q : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (W : Matrix (Fin 4) (Fin 4) ℂ)
    (Z : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : ∑ σ, pw Q W (Z σ) = pw Q W (∑ σ, Z σ) := by
  unfold pw
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [Matrix.mul_sum, Matrix.trace_sum]

/-- **Slots `0, 1` contracted.** -/
theorem sum_smw_01 : ∑ σ, smw P (gammaLower σ) (gamma σ) Y₂ Y₃ =
    2 * pw (contractP P) 𝟙 ((∑ ρ, gamma ρ * Y₂ * gammaLower ρ) * Y₃) := by
  have h := sum_pw_gammaLower_gamma (contractP P) 𝟙 ((∑ ρ, gamma ρ * Y₂ * gammaLower ρ) * Y₃)
  simp only [Matrix.one_mul] at h
  rw [← h]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [smw_eq_pw, Matrix.mul_assoc]

/-- **Slots `0, 2` contracted.** -/
theorem sum_smw_02 : ∑ σ, smw P (gammaLower σ) Y₁ (gamma σ) Y₃ =
    2 * pw (contractP (mulLeftP Y₃ (contractP P))) 𝟙 Y₁ := by
  simp only [smw_eq_pw, sum_gamma_gamma_gammaLower, Matrix.mul_smul, Matrix.smul_mul,
    pw_smul_right]
  rw [← Finset.mul_sum]
  congr 1
  set P' := contractP P
  unfold pw
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [show contractP (mulLeftP Y₃ P') μ = ∑ σ, gamma σ * (Y₃ * P' μ) * gammaLower σ from rfl,
    Matrix.mul_one]
  simp only [Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  calc trace (P' μ * gammaLower σ * gamma μ * (Y₁ * gamma σ * Y₃))
      = trace ((P' μ * gammaLower σ * gamma μ * Y₁ * gamma σ) * Y₃) := by
        simp only [Matrix.mul_assoc]
    _ = trace (Y₃ * (P' μ * gammaLower σ * gamma μ * Y₁ * gamma σ)) := Matrix.trace_mul_comm _ _
    _ = trace ((Y₃ * P' μ * gammaLower σ * gamma μ * Y₁) * gamma σ) := by
        simp only [Matrix.mul_assoc]
    _ = trace (gamma σ * (Y₃ * P' μ * gammaLower σ * gamma μ * Y₁)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

/-- **Slots `0, 3` contracted.** -/
theorem sum_smw_03 : ∑ σ, smw P (gammaLower σ) Y₁ Y₂ (gamma σ) =
    pw (contractP (contractP P)) 𝟙 (Y₁ * (∑ ρ, gamma ρ * Y₂ * gammaLower ρ)) := by
  simp only [smw_eq_pw]
  set X := ∑ ρ, gamma ρ * Y₂ * gammaLower ρ
  set P' := contractP P
  unfold pw
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [show contractP P' μ = ∑ σ, gamma σ * P' μ * gammaLower σ from rfl, Matrix.mul_one]
  simp only [Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  calc trace (P' μ * gammaLower σ * gamma μ * (Y₁ * X * gamma σ))
      = trace ((P' μ * gammaLower σ * gamma μ * (Y₁ * X)) * gamma σ) := by
        simp only [Matrix.mul_assoc]
    _ = trace (gamma σ * (P' μ * gammaLower σ * gamma μ * (Y₁ * X))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

/-- **Slots `1, 2` contracted.** -/
theorem sum_smw_12 : ∑ σ, smw P Y₀ (gammaLower σ) (gamma σ) Y₃ = -8 * pw (contractP P) Y₀ Y₃ := by
  simp only [smw_eq_pw, sum_gamma_gamma_gammaLower, pw_sum_right]
  have h : ∑ σ, gammaLower σ * ((2 : ℂ) • gamma σ) * Y₃ = (-8 : ℂ) • Y₃ := by
    rw [← Finset.sum_mul, sum_gammaLower_two_gamma, Matrix.smul_mul, Matrix.one_mul]
  rw [h, pw_smul_right]

/-- **Slots `1, 3` contracted.** -/
theorem sum_smw_13 : ∑ σ, smw P Y₀ (gammaLower σ) Y₂ (gamma σ) =
    pw (contractP P) Y₀ (∑ σ, gamma σ * (∑ ρ, gamma ρ * Y₂ * gammaLower ρ) * gammaLower σ) := by
  simp only [smw_eq_pw, pw_sum_right, sum_gammaLower_swap]

/-- **Slots `2, 3` contracted.** -/
theorem sum_smw_23 : ∑ σ, smw P Y₀ Y₁ (gammaLower σ) (gamma σ) = -8 * pw (contractP P) Y₀ Y₁ := by
  simp only [smw_eq_pw, sum_gamma_gammaLower_gammaLower, pw_sum_right]
  have h : ∑ σ, Y₁ * ((2 : ℂ) • gammaLower σ) * gamma σ = (-8 : ℂ) • Y₁ := by
    have e : ∀ σ, Y₁ * ((2 : ℂ) • gammaLower σ) * gamma σ =
        (2 : ℂ) • (Y₁ * (gammaLower σ * gamma σ)) := fun σ => by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [Finset.sum_congr rfl fun σ _ => e σ, ← Finset.smul_sum, ← Matrix.mul_sum,
      sum_gammaLower_mul_gamma, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    norm_num
  rw [h, pw_smul_right]

end Slots

section Pairings

variable (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)

/-- **The double contraction `(01)(23)`.** -/
theorem sum_smw_0123 : ∑ σ, ∑ τ, smw P (gammaLower σ) (gamma σ) (gammaLower τ) (gamma τ) =
    -16 * pw (contractP P) 𝟙 𝟙 := by
  simp only [sum_smw_23, ← Finset.mul_sum, sum_pw_gammaLower_gamma']
  ring

/-- **The double contraction `(02)(13)`.** -/
theorem sum_smw_0213 : ∑ σ, ∑ τ, smw P (gammaLower σ) (gammaLower τ) (gamma σ) (gamma τ) =
    8 * pw (contractP P) 𝟙 𝟙 := by
  simp only [sum_smw_13, sum_gamma_gamma_gammaLower, Matrix.mul_smul, Matrix.smul_mul,
    ← Finset.smul_sum, smul_smul, pw_smul_right]
  rw [← Finset.mul_sum, sum_pw_gammaLower_gamma']
  ring

/-- **The double contraction `(03)(12)`.** -/
theorem sum_smw_0312 : ∑ σ, ∑ τ, smw P (gammaLower σ) (gammaLower τ) (gamma τ) (gamma σ) =
    -16 * pw (contractP P) 𝟙 𝟙 := by
  simp only [sum_smw_12, ← Finset.mul_sum, sum_pw_gammaLower_gamma']
  ring

end Pairings

/-! ### The three coefficients of `S₋` -/

section Coeff

variable (P : Params) (z : Fin 8 → ℝ) (u : ℝ)

/-- **`T₁` of `S₋`**: `T₁ = -π⁴ κ η² U⁻² · 6 pw(ΓP; Ē₀, Ē₁ Γ(Ē₂) Ē₃)`. -/
theorem classT1_Sm_eq : classT1 .Sm permSm P z u =
    ladderK P * ((symanzikU (classAlpha .Sm) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (6 * pw (contractP (ladderPauli P u)) (classE .Sm P z u 0)
        (classE .Sm P z u 1 * gamM (classE .Sm P z u 2) * classE .Sm P z u 3)) := by
  rw [classT1_eq_of_pat (isWeightPattern_Sm P), smw_eq_pw]

/-- **`T₂` of `S₋`** through base patterns. -/
theorem classT2_Sm_eq : classT2 .Sm permSm P z u =
    ladderK P * ((symanzikU (classAlpha .Sm) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 1 *
          (2 * pw (contractP (ladderPauli P u)) 𝟙
            (gamM (classE .Sm P z u 2) * classE .Sm P z u 3)) +
        classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 2 *
          (2 * pw (contractP (mulLeftP (classE .Sm P z u 3) (contractP (ladderPauli P u)))) 𝟙
            (classE .Sm P z u 1)) +
        classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 3 *
          pw (contractP (contractP (ladderPauli P u))) 𝟙
            (classE .Sm P z u 1 * gamM (classE .Sm P z u 2)) +
        classC .Sm (symanzikMatrix (classAlpha .Sm) z) 1 2 *
          (-8 * pw (contractP (ladderPauli P u)) (classE .Sm P z u 0) (classE .Sm P z u 3)) +
        classC .Sm (symanzikMatrix (classAlpha .Sm) z) 1 3 *
          pw (contractP (ladderPauli P u)) (classE .Sm P z u 0) (gamM (gamM (classE .Sm P z u 2))) +
        classC .Sm (symanzikMatrix (classAlpha .Sm) z) 2 3 *
          (-8 * pw (contractP (ladderPauli P u)) (classE .Sm P z u 0) (classE .Sm P z u 1))) := by
  rw [classT2_eq_of_pat (isWeightPattern_Sm P), sum_smw_01, sum_smw_02, sum_smw_03, sum_smw_12,
    sum_smw_13, sum_smw_23]

/-- **`T₃` of `S₋`** through base patterns. -/
theorem classT3_Sm_eq : classT3 .Sm permSm P z u =
    ladderK P * ((symanzikU (classAlpha .Sm) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (1 / 4 * (classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 1 *
          classC .Sm (symanzikMatrix (classAlpha .Sm) z) 2 3 *
            (-16 * pw (contractP (ladderPauli P u)) 𝟙 𝟙) +
        classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 2 *
          classC .Sm (symanzikMatrix (classAlpha .Sm) z) 1 3 *
            (8 * pw (contractP (ladderPauli P u)) 𝟙 𝟙) +
        classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 3 *
          classC .Sm (symanzikMatrix (classAlpha .Sm) z) 1 2 *
            (-16 * pw (contractP (ladderPauli P u)) 𝟙 𝟙))) := by
  rw [classT3_eq_of_pat (isWeightPattern_Sm P), sum_smw_0123, sum_smw_0213, sum_smw_0312]

end Coeff

end QED.TwoLoop.UnitSCGraph

end
