/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCGraphCross
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# The contractions of the corner class `C₊`

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the `S + C` link, graph half. The class `C₊`
has the external photon at vertex `1`, the outer photon `(0 3)` and the inner photon `(2 4)`, the
pairing `permCp`. After the Pauli projection its numerator is a combination of the traces
(`cpw`)

`cpw(P; Y₀, Y₁, Y₂, Y₃) = ∑_{μνσ} tr(γ^ν P_μ γ^σ Y₀ γ_ν Y₁ γ_σ Y₂ γ^μ Y₃)`

(`isWeightPattern_Cp`). The inner photon `σ` encloses the outer vertex `ν`: the `σ`-sum is the
one-loop vertex family `H_ν(Y₀, Y₁) = Γ(Y₀ γ_ν Y₁)`, and `cpw = pp(P, H(Y₀, Y₁); Y₂, Y₃)`
(`cpw_eq_pp`). The Wick contractions of pairs of slots reduce, by the Clifford relations and the
sandwich recursion `Γ(X a̸) = -Γ(X) a̸ - 2 a̸ X` alone (for arbitrary matrices), to the patterns
`pp` and `pw` (`sum_cpw_01`, …, `sum_cpw_0312`); so the three coefficients `T₁, T₂, T₃` of the
projected numerator are explicit combinations of them (`classT1_Cp_eq`, `classT2_Cp_eq`,
`classT3_Cp_eq`). The reductions were checked numerically on random matrices and, through the
planar evaluation, against exact Dirac traces (`scripts/numerics/sc_graph/cross_identities.py`,
`cp_planar.py`).
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

/-- **The `C₊` contraction** `∑_{μνσ} tr(γ^ν P_μ γ^σ Y₀ γ_ν Y₁ γ_σ Y₂ γ^μ Y₃)`. -/
noncomputable def cpw (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ) :
    ℂ :=
  ∑ μ, ∑ ν, ∑ σ, trace (gamma ν * P μ * gamma σ * Y₀ * gammaLower ν * Y₁ * gammaLower σ * Y₂ *
    gamma μ * Y₃)

theorem permCp_zero : permCp 0 = 1 := rfl
theorem permCp_one : permCp 1 = 0 := rfl
theorem permCp_two : permCp 2 = 3 := rfl
theorem permCp_three : permCp 3 = 2 := rfl
theorem permCp_four : permCp 4 = 4 := rfl

/-- **The `C₊` chain sum is the `C₊` contraction**: `∑_μ ∑_l c_{μ,l} ch(B_{μ,l}; Y) = η² cpw(P; Y)`. -/
theorem isWeightPattern_Cp (P : Params) : IsWeightPattern permCp P cpw := by
  intro p' p Y₀ Y₁ Y₂ Y₃
  unfold cpw
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [sum_fin5]
  simp only [classWeight, ladderB, ch, permCp_zero, permCp_one, permCp_two, permCp_three,
    permCp_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single μ (fun b _ hb => by simp [kron, hb]) (by simp)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single a (fun d _ hd => by simp [pvEta, Minkowski.metric, Ne.symm hd]) (by simp),
    Finset.sum_eq_single c (fun e _ he => by simp [pvEta, Minkowski.metric, Ne.symm he]) (by simp)]
  simp only [kron, ite_true, one_mul, pvEta, pvConst, gammaLower_eq_metric_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  push_cast
  ring

/-! ### The vertex form -/

section Vertex

variable (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ)

/-- **The `C₊` contraction through the vertex family**: `cpw(P; Y) = pp(P, H(Y₀, Y₁); Y₂, Y₃)`. -/
theorem cpw_eq_pp : cpw P Y₀ Y₁ Y₂ Y₃ = pp P (hfam Y₀ Y₁) Y₂ Y₃ := by
  unfold cpw pp
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  simp only [hfam_apply, gamM, Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  calc trace (gamma ν * P μ * gamma σ * Y₀ * gammaLower ν * Y₁ * gammaLower σ * Y₂ * gamma μ * Y₃)
      = trace ((gamma ν * P μ) * (gamma σ * (Y₀ * gammaLower ν * Y₁) * gammaLower σ * Y₂ *
          gamma μ * Y₃)) := by simp only [Matrix.mul_assoc]
    _ = trace ((gamma σ * (Y₀ * gammaLower ν * Y₁) * gammaLower σ * Y₂ * gamma μ * Y₃) *
          (gamma ν * P μ)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

end Vertex

/-! ### The families of the contracted vertex -/

theorem gamM_sum (X : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : gamM (∑ τ, X τ) = ∑ τ, gamM (X τ) := by
  simp only [gamM, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_comm

/-- `∑_τ H_ν(γ_τ, γ^τ) = 4 γ_ν`. -/
theorem sum_hfam_gammaLower_gamma (ν : Fin 4) :
    ∑ τ, hfam (gammaLower τ) (gamma τ) ν = (4 : ℂ) • gammaLower ν := by
  simp only [hfam_apply]
  rw [← gamM_sum, sum_gammaLower_gammaLower_gamma, gamM_smul, gamM_gammaLower, smul_smul]
  norm_num

/-- `∑_τ H_ν(Y₀, γ_τ) γ^τ = 2 H_ν(Y₀, 1)`. -/
theorem sum_hfam_gammaLower_mul_gamma (Y₀ : Matrix (Fin 4) (Fin 4) ℂ) (ν : Fin 4) :
    ∑ τ, hfam Y₀ (gammaLower τ) ν * gamma τ = (2 : ℂ) • hfam Y₀ 𝟙 ν := by
  simp only [hfam_apply, gamM, Matrix.sum_mul, Matrix.mul_one]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have e : ∀ τ, gamma σ * (Y₀ * gammaLower ν * gammaLower τ) * gammaLower σ * gamma τ =
      (gamma σ * Y₀ * gammaLower ν) * (gammaLower τ * gammaLower σ * gamma τ) := fun τ => by
    simp only [Matrix.mul_assoc]
  rw [Finset.sum_congr rfl fun τ _ => e τ, ← Matrix.mul_sum, sum_gammaLower_gammaLower_gamma,
    Matrix.mul_smul]
  simp only [Matrix.mul_assoc]

/-- The family `K_ν(Y₁) = -Γ(Γ(γ_ν Y₁)) + 8 γ_ν Y₁` of the contraction of the slots `0, 2`. -/
noncomputable def kfam (Y₁ : Matrix (Fin 4) (Fin 4) ℂ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun ν => -gamM (gamM (gammaLower ν * Y₁)) + (8 : ℂ) • (gammaLower ν * Y₁)

/-- `∑_τ H_ν(γ_τ, Y₁) γ^τ = K_ν(Y₁)`. -/
theorem sum_hfam_mul_gamma_kfam (Y₁ : Matrix (Fin 4) (Fin 4) ℂ) (ν : Fin 4) :
    ∑ τ, hfam (gammaLower τ) Y₁ ν * gamma τ = kfam Y₁ ν := by
  have e : ∀ τ, hfam (gammaLower τ) Y₁ ν * gamma τ =
      -(gammaLower τ * gamM (gammaLower ν * Y₁) * gamma τ) -
        (2 : ℂ) • ((gammaLower ν * Y₁) * (gammaLower τ * gamma τ)) := fun τ => by
    rw [hfam_apply, Matrix.mul_assoc (gammaLower τ), gamM_gammaLower_mul]
    simp only [Matrix.sub_mul, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [Finset.sum_congr rfl fun τ _ => e τ, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    sum_gammaLower_mul_gamma', ← Finset.smul_sum, ← Matrix.mul_sum, sum_gammaLower_mul_gamma,
    kfam]
  simp only [Matrix.mul_smul, Matrix.mul_one, smul_smul]
  module

/-! ### The single contractions -/

section Slots

variable (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ)

/-- **Slots `0, 1` contracted.** -/
theorem sum_cpw_01 : ∑ τ, cpw P (gammaLower τ) (gamma τ) Y₂ Y₃ = 4 * pp P gammaLower Y₂ Y₃ := by
  simp only [cpw_eq_pp]
  rw [pp_sum]
  simp only [sum_hfam_gammaLower_gamma]
  exact pp_smul P Y₂ Y₃ 4 gammaLower

/-- **Slots `1, 2` contracted.** -/
theorem sum_cpw_12 : ∑ τ, cpw P Y₀ (gammaLower τ) (gamma τ) Y₃ = 2 * pp P (hfam Y₀ 𝟙) 𝟙 Y₃ := by
  simp only [cpw_eq_pp]
  rw [Finset.sum_congr rfl fun τ _ => pp_left P (gamma τ) Y₃ (hfam Y₀ (gammaLower τ)), pp_sum]
  simp only [mulRightP, sum_hfam_gammaLower_mul_gamma]
  exact pp_smul P 𝟙 Y₃ 2 (hfam Y₀ 𝟙)

/-- `∑_τ pp(P, H; γ_τ, γ^τ) = 2 pp(P, H; 1, 1)`. -/
theorem sum_pp_gammaLower_gamma (H : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ τ, pp P H (gammaLower τ) (gamma τ) = 2 * pp P H 𝟙 𝟙 := by
  unfold pp
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have h : ∑ τ, trace (H ν * gammaLower τ * gamma μ * gamma τ * gamma ν * P μ) =
      trace (H ν * (∑ τ, gammaLower τ * gamma μ * gamma τ) * gamma ν * P μ) := by
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, Matrix.mul_assoc]
  rw [h, sum_gammaLower_gamma_gamma]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_one]

/-- **Slots `2, 3` contracted.** -/
theorem sum_cpw_23 : ∑ τ, cpw P Y₀ Y₁ (gammaLower τ) (gamma τ) = 2 * pp P (hfam Y₀ Y₁) 𝟙 𝟙 := by
  simp only [cpw_eq_pp]
  exact sum_pp_gammaLower_gamma P _

/-- **Slots `0, 2` contracted.** -/
theorem sum_cpw_02 : ∑ τ, cpw P (gammaLower τ) Y₁ (gamma τ) Y₃ = pp P (kfam Y₁) 𝟙 Y₃ := by
  simp only [cpw_eq_pp]
  rw [Finset.sum_congr rfl fun τ _ => pp_left P (gamma τ) Y₃ (hfam (gammaLower τ) Y₁), pp_sum]
  simp only [mulRightP, sum_hfam_mul_gamma_kfam]

/-- The matrix identity behind the contraction of the slots `1, 3`. -/
theorem sum_gamM_mul_13 (μ ν : Fin 4) :
    ∑ τ, gamM (Y₀ * gammaLower ν * gammaLower τ) * Y₂ * gamma μ * gamma τ =
      gamM (Y₀ * gammaLower ν) * gamM Y₂ * gamma μ +
        (2 : ℂ) • (gamM (Y₀ * gammaLower ν) * gamma μ * Y₂) +
        (2 : ℂ) • (gamM (Y₀ * gammaLower ν * Y₂) * gamma μ) +
        (4 : ℂ) • (gamma μ * Y₀ * gammaLower ν * Y₂) := by
  have e : ∀ τ, gamM (Y₀ * gammaLower ν * gammaLower τ) * Y₂ * gamma μ * gamma τ =
      -(gamM (Y₀ * gammaLower ν) * (gammaLower τ * (Y₂ * gamma μ) * gamma τ)) -
        (2 : ℂ) • (gammaLower τ * (Y₀ * gammaLower ν * Y₂ * gamma μ) * gamma τ) := fun τ => by
    rw [gamM_mul_gammaLower]
    simp only [Matrix.sub_mul, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [Finset.sum_congr rfl fun τ _ => e τ, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.smul_sum, ← Matrix.mul_sum, sum_gammaLower_mul_gamma', sum_gammaLower_mul_gamma',
    gamM_mul_gamma, gamM_mul_gamma]
  simp only [Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_smul, smul_sub, smul_neg, smul_smul,
    Matrix.mul_assoc]
  module

/-- **Slots `1, 3` contracted.** -/
theorem sum_cpw_13 : ∑ τ, cpw P Y₀ (gammaLower τ) Y₂ (gamma τ) =
    pp P (hfam Y₀ 𝟙) (gamM Y₂) 𝟙 + 2 * pp P (hfam Y₀ 𝟙) 𝟙 Y₂ + 2 * pp P (hfam Y₀ Y₂) 𝟙 𝟙 +
      4 * pw P 𝟙 (Y₀ * gamM Y₂) := by
  simp only [cpw_eq_pp]
  have hpw : pw P 𝟙 (Y₀ * gamM Y₂) =
      ∑ μ, ∑ ν, trace (gamma μ * Y₀ * gammaLower ν * Y₂ * gamma ν * P μ) := by
    unfold pw
    refine Finset.sum_congr rfl fun μ _ => ?_
    have h : ∑ ν, trace (gamma μ * Y₀ * gammaLower ν * Y₂ * gamma ν * P μ) =
        trace ((gamma μ * Y₀) * (∑ ν, gammaLower ν * Y₂ * gamma ν) * P μ) := by
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, Matrix.mul_assoc]
    rw [h, sum_gammaLower_mul_gamma', Matrix.mul_one]
    calc trace (P μ * gamma μ * (Y₀ * gamM Y₂)) = trace (P μ * (gamma μ * Y₀ * gamM Y₂)) := by
          simp only [Matrix.mul_assoc]
      _ = trace (gamma μ * Y₀ * gamM Y₂ * P μ) := Matrix.trace_mul_comm _ _
  rw [hpw]
  unfold pp
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have h : ∑ τ, trace (hfam Y₀ (gammaLower τ) ν * Y₂ * gamma μ * gamma τ * gamma ν * P μ) =
      trace ((∑ τ, gamM (Y₀ * gammaLower ν * gammaLower τ) * Y₂ * gamma μ * gamma τ) * gamma ν *
        P μ) := by
    simp only [hfam_apply, Matrix.sum_mul, Matrix.trace_sum]
  rw [h, sum_gamM_mul_13]
  simp only [hfam_apply, Matrix.mul_one, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul]
  rw [← Matrix.mul_sum]

/-- The matrix identity behind the contraction of the slots `0, 3`:
`∑_τ γ^τ X γ_τ`-moves around the trace. -/
theorem sum_cpw_03_term (μ ν : Fin 4) :
    ∑ τ, trace (gamM (gammaLower τ * (gammaLower ν * Y₁)) * Y₂ * gamma μ * gamma τ * gamma ν *
        P μ) =
      trace (gamM (gammaLower ν * Y₁) * Y₂ * gamma μ * gamma ν * gamM (P μ)) +
        2 * trace (gamM (gammaLower ν * Y₁) * Y₂ * gamma μ * P μ * gamma ν) +
        2 * trace (gammaLower ν * Y₁ * gamM Y₂ * gamma μ * gamma ν * P μ) +
        4 * trace (gammaLower ν * Y₁ * gamma μ * Y₂ * gamma ν * P μ) := by
  have e : ∀ τ, trace (gamM (gammaLower τ * (gammaLower ν * Y₁)) * Y₂ * gamma μ * gamma τ *
      gamma ν * P μ) =
      -trace (gamM (gammaLower ν * Y₁) * Y₂ * gamma μ * (gamma τ * (gamma ν * P μ) *
        gammaLower τ)) -
        2 * trace (gammaLower ν * Y₁ * (gammaLower τ * (Y₂ * gamma μ) * gamma τ) * gamma ν *
          P μ) := fun τ => by
    have c1 : trace (gammaLower τ * gamM (gammaLower ν * Y₁) * Y₂ * gamma μ * gamma τ * gamma ν *
        P μ) = trace (gamM (gammaLower ν * Y₁) * Y₂ * gamma μ * (gamma τ * (gamma ν * P μ) *
          gammaLower τ)) := by
      calc trace (gammaLower τ * gamM (gammaLower ν * Y₁) * Y₂ * gamma μ * gamma τ * gamma ν *
            P μ)
          = trace (gammaLower τ * (gamM (gammaLower ν * Y₁) * Y₂ * gamma μ * gamma τ * gamma ν *
            P μ)) := by simp only [Matrix.mul_assoc]
        _ = trace ((gamM (gammaLower ν * Y₁) * Y₂ * gamma μ * gamma τ * gamma ν * P μ) *
            gammaLower τ) := Matrix.trace_mul_comm _ _
        _ = _ := by simp only [Matrix.mul_assoc]
    have c2 : trace (gammaLower ν * Y₁ * gammaLower τ * Y₂ * gamma μ * gamma τ * gamma ν * P μ) =
        trace (gammaLower ν * Y₁ * (gammaLower τ * (Y₂ * gamma μ) * gamma τ) * gamma ν * P μ) := by
      simp only [Matrix.mul_assoc]
    rw [gamM_gammaLower_mul]
    simp only [Matrix.sub_mul, Matrix.neg_mul, Matrix.smul_mul, Matrix.trace_sub,
      Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul]
    rw [c1, c2]
  rw [Finset.sum_congr rfl fun τ _ => e τ, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum]
  have h1 : ∑ τ, trace (gamM (gammaLower ν * Y₁) * Y₂ * gamma μ * (gamma τ * (gamma ν * P μ) *
      gammaLower τ)) = trace (gamM (gammaLower ν * Y₁) * Y₂ * gamma μ * gamM (gamma ν * P μ)) := by
    rw [← Matrix.trace_sum, ← Matrix.mul_sum]
  have h2 : ∑ τ, trace (gammaLower ν * Y₁ * (gammaLower τ * (Y₂ * gamma μ) * gamma τ) * gamma ν *
      P μ) = trace (gammaLower ν * Y₁ * gamM (Y₂ * gamma μ) * gamma ν * P μ) := by
    rw [← sum_gammaLower_mul_gamma' (Y₂ * gamma μ), ← Matrix.trace_sum,
      Finset.mul_sum (s := Finset.univ)
        (f := fun τ => gammaLower τ * (Y₂ * gamma μ) * gamma τ) (a := gammaLower ν * Y₁),
      Finset.sum_mul (s := Finset.univ)
        (f := fun τ => gammaLower ν * Y₁ * (gammaLower τ * (Y₂ * gamma μ) * gamma τ)),
      Finset.sum_mul (s := Finset.univ)
        (f := fun τ => gammaLower ν * Y₁ * (gammaLower τ * (Y₂ * gamma μ) * gamma τ) * gamma ν)]
  rw [h1, h2, gamM_gamma_mul, gamM_mul_gamma]
  simp only [Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_smul, Matrix.sub_mul, Matrix.neg_mul,
    Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul,
    Matrix.mul_assoc]
  ring

/-- **Slots `0, 3` contracted.** -/
theorem sum_cpw_03 : ∑ τ, cpw P (gammaLower τ) Y₁ Y₂ (gamma τ) =
    pp (contractP P) (hfam 𝟙 Y₁) Y₂ 𝟙 + 4 * pw P (gamM Y₁ * Y₂) 𝟙 +
      2 * pw (contractP P) (Y₁ * gamM Y₂) 𝟙 + 4 * pw (contractP P) Y₁ Y₂ := by
  simp only [cpw_eq_pp]
  unfold pp
  rw [Finset.sum_comm]
  have hL : ∀ μ, ∑ τ, ∑ ν, trace (hfam (gammaLower τ) Y₁ ν * Y₂ * gamma μ * gamma τ * gamma ν *
      P μ) =
      ∑ ν, (trace (gamM (gammaLower ν * Y₁) * Y₂ * gamma μ * gamma ν * gamM (P μ)) +
        2 * trace (gamM (gammaLower ν * Y₁) * Y₂ * gamma μ * P μ * gamma ν) +
        2 * trace (gammaLower ν * Y₁ * gamM Y₂ * gamma μ * gamma ν * P μ) +
        4 * trace (gammaLower ν * Y₁ * gamma μ * Y₂ * gamma ν * P μ)) := fun μ => by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← sum_cpw_03_term]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hfam_apply, Matrix.mul_assoc (gammaLower τ)]
  simp only [Finset.sum_congr rfl fun μ _ => hL μ, Finset.sum_add_distrib, ← Finset.mul_sum]
  -- the four pieces
  have e1 : ∑ μ, ∑ ν, trace (gamM (gammaLower ν * Y₁) * Y₂ * gamma μ * gamma ν * gamM (P μ)) =
      ∑ μ, ∑ ν, trace (hfam 𝟙 Y₁ ν * Y₂ * gamma μ * 𝟙 * gamma ν * contractP P μ) := by
    simp only [hfam_apply, Matrix.one_mul, Matrix.mul_one]
    rfl
  have e2 : ∑ μ, ∑ ν, trace (gamM (gammaLower ν * Y₁) * Y₂ * gamma μ * P μ * gamma ν) =
      2 * pw P (gamM Y₁ * Y₂) 𝟙 := by
    unfold pw
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have h : ∑ ν, trace (gamM (gammaLower ν * Y₁) * Y₂ * gamma μ * P μ * gamma ν) =
        trace ((∑ ν, gamma ν * gamM (gammaLower ν * Y₁)) * (Y₂ * gamma μ * P μ)) := by
      rw [Finset.sum_mul (s := Finset.univ) (f := fun ν => gamma ν * gamM (gammaLower ν * Y₁)),
        Matrix.trace_sum]
      refine Finset.sum_congr rfl fun ν _ => ?_
      calc trace (gamM (gammaLower ν * Y₁) * Y₂ * gamma μ * P μ * gamma ν)
          = trace (gamma ν * (gamM (gammaLower ν * Y₁) * Y₂ * gamma μ * P μ)) :=
            Matrix.trace_mul_comm _ _
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [h, sum_gamma_mul_gamM_gammaLower_mul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      Matrix.mul_one]
    congr 1
    calc trace (gamM Y₁ * (Y₂ * gamma μ * P μ)) = trace ((gamM Y₁ * Y₂ * gamma μ) * P μ) := by
          simp only [Matrix.mul_assoc]
      _ = trace (P μ * (gamM Y₁ * Y₂ * gamma μ)) := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  have e34 : ∀ (A B : Matrix (Fin 4) (Fin 4) ℂ),
      ∑ μ, ∑ ν, trace (gammaLower ν * A * gamma μ * B * gamma ν * P μ) =
        pw (contractP P) A B := fun A B => by
    unfold pw contractP
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [Matrix.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    calc trace (gammaLower ν * A * gamma μ * B * gamma ν * P μ)
        = trace ((gammaLower ν * A * gamma μ * B) * (gamma ν * P μ)) := by
          simp only [Matrix.mul_assoc]
      _ = trace ((gamma ν * P μ) * (gammaLower ν * A * gamma μ * B)) := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  have e3 : ∑ μ, ∑ ν, trace (gammaLower ν * Y₁ * gamM Y₂ * gamma μ * gamma ν * P μ) =
      pw (contractP P) (Y₁ * gamM Y₂) 𝟙 := by
    rw [← e34]
    simp only [Matrix.mul_one, Matrix.mul_assoc]
  have e4 : ∑ μ, ∑ ν, trace (gammaLower ν * Y₁ * gamma μ * Y₂ * gamma ν * P μ) =
      pw (contractP P) Y₁ Y₂ := e34 Y₁ Y₂
  rw [e1, e2, e3, e4]
  ring

end Slots

/-! ### The double contractions -/

section Pairings

variable (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)

/-- `pp(P, γ_·; 1, 1) = 2 pw(P; 1, 1)`. -/
theorem pp_gammaLower_one_one : pp P gammaLower 𝟙 𝟙 = 2 * pw P 𝟙 𝟙 := by
  unfold pp pw
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h : ∑ ν, trace (gammaLower ν * 𝟙 * gamma μ * 𝟙 * gamma ν * P μ) =
      trace ((∑ ν, gammaLower ν * gamma μ * gamma ν) * P μ) := by
    simp only [Matrix.mul_one, Matrix.sum_mul, Matrix.trace_sum]
  rw [h, sum_gammaLower_gamma_gamma, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    Matrix.mul_one, Matrix.mul_one, Matrix.trace_mul_comm]

/-- `∑_σ pp(P, H(γ_σ, 1); 1, γ^σ) = -16 pw(P; 1, 1)`. -/
theorem sum_pp_hfam_one : ∑ σ, pp P (hfam (gammaLower σ) 𝟙) 𝟙 (gamma σ) = -16 * pw P 𝟙 𝟙 := by
  have hH : ∀ σ ν, hfam (gammaLower σ) 𝟙 ν =
      -((2 : ℂ) • (gammaLower σ * gammaLower ν)) - (2 : ℂ) • (gammaLower ν * gammaLower σ) :=
    fun σ ν => by
      rw [hfam_apply, Matrix.mul_one, gamM_gammaLower_mul, gamM_gammaLower, Matrix.mul_smul]
  unfold pp pw
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  simp only [hH, Matrix.mul_one, Matrix.sub_mul, Matrix.neg_mul, Matrix.smul_mul,
    Matrix.trace_sub, Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, ← Finset.mul_sum]
  have h1 : ∑ ν, ∑ σ, trace (gammaLower σ * gammaLower ν * gamma μ * gamma σ * gamma ν * P μ) =
      4 * trace (P μ * gamma μ) := by
    have e : ∀ ν, ∑ σ, trace (gammaLower σ * gammaLower ν * gamma μ * gamma σ * gamma ν * P μ) =
        trace (gamM (gammaLower ν * gamma μ) * gamma ν * P μ) := fun ν => by
      rw [← sum_gammaLower_mul_gamma']
      simp only [Matrix.sum_mul, Matrix.trace_sum, Matrix.mul_assoc]
    simp only [e, gamM_gammaLower_mul, gamM_gamma, Matrix.mul_smul, Matrix.sub_mul,
      Matrix.neg_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_neg, Matrix.trace_smul,
      smul_eq_mul, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
    have a : ∑ ν, trace (gammaLower ν * gamma μ * gamma ν * P μ) = 2 * trace (P μ * gamma μ) := by
      rw [← Matrix.trace_sum, ← Finset.sum_mul, sum_gammaLower_gamma_gamma,
        Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm]
    have b : ∑ ν, trace (gamma μ * gammaLower ν * gamma ν * P μ) = -4 * trace (P μ * gamma μ) := by
      have : ∑ ν, gamma μ * gammaLower ν * gamma ν = gamma μ * ∑ ν, gammaLower ν * gamma ν := by
        simp only [Matrix.mul_sum, Matrix.mul_assoc]
      rw [← Matrix.trace_sum, ← Finset.sum_mul, this, sum_gammaLower_mul_gamma, Matrix.mul_smul,
        Matrix.mul_one, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm]
    rw [a, b]
    ring
  have h2 : ∑ ν, ∑ σ, trace (gammaLower ν * gammaLower σ * gamma μ * gamma σ * gamma ν * P μ) =
      4 * trace (P μ * gamma μ) := by
    have e : ∀ ν, ∑ σ, trace (gammaLower ν * gammaLower σ * gamma μ * gamma σ * gamma ν * P μ) =
        trace (gammaLower ν * (∑ σ, gammaLower σ * gamma μ * gamma σ) * gamma ν * P μ) :=
      fun ν => by simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, Matrix.mul_assoc]
    simp only [e, sum_gammaLower_gamma_gamma, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
      smul_eq_mul, ← Finset.mul_sum]
    rw [← Matrix.trace_sum, ← Finset.sum_mul, sum_gammaLower_gamma_gamma,
      Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm]
    ring
  rw [h1, h2]
  ring

/-- **The double contraction `(01)(23)`.** -/
theorem sum_cpw_0123 : ∑ σ, ∑ τ, cpw P (gammaLower σ) (gamma σ) (gammaLower τ) (gamma τ) =
    16 * pw P 𝟙 𝟙 := by
  simp only [sum_cpw_23, ← Finset.mul_sum, pp_sum, sum_hfam_gammaLower_gamma]
  rw [pp_smul P 𝟙 𝟙 4 gammaLower, pp_gammaLower_one_one]
  ring

/-- **The double contraction `(02)(13)`.** -/
theorem sum_cpw_0213 : ∑ σ, ∑ τ, cpw P (gammaLower σ) (gammaLower τ) (gamma σ) (gamma τ) =
    -32 * pw P 𝟙 𝟙 := by
  simp only [sum_cpw_13, Finset.sum_add_distrib, ← Finset.mul_sum, gamM_gamma, pp_smul_left]
  have h1 : ∑ σ, pp P (hfam (gammaLower σ) 𝟙) (gamma σ) 𝟙 = 8 * pw P 𝟙 𝟙 := by
    rw [Finset.sum_congr rfl fun σ _ =>
      pp_left P (gamma σ) 𝟙 (hfam (gammaLower σ) 𝟙), pp_sum]
    simp only [mulRightP, sum_hfam_mul_gamma_kfam]
    have hk : kfam 𝟙 = fun ν => (4 : ℂ) • gammaLower ν := by
      funext ν
      simp only [kfam, Matrix.mul_one, gamM_gammaLower, gamM_smul, smul_smul]
      module
    rw [hk, pp_smul, pp_gammaLower_one_one]
    ring
  have h3 : ∑ σ, pp P (hfam (gammaLower σ) (gamma σ)) 𝟙 𝟙 = 8 * pw P 𝟙 𝟙 := by
    rw [pp_sum]
    simp only [sum_hfam_gammaLower_gamma]
    rw [pp_smul P 𝟙 𝟙 4 gammaLower, pp_gammaLower_one_one]
    ring
  have h4 : ∑ σ, pw P 𝟙 (gammaLower σ * ((2 : ℂ) • gamma σ)) = -8 * pw P 𝟙 𝟙 := by
    unfold pw
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Matrix.trace_sum, ← Matrix.mul_sum, sum_gammaLower_two_gamma, Matrix.mul_smul,
      Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
  rw [h1, sum_pp_hfam_one, h3, h4]
  ring

/-- **The double contraction `(03)(12)`.** -/
theorem sum_cpw_0312 : ∑ σ, ∑ τ, cpw P (gammaLower σ) (gammaLower τ) (gamma τ) (gamma σ) =
    -32 * pw P 𝟙 𝟙 := by
  simp only [sum_cpw_12, ← Finset.mul_sum, sum_pp_hfam_one]
  ring

end Pairings

/-! ### The three coefficients of `C₊` -/

section Coeff

variable (P : Params) (z : Fin 8 → ℝ) (u : ℝ)

/-- **`T₁` of `C₊`**: `T₁ = -π⁴ κ η² U⁻² · 6 pp(P, H(Ē₀, Ē₁); Ē₂, Ē₃)`. -/
theorem classT1_Cp_eq : classT1 .Cp permCp P z u =
    ladderK P * ((symanzikU (classAlpha .Cp) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (6 * pp (ladderPauli P u) (hfam (classE .Cp P z u 0) (classE .Cp P z u 1))
        (classE .Cp P z u 2) (classE .Cp P z u 3)) := by
  rw [classT1_eq_of_pat (isWeightPattern_Cp P), cpw_eq_pp]

/-- **`T₂` of `C₊`** through the patterns `pp` and `pw`. -/
theorem classT2_Cp_eq : classT2 .Cp permCp P z u =
    ladderK P * ((symanzikU (classAlpha .Cp) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 1 *
          (4 * pp (ladderPauli P u) gammaLower (classE .Cp P z u 2) (classE .Cp P z u 3)) +
        classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 2 *
          pp (ladderPauli P u) (kfam (classE .Cp P z u 1)) 𝟙 (classE .Cp P z u 3) +
        classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 3 *
          (pp (contractP (ladderPauli P u)) (hfam 𝟙 (classE .Cp P z u 1)) (classE .Cp P z u 2) 𝟙 +
            4 * pw (ladderPauli P u) (gamM (classE .Cp P z u 1) * classE .Cp P z u 2) 𝟙 +
            2 * pw (contractP (ladderPauli P u)) (classE .Cp P z u 1 * gamM (classE .Cp P z u 2))
              𝟙 +
            4 * pw (contractP (ladderPauli P u)) (classE .Cp P z u 1) (classE .Cp P z u 2)) +
        classC .Cp (symanzikMatrix (classAlpha .Cp) z) 1 2 *
          (2 * pp (ladderPauli P u) (hfam (classE .Cp P z u 0) 𝟙) 𝟙 (classE .Cp P z u 3)) +
        classC .Cp (symanzikMatrix (classAlpha .Cp) z) 1 3 *
          (pp (ladderPauli P u) (hfam (classE .Cp P z u 0) 𝟙) (gamM (classE .Cp P z u 2)) 𝟙 +
            2 * pp (ladderPauli P u) (hfam (classE .Cp P z u 0) 𝟙) 𝟙 (classE .Cp P z u 2) +
            2 * pp (ladderPauli P u) (hfam (classE .Cp P z u 0) (classE .Cp P z u 2)) 𝟙 𝟙 +
            4 * pw (ladderPauli P u) 𝟙 (classE .Cp P z u 0 * gamM (classE .Cp P z u 2))) +
        classC .Cp (symanzikMatrix (classAlpha .Cp) z) 2 3 *
          (2 * pp (ladderPauli P u) (hfam (classE .Cp P z u 0) (classE .Cp P z u 1)) 𝟙 𝟙)) := by
  rw [classT2_eq_of_pat (isWeightPattern_Cp P), sum_cpw_01, sum_cpw_02, sum_cpw_03, sum_cpw_12,
    sum_cpw_13, sum_cpw_23]

/-- **`T₃` of `C₊`** through `pw`. -/
theorem classT3_Cp_eq : classT3 .Cp permCp P z u =
    ladderK P * ((symanzikU (classAlpha .Cp) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (1 / 4 * (classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 1 *
          classC .Cp (symanzikMatrix (classAlpha .Cp) z) 2 3 *
            (16 * pw (ladderPauli P u) 𝟙 𝟙) +
        classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 2 *
          classC .Cp (symanzikMatrix (classAlpha .Cp) z) 1 3 *
            (-32 * pw (ladderPauli P u) 𝟙 𝟙) +
        classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 3 *
          classC .Cp (symanzikMatrix (classAlpha .Cp) z) 1 2 *
            (-32 * pw (ladderPauli P u) 𝟙 𝟙))) := by
  rw [classT3_eq_of_pat (isWeightPattern_Cp P), sum_cpw_0123, sum_cpw_0213, sum_cpw_0312]

end Coeff

end QED.TwoLoop.UnitSCGraph

end
