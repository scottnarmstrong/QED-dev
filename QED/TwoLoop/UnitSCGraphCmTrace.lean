/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCGraphCpTrace
public import QED.TwoLoop.UnitSCGraphRev
import Mathlib.Tactic.Ring

/-!
# The contractions of the corner class `C₋`

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the `S + C` link, graph half. The class `C₋`
has the external photon at vertex `3`, the inner photon `(0 2)` and the outer photon `(1 4)`, the
pairing `permCm`. After the Pauli projection its numerator is a combination of the traces
(`cmw`)

`cmw(P; Y₀, Y₁, Y₂, Y₃) = ∑_{μνσ} tr(γ^ν P_μ γ^σ Y₀ γ^μ Y₁ γ_ν Y₂ γ_σ Y₃)`

(`isWeightPattern_Cm`). Reversing the trace (`QED/TwoLoop/UnitSCGraphRev.lean`) turns it into the
`C₊` contraction of the reversed matrices:
`cmw(P; Y₀, Y₁, Y₂, Y₃) = -cpw(P^R; Y₃^R, Y₂^R, Y₁^R, Y₀^R)` (`cmw_eq_cpw`), the mirror symmetry
`C₋ ↔ C₊` at the level of the traces. So every Wick contraction of `C₋` is a contraction of `C₊`
(slots `(k, l)` ↔ `(3 - l, 3 - k)`), and the three coefficients `T₁, T₂, T₃` of `C₋` are given by
the reductions of `QED/TwoLoop/UnitSCGraphCpTrace.lean` (`classT1_Cm_eq`, `classT2_Cm_eq`,
`classT3_Cm_eq`). Checked against exact Dirac traces by `scripts/numerics/sc_graph/cm_planar.py`.
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

/-- **The `C₋` contraction** `∑_{μνσ} tr(γ^ν P_μ γ^σ Y₀ γ^μ Y₁ γ_ν Y₂ γ_σ Y₃)`. -/
noncomputable def cmw (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ) :
    ℂ :=
  ∑ μ, ∑ ν, ∑ σ, trace (gamma ν * P μ * gamma σ * Y₀ * gamma μ * Y₁ * gammaLower ν * Y₂ *
    gammaLower σ * Y₃)

theorem permCm_zero : permCm 0 = 3 := rfl
theorem permCm_one : permCm 1 = 0 := rfl
theorem permCm_two : permCm 2 = 2 := rfl
theorem permCm_three : permCm 3 = 1 := rfl
theorem permCm_four : permCm 4 = 4 := rfl

/-- **The `C₋` chain sum is the `C₋` contraction**: `∑_μ ∑_l c_{μ,l} ch(B_{μ,l}; Y) = η² cmw(P; Y)`. -/
theorem isWeightPattern_Cm (P : Params) : IsWeightPattern permCm P cmw := by
  intro p' p Y₀ Y₁ Y₂ Y₃
  unfold cmw
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [sum_fin5]
  simp only [classWeight, ladderB, ch, permCm_zero, permCm_one, permCm_two, permCm_three,
    permCm_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single a (fun c _ hc => by simp [pvEta, Minkowski.metric, Ne.symm hc]) (by simp),
    Finset.sum_eq_single μ (fun d _ hd => by simp [kron, hd]) (by simp),
    Finset.sum_eq_single b (fun e _ he => by simp [pvEta, Minkowski.metric, Ne.symm he]) (by simp)]
  simp only [kron, ite_true, one_mul, pvEta, pvConst, gammaLower_eq_metric_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  push_cast
  ring

/-! ### Reversal -/

/-- The reversed family `P^R_μ = (P_μ)^R`. -/
noncomputable def revF (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => revM (P μ)

/-- A cyclic rotation of a trace of ten factors. -/
theorem trace_rot_ten (A B C D E F G H I J : Matrix (Fin 4) (Fin 4) ℂ) :
    trace (A * B * C * D * E * F * G * H * I * J) = trace (H * I * J * A * B * C * D * E * F * G) := by
  rw [show A * B * C * D * E * F * G * H * I * J = (A * B * C * D * E * F * G) * (H * I * J) by
    simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- **The mirror symmetry of the traces**: `cmw(P; Y) = -cpw(P^R; Y₃^R, Y₂^R, Y₁^R, Y₀^R)`. -/
theorem cmw_eq_cpw (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ) :
    cmw P Y₀ Y₁ Y₂ Y₃ = -cpw (revF P) (revM Y₃) (revM Y₂) (revM Y₁) (revM Y₀) := by
  unfold cmw cpw
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← trace_revM]
  simp only [revM_mul, revM_gamma, revM_gammaLower, Matrix.neg_mul, Matrix.mul_neg, neg_neg,
    Matrix.trace_neg, revF]
  rw [neg_inj]
  have h := trace_rot_ten (revM Y₃) (gammaLower σ) (revM Y₂) (gammaLower ν) (revM Y₁) (gamma μ)
    (revM Y₀) (gamma σ) (revM (P μ)) (gamma ν)
  simp only [Matrix.mul_assoc] at h ⊢
  exact h

/-! ### Exchanging the two halves of a contracted pair -/

theorem sum_swap_gamma (f : Matrix (Fin 4) (Fin 4) ℂ → Matrix (Fin 4) (Fin 4) ℂ → ℂ)
    (h₁ : ∀ (c : ℂ) A B, f (c • A) B = c * f A B) (h₂ : ∀ (c : ℂ) A B, f A (c • B) = c * f A B) :
    ∑ τ, f (gamma τ) (gammaLower τ) = ∑ τ, f (gammaLower τ) (gamma τ) := by
  simp only [gammaLower_eq_metric_smul, h₁, h₂]

section CpwSlots

variable (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ) (c : ℂ)

theorem cpw_smul_zero : cpw P (c • Y₀) Y₁ Y₂ Y₃ = c * cpw P Y₀ Y₁ Y₂ Y₃ := by
  simp only [cpw, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]

theorem cpw_smul_one : cpw P Y₀ (c • Y₁) Y₂ Y₃ = c * cpw P Y₀ Y₁ Y₂ Y₃ := by
  simp only [cpw, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]

theorem cpw_smul_two : cpw P Y₀ Y₁ (c • Y₂) Y₃ = c * cpw P Y₀ Y₁ Y₂ Y₃ := by
  simp only [cpw, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]

theorem cpw_smul_three : cpw P Y₀ Y₁ Y₂ (c • Y₃) = c * cpw P Y₀ Y₁ Y₂ Y₃ := by
  simp only [cpw, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]

theorem neg_eq_smul (X : Matrix (Fin 4) (Fin 4) ℂ) : -X = (-1 : ℂ) • X := by simp

end CpwSlots

/-- All four slots through a sign: the reversed contracted pairs. -/
theorem cpw_neg_neg_02 (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (A B C D : Matrix (Fin 4) (Fin 4) ℂ) :
    cpw P (-A) B (-C) D = cpw P A B C D := by
  rw [neg_eq_smul A, neg_eq_smul C, cpw_smul_zero, cpw_smul_two]; ring

theorem cpw_neg_neg_03 (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (A B C D : Matrix (Fin 4) (Fin 4) ℂ) :
    cpw P (-A) B C (-D) = cpw P A B C D := by
  rw [neg_eq_smul A, neg_eq_smul D, cpw_smul_zero, cpw_smul_three]; ring

theorem cpw_neg_neg_12 (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (A B C D : Matrix (Fin 4) (Fin 4) ℂ) :
    cpw P A (-B) (-C) D = cpw P A B C D := by
  rw [neg_eq_smul B, neg_eq_smul C, cpw_smul_one, cpw_smul_two]; ring

theorem cpw_neg_neg_13 (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (A B C D : Matrix (Fin 4) (Fin 4) ℂ) :
    cpw P A (-B) C (-D) = cpw P A B C D := by
  rw [neg_eq_smul B, neg_eq_smul D, cpw_smul_one, cpw_smul_three]; ring

theorem cpw_neg_neg_23 (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (A B C D : Matrix (Fin 4) (Fin 4) ℂ) :
    cpw P A B (-C) (-D) = cpw P A B C D := by
  rw [neg_eq_smul C, neg_eq_smul D, cpw_smul_two, cpw_smul_three]; ring

theorem cpw_neg_neg_01 (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (A B C D : Matrix (Fin 4) (Fin 4) ℂ) :
    cpw P (-A) (-B) C D = cpw P A B C D := by
  rw [neg_eq_smul A, neg_eq_smul B, cpw_smul_zero, cpw_smul_one]; ring

/-! ### The single contractions -/

section Slots

variable (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ)

/-- **Slots `0, 1` contracted** (the `C₊` slots `2, 3`). -/
theorem sum_cmw_01 : ∑ τ, cmw P (gammaLower τ) (gamma τ) Y₂ Y₃ =
    -(2 * pp (revF P) (hfam (revM Y₃) (revM Y₂)) 𝟙 𝟙) := by
  simp only [cmw_eq_cpw, revM_gamma, revM_gammaLower, cpw_neg_neg_23, Finset.sum_neg_distrib]
  rw [sum_swap_gamma (fun A B => cpw (revF P) (revM Y₃) (revM Y₂) A B)
    (fun c A B => cpw_smul_two _ _ _ _ _ c) (fun c A B => cpw_smul_three _ _ _ _ _ c),
    sum_cpw_23]

/-- **Slots `0, 2` contracted** (the `C₊` slots `1, 3`). -/
theorem sum_cmw_02 : ∑ τ, cmw P (gammaLower τ) Y₁ (gamma τ) Y₃ =
    -(pp (revF P) (hfam (revM Y₃) 𝟙) (gamM (revM Y₁)) 𝟙 +
      2 * pp (revF P) (hfam (revM Y₃) 𝟙) 𝟙 (revM Y₁) +
      2 * pp (revF P) (hfam (revM Y₃) (revM Y₁)) 𝟙 𝟙 +
      4 * pw (revF P) 𝟙 (revM Y₃ * gamM (revM Y₁))) := by
  simp only [cmw_eq_cpw, revM_gamma, revM_gammaLower, cpw_neg_neg_13, Finset.sum_neg_distrib]
  rw [sum_swap_gamma (fun A B => cpw (revF P) (revM Y₃) A (revM Y₁) B)
    (fun c A B => cpw_smul_one _ _ _ _ _ c) (fun c A B => cpw_smul_three _ _ _ _ _ c),
    sum_cpw_13]

/-- **Slots `0, 3` contracted** (the `C₊` slots `0, 3`). -/
theorem sum_cmw_03 : ∑ τ, cmw P (gammaLower τ) Y₁ Y₂ (gamma τ) =
    -(pp (contractP (revF P)) (hfam 𝟙 (revM Y₂)) (revM Y₁) 𝟙 +
      4 * pw (revF P) (gamM (revM Y₂) * revM Y₁) 𝟙 +
      2 * pw (contractP (revF P)) (revM Y₂ * gamM (revM Y₁)) 𝟙 +
      4 * pw (contractP (revF P)) (revM Y₂) (revM Y₁)) := by
  simp only [cmw_eq_cpw, revM_gamma, revM_gammaLower, cpw_neg_neg_03, Finset.sum_neg_distrib]
  rw [sum_swap_gamma (fun A B => cpw (revF P) A (revM Y₂) (revM Y₁) B)
    (fun c A B => cpw_smul_zero _ _ _ _ _ c) (fun c A B => cpw_smul_three _ _ _ _ _ c),
    sum_cpw_03]

/-- **Slots `1, 2` contracted** (the `C₊` slots `1, 2`). -/
theorem sum_cmw_12 : ∑ τ, cmw P Y₀ (gammaLower τ) (gamma τ) Y₃ =
    -(2 * pp (revF P) (hfam (revM Y₃) 𝟙) 𝟙 (revM Y₀)) := by
  simp only [cmw_eq_cpw, revM_gamma, revM_gammaLower, cpw_neg_neg_12, Finset.sum_neg_distrib]
  rw [sum_swap_gamma (fun A B => cpw (revF P) (revM Y₃) A B (revM Y₀))
    (fun c A B => cpw_smul_one _ _ _ _ _ c) (fun c A B => cpw_smul_two _ _ _ _ _ c),
    sum_cpw_12]

/-- **Slots `1, 3` contracted** (the `C₊` slots `0, 2`). -/
theorem sum_cmw_13 : ∑ τ, cmw P Y₀ (gammaLower τ) Y₂ (gamma τ) =
    -pp (revF P) (kfam (revM Y₂)) 𝟙 (revM Y₀) := by
  simp only [cmw_eq_cpw, revM_gamma, revM_gammaLower, cpw_neg_neg_02, Finset.sum_neg_distrib]
  rw [sum_swap_gamma (fun A B => cpw (revF P) A (revM Y₂) B (revM Y₀))
    (fun c A B => cpw_smul_zero _ _ _ _ _ c) (fun c A B => cpw_smul_two _ _ _ _ _ c),
    sum_cpw_02]

/-- **Slots `2, 3` contracted** (the `C₊` slots `0, 1`). -/
theorem sum_cmw_23 : ∑ τ, cmw P Y₀ Y₁ (gammaLower τ) (gamma τ) =
    -(4 * pp (revF P) gammaLower (revM Y₁) (revM Y₀)) := by
  simp only [cmw_eq_cpw, revM_gamma, revM_gammaLower, cpw_neg_neg_01, Finset.sum_neg_distrib]
  rw [sum_swap_gamma (fun A B => cpw (revF P) A B (revM Y₁) (revM Y₀))
    (fun c A B => cpw_smul_zero _ _ _ _ _ c) (fun c A B => cpw_smul_one _ _ _ _ _ c),
    sum_cpw_01]

end Slots

/-! ### The double contractions -/

section Pairings

variable (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)

/-- **The double contraction `(01)(23)`.** -/
theorem sum_cmw_0123 : ∑ σ, ∑ τ, cmw P (gammaLower σ) (gamma σ) (gammaLower τ) (gamma τ) =
    -(16 * pw (revF P) 𝟙 𝟙) := by
  simp only [sum_cmw_23, revM_gamma, revM_gammaLower, Finset.sum_neg_distrib, ← Finset.mul_sum]
  have h : ∀ τ : Fin 4, (∑ σ, pp (revF P) gammaLower (-gamma σ) (-gammaLower σ)) =
      ∑ σ, pp (revF P) gammaLower (gammaLower σ) (gamma σ) := fun _ => by
    simp only [neg_eq_smul, pp_smul_left, pp_smul_right]
    simp only [← mul_assoc, show ((-1 : ℂ) * -1) = 1 by ring, one_mul]
    exact sum_swap_gamma (fun A B => pp (revF P) gammaLower A B)
      (fun c A B => pp_smul_left _ _ _ _ c) (fun c A B => pp_smul_right _ _ _ _ c)
  rw [h 0, sum_pp_gammaLower_gamma, pp_gammaLower_one_one]
  ring

/-- **The double contraction `(02)(13)`.** -/
theorem sum_cmw_0213 : ∑ σ, ∑ τ, cmw P (gammaLower σ) (gammaLower τ) (gamma σ) (gamma τ) =
    32 * pw (revF P) 𝟙 𝟙 := by
  simp only [cmw_eq_cpw, revM_gamma, revM_gammaLower, Finset.sum_neg_distrib]
  have h : ∀ σ τ : Fin 4, cpw (revF P) (-gamma τ) (-gamma σ) (-gammaLower τ) (-gammaLower σ) =
      cpw (revF P) (gamma τ) (gamma σ) (gammaLower τ) (gammaLower σ) := fun σ τ => by
    rw [cpw_neg_neg_02, cpw_neg_neg_13]
  simp only [h]
  have h1 : ∀ σ, ∑ τ, cpw (revF P) (gamma τ) (gamma σ) (gammaLower τ) (gammaLower σ) =
      ∑ τ, cpw (revF P) (gammaLower τ) (gamma σ) (gamma τ) (gammaLower σ) := fun σ =>
    sum_swap_gamma (fun A B => cpw (revF P) A (gamma σ) B (gammaLower σ))
      (fun c A B => cpw_smul_zero _ _ _ _ _ c) (fun c A B => cpw_smul_two _ _ _ _ _ c)
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ τ, ∑ σ, cpw (revF P) (gammaLower τ) (gamma σ) (gamma τ) (gammaLower σ) =
      ∑ σ, cpw (revF P) (gammaLower τ) (gammaLower σ) (gamma τ) (gamma σ) := fun τ =>
    sum_swap_gamma (fun A B => cpw (revF P) (gammaLower τ) A (gamma τ) B)
      (fun c A B => cpw_smul_one _ _ _ _ _ c) (fun c A B => cpw_smul_three _ _ _ _ _ c)
  simp only [h2, sum_cpw_0213]
  ring

/-- **The double contraction `(03)(12)`.** -/
theorem sum_cmw_0312 : ∑ σ, ∑ τ, cmw P (gammaLower σ) (gammaLower τ) (gamma τ) (gamma σ) =
    32 * pw (revF P) 𝟙 𝟙 := by
  simp only [cmw_eq_cpw, revM_gamma, revM_gammaLower, Finset.sum_neg_distrib]
  have h : ∀ σ τ : Fin 4, cpw (revF P) (-gamma σ) (-gamma τ) (-gammaLower τ) (-gammaLower σ) =
      cpw (revF P) (gamma σ) (gamma τ) (gammaLower τ) (gammaLower σ) := fun σ τ => by
    rw [cpw_neg_neg_03, cpw_neg_neg_12]
  simp only [h]
  have h1 : ∀ σ, ∑ τ, cpw (revF P) (gamma σ) (gamma τ) (gammaLower τ) (gammaLower σ) =
      ∑ τ, cpw (revF P) (gamma σ) (gammaLower τ) (gamma τ) (gammaLower σ) := fun σ =>
    sum_swap_gamma (fun A B => cpw (revF P) (gamma σ) A B (gammaLower σ))
      (fun c A B => cpw_smul_one _ _ _ _ _ c) (fun c A B => cpw_smul_two _ _ _ _ _ c)
  simp only [h1]
  rw [sum_swap_gamma (fun A B => ∑ τ, cpw (revF P) A (gammaLower τ) (gamma τ) B)
    (fun c A B => by simp only [cpw_smul_zero, Finset.mul_sum])
    (fun c A B => by simp only [cpw_smul_three, Finset.mul_sum]), sum_cpw_0312]
  ring

end Pairings

/-! ### The three coefficients of `C₋` -/

section Coeff

variable (P : Params) (z : Fin 8 → ℝ) (u : ℝ)

/-- **`T₁` of `C₋`**: `T₁ = -π⁴ κ η² U⁻² · 6 (-pp(P^R, H(Ē₃^R, Ē₂^R); Ē₁^R, Ē₀^R))`. -/
theorem classT1_Cm_eq : classT1 .Cm permCm P z u =
    ladderK P * ((symanzikU (classAlpha .Cm) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (6 * -pp (revF (ladderPauli P u))
        (hfam (revM (classE .Cm P z u 3)) (revM (classE .Cm P z u 2)))
        (revM (classE .Cm P z u 1)) (revM (classE .Cm P z u 0))) := by
  rw [classT1_eq_of_pat (isWeightPattern_Cm P), cmw_eq_cpw, cpw_eq_pp]

/-- **`T₂` of `C₋`** through the patterns `pp` and `pw` of the reversed matrices. -/
theorem classT2_Cm_eq : classT2 .Cm permCm P z u =
    ladderK P * ((symanzikU (classAlpha .Cm) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 1 *
          -(2 * pp (revF (ladderPauli P u))
            (hfam (revM (classE .Cm P z u 3)) (revM (classE .Cm P z u 2))) 𝟙 𝟙) +
        classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 2 *
          -(pp (revF (ladderPauli P u)) (hfam (revM (classE .Cm P z u 3)) 𝟙)
              (gamM (revM (classE .Cm P z u 1))) 𝟙 +
            2 * pp (revF (ladderPauli P u)) (hfam (revM (classE .Cm P z u 3)) 𝟙) 𝟙
              (revM (classE .Cm P z u 1)) +
            2 * pp (revF (ladderPauli P u))
              (hfam (revM (classE .Cm P z u 3)) (revM (classE .Cm P z u 1))) 𝟙 𝟙 +
            4 * pw (revF (ladderPauli P u)) 𝟙
              (revM (classE .Cm P z u 3) * gamM (revM (classE .Cm P z u 1)))) +
        classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 3 *
          -(pp (contractP (revF (ladderPauli P u))) (hfam 𝟙 (revM (classE .Cm P z u 2)))
              (revM (classE .Cm P z u 1)) 𝟙 +
            4 * pw (revF (ladderPauli P u))
              (gamM (revM (classE .Cm P z u 2)) * revM (classE .Cm P z u 1)) 𝟙 +
            2 * pw (contractP (revF (ladderPauli P u)))
              (revM (classE .Cm P z u 2) * gamM (revM (classE .Cm P z u 1))) 𝟙 +
            4 * pw (contractP (revF (ladderPauli P u))) (revM (classE .Cm P z u 2))
              (revM (classE .Cm P z u 1))) +
        classC .Cm (symanzikMatrix (classAlpha .Cm) z) 1 2 *
          -(2 * pp (revF (ladderPauli P u)) (hfam (revM (classE .Cm P z u 3)) 𝟙) 𝟙
            (revM (classE .Cm P z u 0))) +
        classC .Cm (symanzikMatrix (classAlpha .Cm) z) 1 3 *
          -pp (revF (ladderPauli P u)) (kfam (revM (classE .Cm P z u 2))) 𝟙
            (revM (classE .Cm P z u 0)) +
        classC .Cm (symanzikMatrix (classAlpha .Cm) z) 2 3 *
          -(4 * pp (revF (ladderPauli P u)) gammaLower (revM (classE .Cm P z u 1))
            (revM (classE .Cm P z u 0)))) := by
  rw [classT2_eq_of_pat (isWeightPattern_Cm P), sum_cmw_01, sum_cmw_02, sum_cmw_03, sum_cmw_12,
    sum_cmw_13, sum_cmw_23]

/-- **`T₃` of `C₋`** through `pw`. -/
theorem classT3_Cm_eq : classT3 .Cm permCm P z u =
    ladderK P * ((symanzikU (classAlpha .Cm) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (1 / 4 * (classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 1 *
          classC .Cm (symanzikMatrix (classAlpha .Cm) z) 2 3 *
            -(16 * pw (revF (ladderPauli P u)) 𝟙 𝟙) +
        classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 2 *
          classC .Cm (symanzikMatrix (classAlpha .Cm) z) 1 3 *
            (32 * pw (revF (ladderPauli P u)) 𝟙 𝟙) +
        classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 3 *
          classC .Cm (symanzikMatrix (classAlpha .Cm) z) 1 2 *
            (32 * pw (revF (ladderPauli P u)) 𝟙 𝟙))) := by
  rw [classT3_eq_of_pat (isWeightPattern_Cm P), sum_cmw_0123, sum_cmw_0213, sum_cmw_0312]

end Coeff

end QED.TwoLoop.UnitSCGraph

end
