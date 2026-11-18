/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCtTrace
import Mathlib.Tactic.Ring

/-!
# The Dirac traces of the `δ₂, δ_m` class on the outgoing line

The analogue of `QED/TwoLoop/UnitSCCtTrace.lean` for the class `kindsD2Out` (the counterterm on
the outgoing internal electron line). The Pauli projection of the class numerator is
`-c (Λ² - m_γ²) ∑_μ tr(ΓP_μ E_o C E_o γ^μ E_i)` (`sum_pauliWt_numD2Out`), a combination of the
chains `(E_o, N_c, E_o, E_i)` with the constant matrices `(ΓP_μ, 1, 1, γ^μ)`; the projected
numerator is `T₁ + T₂ V + T₃ V²` (`kindsNum_d2Out_eq_T`) with coefficients through base patterns
(`ctT1Out_planar`, `ctT2Out_planar`, `ctT3Out_planar`).
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.TwoLoop.UnitSCCt

open QED.Dirac QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.ParamNumEval QED.TwoLoop.UnitLGraph QED.TwoLoop.UnitLGraphTrace
open QED.TwoLoop.UnitSCGraph QED.TwoLoop.UnitLGraphTrace.Pl
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.TwoLoop (LoopQuartic castLoopMatrix symanzikV symanzikU symanzikMatrix
  lineMomentum loopShift)

/-- The identity matrix. -/
local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-! ### The chain form, outgoing class -/

/-- The constant matrices of the outgoing chain: `(ΓP_μ, 1, 1, γ^μ)`. -/
noncomputable def ctBOut (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![contractP (pauliMat m p' p) μ, 𝟙, 𝟙, gamma μ]

/-- The lines of the slots of the outgoing chain: outgoing, outgoing, outgoing, incoming. -/
def ctLinesOut : Fin 4 → Fin 8 := ![0, 0, 1, 2]

/-- The chain of the outgoing class with the mass `c` in the counterterm slot. -/
noncomputable def ctChainOut (P : Params) (p' : Fin 4 → ℝ) (μ : Fin 4) (c : ℝ) :
    (Fin 2 → Fin 4 → ℝ) → ℂ :=
  elecChain (ctAlpha kindsD2Out) (fun i => (kindsD2Out i).mom (restMomentum P.m) p')
    (ctBOut P.m p' (restMomentum P.m) μ) ![P.m, c, P.m, P.m] ctLinesOut

/-- **The projected class numerator as a combination of chains** (outgoing class). -/
theorem sum_pauliWt_numD2Out (P : Params) (p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∑ j : Idx, pauliWt P.m p' (restMomentum P.m) j.1 j.2.1 j.2.2 *
        numD2Out P p' (restMomentum P.m) j.1 (ℓ 0) j.2.1 j.2.2 =
      -(vcConst P.e * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) * ∑ μ,
        ((-((P.δ₂ : ℂ) + P.δm)) * ctChainOut P p' μ 0 ℓ +
          (P.δm : ℂ) * ctChainOut P p' μ P.m ℓ) := by
  simp only [Fintype.sum_prod_type, sum_pauliWt_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [numD2Out, trace_vertexChain_pv_mul]
  have hl0 : lineMomentum (ctAlpha kindsD2Out) (fun i => (kindsD2Out i).mom (restMomentum P.m) p')
      (ctLinesOut 0) ℓ = p' + ℓ 0 := by
    rw [lineMomentum_kinds]; rfl
  have hl1 : lineMomentum (ctAlpha kindsD2Out) (fun i => (kindsD2Out i).mom (restMomentum P.m) p')
      (ctLinesOut 1) ℓ = p' + ℓ 0 := by
    rw [lineMomentum_kinds]; rfl
  have hl2 : lineMomentum (ctAlpha kindsD2Out) (fun i => (kindsD2Out i).mom (restMomentum P.m) p')
      (ctLinesOut 2) ℓ = p' + ℓ 0 := by
    rw [lineMomentum_kinds]; rfl
  have hl3 : lineMomentum (ctAlpha kindsD2Out) (fun i => (kindsD2Out i).mom (restMomentum P.m) p')
      (ctLinesOut 3) ℓ = restMomentum P.m + ℓ 0 := by
    rw [lineMomentum_kinds]; rfl
  simp only [ctChainOut, elecChain, ch, ctBOut, hl0, hl1, hl2, hl3, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, Matrix.mul_one, fermionCtMatrix_eq_numerators, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_neg, smul_eq_mul, contractP]
  simp only [Matrix.mul_assoc]
  ring

/-! ### The three coefficients, outgoing class -/

/-- The electron numerators of the outgoing chain at the shifted loop momenta. -/
noncomputable def ctEOut (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (c : ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  elecAt (ctAlpha kindsD2Out) (ctMom kindsD2Out P u) ![P.m, c, P.m, P.m] ctLinesOut
    (-loopShift (ctAlpha kindsD2Out) (ctMom kindsD2Out P u) z)

/-- `T₁` of the outgoing class. -/
noncomputable def ctT1Out (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : ℂ :=
  ∑ k : Fin 4 × Fin 2, ctK P * ctCf P k.2 *
    (((symanzikU (ctAlpha kindsD2Out) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (6 * ch (ctBOut P.m (curveMomentum P.m u) (restMomentum P.m) k.1)
        (ctEOut P z u (ctCm P k.2) 0) (ctEOut P z u (ctCm P k.2) 1)
        (ctEOut P z u (ctCm P k.2) 2) (ctEOut P z u (ctCm P k.2) 3)))

/-- `T₂` of the outgoing class. -/
noncomputable def ctT2Out (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : ℂ :=
  ∑ k : Fin 4 × Fin 2, ctK P * ctCf P k.2 *
    (((symanzikU (ctAlpha kindsD2Out) z ^ 2 : ℝ) : ℂ)⁻¹ *
      chainTwo (ctAlpha kindsD2Out) (ctBOut P.m (curveMomentum P.m u) (restMomentum P.m) k.1)
        (ctEOut P z u (ctCm P k.2)) ctLinesOut (symanzikMatrix (ctAlpha kindsD2Out) z))

/-- `T₃` of the outgoing class. -/
noncomputable def ctT3Out (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : ℂ :=
  ∑ k : Fin 4 × Fin 2, ctK P * ctCf P k.2 *
    (((symanzikU (ctAlpha kindsD2Out) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (1 / 4 * chainFour (ctAlpha kindsD2Out)
        (ctBOut P.m (curveMomentum P.m u) (restMomentum P.m) k.1) ctLinesOut
        (symanzikMatrix (ctAlpha kindsD2Out) z)))

/-- **The projected numerator of the outgoing class is `T₁ + T₂ V + T₃ V²`.** -/
theorem kindsNum_d2Out_eq_T (P : Params) (x : Fin 7 → ℝ) (u : ℝ) :
    kindsNum kindsD2Out (massesD2In P) P (fun p' μ k => numD2Out P p' (restMomentum P.m) μ k) x u =
      ctT1Out P (simplexPoint x) u + ctT2Out P (simplexPoint x) u *
          ((symanzikV (ctAlpha kindsD2Out) (ctMom kindsD2Out P u) (massesD2In P)
            (simplexPoint x) : ℝ) : ℂ) +
        ctT3Out P (simplexPoint x) u *
          ((symanzikV (ctAlpha kindsD2Out) (ctMom kindsD2Out P u) (massesD2In P)
            (simplexPoint x) : ℝ) : ℂ) ^ 2 := by
  have hq : ∀ j : Idx, ∃ Q : LoopQuartic,
      Q.eval = fun ℓ => numD2Out P (curveMomentum P.m u) (restMomentum P.m) j.1 (ℓ 0) j.2.1 j.2.2 :=
    fun j => (isLoopPoly_numD2Out P (curveMomentum P.m u) _ j.1 j.2.1 j.2.2).exists_loopQuartic
  have h1 : kindsNum kindsD2Out (massesD2In P) P
      (fun p' μ k => numD2Out P p' (restMomentum P.m) μ k) x u =
      -((π : ℂ) ^ 4) * paramNumOf (fun ℓ => ∑ j : Idx,
        pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
          numD2Out P (curveMomentum P.m u) (restMomentum P.m) j.1 (ℓ 0) j.2.1 j.2.2)
        (ctAlpha kindsD2Out) (ctMom kindsD2Out P u) (massesD2In P) x := by
    rw [paramNumOf_sum _ _ _ _ _ _ hq, kindsNum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : (fun ℓ => ∑ j : Idx,
      pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
        numD2Out P (curveMomentum P.m u) (restMomentum P.m) j.1 (ℓ 0) j.2.1 j.2.2) =
      fun ℓ => ∑ k : Fin 4 × Fin 2,
        (-(vcConst P.e * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) * ctCf P k.2) *
          ctChainOut P (curveMomentum P.m u) k.1 (ctCm P k.2) ℓ := by
    funext ℓ
    rw [sum_pauliWt_numD2Out, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [Fin.sum_univ_two, ctCf, ctCm, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [h1, h2, paramNumOf_sum _ _ _ _ _ _
    (F := fun k : Fin 4 × Fin 2 => ctChainOut P (curveMomentum P.m u) k.1 (ctCm P k.2))
    (fun k => exists_quartic_elecChain _ _ _ _ _)]
  simp only [ctChainOut, paramNumOf_elecChain]
  norm_num [Nat.factorial]
  simp only [ctT1Out, ctT2Out, ctT3Out, ctEOut, Finset.mul_sum, Finset.sum_mul, ←
    Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ctK]
  push_cast
  ring

/-! ### The contraction patterns of the outgoing chain -/

section SlotsOut

variable (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ)

/-- The chain sum of the outgoing class: `∑_μ tr(P_μ Y₀ Y₁ Y₂ γ^μ Y₃) = pw(P; Y₀ Y₁ Y₂, Y₃)`. -/
theorem sum_ch_ctBOut (m : ℝ) (p' p : Fin 4 → ℝ) :
    ∑ μ, ch (ctBOut m p' p μ) Y₀ Y₁ Y₂ Y₃ = pw (contractP (pauliMat m p' p)) (Y₀ * Y₁ * Y₂) Y₃ := by
  unfold ch ctBOut pw
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.mul_one, Matrix.mul_assoc]

theorem out01 : ∑ σ, pw P (gammaLower σ * gamma σ * Y₂) Y₃ = -4 * pw P Y₂ Y₃ := by
  rw [pw_sum_left, ← Finset.sum_mul, sum_gammaLower_mul_gamma, Matrix.smul_mul, Matrix.one_mul,
    pw_smul_left]

theorem out02 : ∑ σ, pw P (gammaLower σ * Y₁ * gamma σ) Y₃ = pw P (gamM Y₁) Y₃ := by
  rw [pw_sum_left, sum_gammaLower_swap]

theorem out03 : ∑ σ, pw P (gammaLower σ * Y₁ * Y₂) (gamma σ) =
    pw (contractP P) (Y₁ * Y₂) 𝟙 := by
  unfold pw
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [show contractP P μ = ∑ σ, gamma σ * P μ * gammaLower σ from rfl, Matrix.mul_one]
  simp only [Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [show P μ * (gammaLower σ * Y₁ * Y₂) * gamma μ * gamma σ =
      (P μ * (gammaLower σ * Y₁ * Y₂) * gamma μ) * gamma σ by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem out12 : ∑ σ, pw P (Y₀ * gammaLower σ * gamma σ) Y₃ = -4 * pw P Y₀ Y₃ := by
  have e : ∀ σ, Y₀ * gammaLower σ * gamma σ = Y₀ * (gammaLower σ * gamma σ) := fun σ => by
    rw [Matrix.mul_assoc]
  simp only [e]
  rw [pw_sum_left, ← Matrix.mul_sum, sum_gammaLower_mul_gamma, Matrix.mul_smul, Matrix.mul_one,
    pw_smul_left]

theorem out13 : ∑ σ, pw P (Y₀ * gammaLower σ * Y₂) (gamma σ) =
    pw (contractP (mulRightP P Y₀)) Y₂ 𝟙 := by
  unfold pw
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [show contractP (mulRightP P Y₀) μ = ∑ σ, gamma σ * (P μ * Y₀) * gammaLower σ from rfl,
    Matrix.mul_one]
  simp only [Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [show P μ * (Y₀ * gammaLower σ * Y₂) * gamma μ * gamma σ =
      (P μ * (Y₀ * gammaLower σ * Y₂) * gamma μ) * gamma σ by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem out23 : ∑ σ, pw P (Y₀ * Y₁ * gammaLower σ) (gamma σ) = 2 * pw P (Y₀ * Y₁) 𝟙 := by
  have h := sum_pw_gammaLower_gamma P (Y₀ * Y₁) 𝟙
  simp only [Matrix.mul_one] at h
  exact h

theorem out0123 : ∑ σ, ∑ τ, pw P (gammaLower σ * gamma σ * gammaLower τ) (gamma τ) =
    -8 * pw P 𝟙 𝟙 := by
  rw [Finset.sum_comm]
  have e : ∀ τ, ∑ σ, pw P (gammaLower σ * gamma σ * gammaLower τ) (gamma τ) =
      -4 * pw P (gammaLower τ) (gamma τ) := fun τ => by
    rw [pw_sum_left, ← Finset.sum_mul, sum_gammaLower_mul_gamma, Matrix.smul_mul,
      Matrix.one_mul, pw_smul_left]
  simp only [e, ← Finset.mul_sum, sum_pw_gammaLower_gamma']
  ring

theorem out0213 : ∑ σ, ∑ τ, pw P (gammaLower σ * gammaLower τ * gamma σ) (gamma τ) =
    4 * pw P 𝟙 𝟙 := by
  rw [Finset.sum_comm]
  have e : ∀ τ, ∑ σ, pw P (gammaLower σ * gammaLower τ * gamma σ) (gamma τ) =
      2 * pw P (gammaLower τ) (gamma τ) := fun τ => by
    rw [pw_sum_left, sum_gammaLower_gammaLower_gamma, pw_smul_left]
  simp only [e, ← Finset.mul_sum, sum_pw_gammaLower_gamma']
  ring

theorem out0312 : ∑ σ, ∑ τ, pw P (gammaLower σ * gammaLower τ * gamma τ) (gamma σ) =
    -8 * pw P 𝟙 𝟙 := by
  have e : ∀ σ, ∑ τ, pw P (gammaLower σ * gammaLower τ * gamma τ) (gamma σ) =
      -4 * pw P (gammaLower σ) (gamma σ) := fun σ => by
    have e' : ∀ τ, gammaLower σ * gammaLower τ * gamma τ = gammaLower σ * (gammaLower τ * gamma τ) :=
      fun τ => by rw [Matrix.mul_assoc]
    simp only [e']
    rw [pw_sum_left, ← Matrix.mul_sum, sum_gammaLower_mul_gamma, Matrix.mul_smul, Matrix.mul_one,
      pw_smul_left]
  simp only [e, ← Finset.mul_sum, sum_pw_gammaLower_gamma']
  ring

end SlotsOut

/-! ### The coefficients of the outgoing class through base patterns -/

theorem contrC_ctLinesOut (A : Matrix (Fin 2) (Fin 2) ℝ) (k l : Fin 4) :
    contrC (ctAlpha kindsD2Out) A (ctLinesOut k) (ctLinesOut l) = A⁻¹ 0 0 := by
  fin_cases k <;> fin_cases l <;>
    simp [contrC, castLoopMatrix, kindsD2Out, LineKind.dir, ctLinesOut, Fin.sum_univ_two]

section CoeffOut

variable (m : ℝ) (p' p : Fin 4 → ℝ) (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
  (A : Matrix (Fin 2) (Fin 2) ℝ)

theorem sum_chainTwo_ctBOut :
    ∑ μ, chainTwo (ctAlpha kindsD2Out) (ctBOut m p' p μ) E ctLinesOut A =
      ((A⁻¹ 0 0 : ℝ) : ℂ) * (-4 * pw (contractP (pauliMat m p' p)) (E 2) (E 3) +
        pw (contractP (pauliMat m p' p)) (gamM (E 1)) (E 3) +
        pw (contractP (contractP (pauliMat m p' p))) (E 1 * E 2) 𝟙 +
        -4 * pw (contractP (pauliMat m p' p)) (E 0) (E 3) +
        pw (contractP (mulRightP (contractP (pauliMat m p' p)) (E 0))) (E 2) 𝟙 +
        2 * pw (contractP (pauliMat m p' p)) (E 0 * E 1) 𝟙) := by
  set Q := contractP (pauliMat m p' p)
  have h01 : ∑ μ, ∑ ν, ch (ctBOut m p' p μ) (gammaLower ν) (gamma ν) (E 2) (E 3) =
      -4 * pw Q (E 2) (E 3) := by
    rw [Finset.sum_comm]; simp only [sum_ch_ctBOut]; exact out01 _ _ _
  have h02 : ∑ μ, ∑ ν, ch (ctBOut m p' p μ) (gammaLower ν) (E 1) (gamma ν) (E 3) =
      pw Q (gamM (E 1)) (E 3) := by
    rw [Finset.sum_comm]; simp only [sum_ch_ctBOut]; exact out02 _ _ _
  have h03 : ∑ μ, ∑ ν, ch (ctBOut m p' p μ) (gammaLower ν) (E 1) (E 2) (gamma ν) =
      pw (contractP Q) (E 1 * E 2) 𝟙 := by
    rw [Finset.sum_comm]; simp only [sum_ch_ctBOut]; exact out03 _ _ _
  have h12 : ∑ μ, ∑ ν, ch (ctBOut m p' p μ) (E 0) (gammaLower ν) (gamma ν) (E 3) =
      -4 * pw Q (E 0) (E 3) := by
    rw [Finset.sum_comm]; simp only [sum_ch_ctBOut]; exact out12 _ _ _
  have h13 : ∑ μ, ∑ ν, ch (ctBOut m p' p μ) (E 0) (gammaLower ν) (E 2) (gamma ν) =
      pw (contractP (mulRightP Q (E 0))) (E 2) 𝟙 := by
    rw [Finset.sum_comm]; simp only [sum_ch_ctBOut]; exact out13 _ _ _
  have h23 : ∑ μ, ∑ ν, ch (ctBOut m p' p μ) (E 0) (E 1) (gammaLower ν) (gamma ν) =
      2 * pw Q (E 0 * E 1) 𝟙 := by
    rw [Finset.sum_comm]; simp only [sum_ch_ctBOut]; exact out23 _ _ _
  simp only [chainTwo, contrC_ctLinesOut, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h01, h02, h03, h12, h13, h23]
  ring

theorem sum_chainFour_ctBOut :
    ∑ μ, chainFour (ctAlpha kindsD2Out) (ctBOut m p' p μ) ctLinesOut A =
      ((A⁻¹ 0 0 : ℝ) : ℂ) ^ 2 * (-12 * pw (contractP (pauliMat m p' p)) 𝟙 𝟙) := by
  set Q := contractP (pauliMat m p' p)
  have h1 : ∑ μ, ∑ ν, ∑ ρ, ch (ctBOut m p' p μ) (gammaLower ν) (gamma ν) (gammaLower ρ)
      (gamma ρ) = -8 * pw Q 𝟙 𝟙 := by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun ν _ => Finset.sum_comm]
    simp only [sum_ch_ctBOut]
    exact out0123 _
  have h2 : ∑ μ, ∑ ν, ∑ ρ, ch (ctBOut m p' p μ) (gammaLower ν) (gammaLower ρ) (gamma ν)
      (gamma ρ) = 4 * pw Q 𝟙 𝟙 := by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun ν _ => Finset.sum_comm]
    simp only [sum_ch_ctBOut]
    exact out0213 _
  have h3 : ∑ μ, ∑ ν, ∑ ρ, ch (ctBOut m p' p μ) (gammaLower ν) (gammaLower ρ) (gamma ρ)
      (gamma ν) = -8 * pw Q 𝟙 𝟙 := by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun ν _ => Finset.sum_comm]
    simp only [sum_ch_ctBOut]
    exact out0312 _
  simp only [chainFour, contrC_ctLinesOut, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1, h2, h3]
  ring

end CoeffOut

/-! ### The loop shift and the slot momenta, outgoing class -/

/-- The outgoing-electron share `ζ = (z₀ + z₁)/X₁` of the outgoing class. -/
noncomputable def ctZetaOut (z : Fin 8 → ℝ) : ℝ := (z 0 + z 1) / ctX1 z

/-- The incoming-electron share `σ = z₂/X₁` of the outgoing class. -/
noncomputable def ctSigOut (z : Fin 8 → ℝ) : ℝ := z 2 / ctX1 z

/-- **The loop shift of the outgoing class**: `S₀ = ζ p' + σ p`. -/
theorem loopShift_d2Out (P : Params) (u : ℝ) {z : Fin 8 → ℝ} (hX1 : ctX1 z ≠ 0)
    (hX2 : ctX2 z ≠ 0) (μ : Fin 4) :
    loopShift (ctAlpha kindsD2Out) (ctMom kindsD2Out P u) z 0 μ =
      ctZetaOut z * curveMomentum P.m u μ + ctSigOut z * restMomentum P.m μ := by
  rw [QED.TwoLoop.LimitCovariance.loopShift_apply]
  simp only [Fin.sum_univ_two, inv_symanzikMatrix_kinds kindsD2Out (Or.inr rfl)]
  simp [Fin.sum_univ_eight, castLoopMatrix, kindsD2Out, LineKind.dir, LineKind.mom, ctZetaOut,
    ctSigOut, ctMom]
  simp only [ctX1, ctX2] at hX1 hX2 ⊢
  field_simp

/-- The outgoing slot momentum `p' - S₀ = -σ p + (1 - ζ) p'` of the outgoing class. -/
noncomputable def ctQoOut (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : Fin 4 → ℝ :=
  fun μ => -ctSigOut z * restMomentum P.m μ + (1 - ctZetaOut z) * curveMomentum P.m u μ

/-- The incoming slot momentum `p - S₀ = (1 - σ) p - ζ p'` of the outgoing class. -/
noncomputable def ctQiOut (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : Fin 4 → ℝ :=
  fun μ => (1 - ctSigOut z) * restMomentum P.m μ + -ctZetaOut z * curveMomentum P.m u μ

/-- **The slot numerators of the outgoing class.** -/
theorem ctEOut_eq (P : Params) {z : Fin 8 → ℝ} (hX1 : ctX1 z ≠ 0) (hX2 : ctX2 z ≠ 0)
    (u c : ℝ) :
    ctEOut P z u c = ![electronNumerator P.m (ctQoOut P z u), electronNumerator c (ctQoOut P z u),
      electronNumerator P.m (ctQoOut P z u), electronNumerator P.m (ctQiOut P z u)] := by
  have hS := loopShift_d2Out P u hX1 hX2
  funext k
  simp only [ctEOut, elecAt, lineMomentum_kinds]
  generalize loopShift (ctAlpha kindsD2Out) (ctMom kindsD2Out P u) z = L at hS ⊢
  fin_cases k <;>
  · congr 1
    funext μ
    simp [ctLinesOut, kindsD2Out, LineKind.lineMom, ctQoOut, ctQiOut, hS]
    ring

/-! ### The planar form of the coefficients, outgoing class -/

theorem ctQoOut_two (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : ctQoOut P z u 2 = 0 := by
  simp [ctQoOut, restMomentum_two, curveMomentum_two]

theorem ctQoOut_three (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : ctQoOut P z u 3 = 0 := by
  simp [ctQoOut, restMomentum_three, curveMomentum_three]

theorem ctQiOut_two (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : ctQiOut P z u 2 = 0 := by
  simp [ctQiOut, restMomentum_two, curveMomentum_two]

theorem ctQiOut_three (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : ctQiOut P z u 3 = 0 := by
  simp [ctQiOut, restMomentum_three, curveMomentum_three]

/-- The planar slot numerators of the outgoing class. -/
noncomputable abbrev eoOut (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : Pl := ePl P.m (ctQoOut P z u)
/-- The planar slot numerators of the outgoing class. -/
noncomputable abbrev eiOut (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : Pl := ePl P.m (ctQiOut P z u)
/-- The planar slot numerators of the outgoing class. -/
noncomputable abbrev ecOut (P : Params) (z : Fin 8 → ℝ) (u c : ℝ) : Pl := ePl c (ctQoOut P z u)

theorem ctEOut_planar (P : Params) {z : Fin 8 → ℝ} (hX1 : ctX1 z ≠ 0) (hX2 : ctX2 z ≠ 0)
    (u c : ℝ) :
    ctEOut P z u c = ![toMat (eoOut P z u), toMat (ecOut P z u c), toMat (eoOut P z u),
      toMat (eiOut P z u)] := by
  rw [ctEOut_eq P hX1 hX2, electronNumerator_ePl P.m (ctQoOut_two P z u) (ctQoOut_three P z u),
    electronNumerator_ePl P.m (ctQiOut_two P z u) (ctQiOut_three P z u),
    electronNumerator_ePl c (ctQoOut_two P z u) (ctQoOut_three P z u)]

/-- **`T₁` of the outgoing class as a planar expression.** -/
theorem ctT1Out_planar (P : Params) {z : Fin 8 → ℝ} (hX1 : ctX1 z ≠ 0) (hX2 : ctX2 z ≠ 0)
    (u : ℝ) :
    ctT1Out P z u = ∑ c : Fin 2, ctK P * ctCf P c *
      (((symanzikU (ctAlpha kindsD2Out) z ^ 2 : ℝ) : ℂ)⁻¹ *
        (6 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u))
          (eoOut P z u * ecOut P z u (ctCm P c) * eoOut P z u) (eiOut P z u))) := by
  have hP1 := planarPauli_contractP (planarPauli_ladder P u)
  unfold ctT1Out
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [← Finset.mul_sum, sum_ch_ctBOut, ctEOut_planar P hX1 hX2, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, toMat_mul]
  rw [pw_planar hP1]

/-- **`T₂` of the outgoing class as a planar expression.** -/
theorem ctT2Out_planar (P : Params) {z : Fin 8 → ℝ} (hX1 : ctX1 z ≠ 0) (hX2 : ctX2 z ≠ 0)
    (u : ℝ) :
    ctT2Out P z u = ∑ c : Fin 2, ctK P * ctCf P c *
      (((symanzikU (ctAlpha kindsD2Out) z ^ 2 : ℝ) : ℂ)⁻¹ *
        ((((symanzikMatrix (ctAlpha kindsD2Out) z)⁻¹ 0 0 : ℝ) : ℂ) *
          (-4 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) (eoOut P z u)
              (eiOut P z u) +
            pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u))
              (gam (ecOut P z u (ctCm P c))) (eiOut P z u) +
            pwPl (gam (gam (lQ0 P u))) (gam (gam (lQ1 P u))) (gamT (gamT (lR P u)))
              (ecOut P z u (ctCm P c) * eoOut P z u) 1 +
            -4 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) (eoOut P z u)
              (eiOut P z u) +
            pwPl (gam (gam (lQ0 P u) * eoOut P z u)) (gam (gam (lQ1 P u) * eoOut P z u))
              (gamT (gamT (lR P u) * bar (eoOut P z u))) (eoOut P z u) 1 +
            2 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u))
              (eoOut P z u * ecOut P z u (ctCm P c)) 1))) := by
  have hP1 := planarPauli_contractP (planarPauli_ladder P u)
  have hP2 := planarPauli_contractP hP1
  have hP3 := planarPauli_contractP (planarPauli_mulRightP hP1 (eoOut P z u))
  unfold ctT2Out
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [← Finset.mul_sum, sum_chainTwo_ctBOut, ctEOut_planar P hX1 hX2,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, toMat_mul, gamM_toMat']
  rw [← toMat_one]
  simp only [pw_planar hP1, pw_planar hP2, pw_planar hP3]

/-- **`T₃` of the outgoing class as a planar expression.** -/
theorem ctT3Out_planar (P : Params) (z : Fin 8 → ℝ) (u : ℝ) :
    ctT3Out P z u = ∑ c : Fin 2, ctK P * ctCf P c *
      (((symanzikU (ctAlpha kindsD2Out) z ^ 2 : ℝ) : ℂ)⁻¹ *
        (1 / 4 * ((((symanzikMatrix (ctAlpha kindsD2Out) z)⁻¹ 0 0 : ℝ) : ℂ) ^ 2 *
          (-12 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) 1 1)))) := by
  have hP1 := planarPauli_contractP (planarPauli_ladder P u)
  unfold ctT3Out
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [← Finset.mul_sum, sum_chainFour_ctBOut]
  rw [← toMat_one, pw_planar hP1]

end QED.TwoLoop.UnitSCCt

end
