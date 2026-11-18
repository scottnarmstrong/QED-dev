/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCGraphSpTrace
public import QED.TwoLoop.PauliZeroExplicitCt
public import QED.TwoLoop.UnitSCCtIntegral
import Mathlib.Tactic.Ring

/-!
# The Dirac traces of the `δ₂, δ_m` counterterm classes

Section 5.2 of `docs/TWO-LOOP-UNITS.md`, the `δ₂, δ_m` half of the unit `S`, trace stage. The
projected parametric numerator of the product data of the `δ₂, δ_m` class on the incoming line
(`QED.TwoLoop.PauliZeroExplicit.kindsNum`) is reduced to the base pattern
`pw(P; W, Z) = ∑_μ tr(P_μ W γ^μ Z)` of `QED/TwoLoop/UnitSCGraphPauli.lean`:

* `sum_pauliWt_numD2In`: the Pauli projection of the class numerator is
  `-c (Λ² - m_γ²) ∑_μ tr(ΓP_μ E_o γ^μ E_i C E_i)`, `c = (ie)³(1/i)³(2π)⁻⁴`, with `ΓP` the contracted
  Pauli family, and the counterterm matrix `C = δ₂ k̸ + δ_m m = a₀ N₀(k) + a₁ N_m(k)`,
  `a₀ = -(δ₂ + δ_m)`, `a₁ = δ_m`, a combination of electron numerators; hence a combination of
  chains of four electron numerators (`ctChainIn`);
* `kindsNum_d2In_eq_T`: the projected numerator is `T₁ + T₂ V + T₃ V²` (Wick's rule,
  `QED.TwoLoop.ParamNumEval.paramNumOf_elecChain`);
* `ctT1In_eq`, `ctT2In_eq`, `ctT3In_eq`: the coefficients through base patterns, all contraction
  coefficients being `1/X₁`.
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

/-! ### The Pauli projection of the vertex chain -/

/-- The vertex-chain constant `(ie)³ (1/i)³ (2π)⁻⁴`. -/
noncomputable def vcConst (e : ℝ) : ℂ :=
  (I * e) ^ 3 * (1 / I) ^ 3 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹

/-- **The Pauli projection of a vertex chain with the Pauli–Villars photon**:
`tr(V^μ P) = c (Λ² - m_γ²) tr(ΓP Sout γ^μ Sin)`, `ΓP = ∑_ν γ^ν P γ_ν`. -/
theorem trace_vertexChain_pv_mul (e : ℝ) (μ : Fin 4) (Sout Sin Pm : Matrix (Fin 4) (Fin 4) ℂ)
    (mγ Λ : ℝ) :
    trace (vertexChain e μ Sout Sin (pvPhotonNum mγ Λ) * Pm) =
      vcConst e * ((Λ ^ 2 - mγ ^ 2 : ℝ) : ℂ) *
        trace ((∑ ν, gamma ν * Pm * gammaLower ν) * Sout * gamma μ * Sin) := by
  unfold vertexChain
  rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.sum_mul, Matrix.trace_sum, smul_eq_mul]
  have hR : trace ((∑ ν, gamma ν * Pm * gammaLower ν) * Sout * gamma μ * Sin) =
      ∑ ν, trace (gamma ν * Pm * gammaLower ν * Sout * gamma μ * Sin) := by
    simp only [Matrix.sum_mul, Matrix.trace_sum]
  rw [hR, vcConst, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Matrix.sum_mul, Matrix.trace_sum, Finset.sum_eq_single ν
    (fun ρ _ hρ => by simp [pvPhotonNum, Minkowski.metric, Ne.symm hρ]) (by simp)]
  rw [gammaLower_eq_metric_smul]
  simp only [pvPhotonNum, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  have hc : trace (gamma ν * Sout * gamma μ * Sin * gamma ν * Pm) =
      trace (gamma ν * Pm * gamma ν * Sout * gamma μ * Sin) := by
    rw [show gamma ν * Sout * gamma μ * Sin * gamma ν * Pm =
        (gamma ν * Sout * gamma μ * Sin) * (gamma ν * Pm) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [hc]
  push_cast
  ring

/-! ### The chain form, incoming class -/

/-- The loop matrix of the product data. -/
noncomputable abbrev ctAlpha (κ : Fin 8 → LineKind) : Fin 8 → Fin 2 → ℝ :=
  castLoopMatrix fun i => (κ i).dir

/-- The external momenta of the product data along the curve. -/
noncomputable abbrev ctMom (κ : Fin 8 → LineKind) (P : Params) (u : ℝ) : Fin 8 → Fin 4 → ℝ :=
  fun i => (κ i).mom (restMomentum P.m) (curveMomentum P.m u)

/-- The constant matrices of the incoming chain: `(ΓP_μ, γ^μ, 1, 1)`. -/
noncomputable def ctBIn (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![contractP (pauliMat m p' p) μ, gamma μ, 𝟙, 𝟙]

/-- The lines of the slots of the incoming chain: outgoing, incoming, incoming, incoming. -/
def ctLinesIn : Fin 4 → Fin 8 := ![0, 1, 1, 2]

/-- The chain of the incoming class with the mass `c` in the counterterm slot. -/
noncomputable def ctChainIn (P : Params) (p' : Fin 4 → ℝ) (μ : Fin 4) (c : ℝ) :
    (Fin 2 → Fin 4 → ℝ) → ℂ :=
  elecChain (ctAlpha kindsD2In) (fun i => (kindsD2In i).mom (restMomentum P.m) p')
    (ctBIn P.m p' (restMomentum P.m) μ) ![P.m, P.m, c, P.m] ctLinesIn

/-- The counterterm matrix as electron numerators:
`δ₂ k̸ + δ_m m = -(δ₂ + δ_m) N₀(k) + δ_m N_m(k)`. -/
theorem fermionCtMatrix_eq_numerators (δ₂ δm m : ℝ) (k : Fin 4 → ℝ) :
    fermionCtMatrix δ₂ δm m k =
      (-((δ₂ : ℂ) + δm)) • electronNumerator 0 k + (δm : ℂ) • electronNumerator m k := by
  simp only [fermionCtMatrix, electronNumerator]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  push_cast
  ring

/-- **The projected class numerator as a combination of chains** (incoming class). -/
theorem sum_pauliWt_numD2In (P : Params) (p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∑ j : Idx, pauliWt P.m p' (restMomentum P.m) j.1 j.2.1 j.2.2 *
        numD2In P p' (restMomentum P.m) j.1 (ℓ 0) j.2.1 j.2.2 =
      -(vcConst P.e * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) * ∑ μ,
        ((-((P.δ₂ : ℂ) + P.δm)) * ctChainIn P p' μ 0 ℓ + (P.δm : ℂ) * ctChainIn P p' μ P.m ℓ) := by
  simp only [Fintype.sum_prod_type, sum_pauliWt_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [numD2In, trace_vertexChain_pv_mul]
  have hl0 : lineMomentum (ctAlpha kindsD2In) (fun i => (kindsD2In i).mom (restMomentum P.m) p')
      (ctLinesIn 0) ℓ = p' + ℓ 0 := by
    rw [lineMomentum_kinds]; rfl
  have hl1 : lineMomentum (ctAlpha kindsD2In) (fun i => (kindsD2In i).mom (restMomentum P.m) p')
      (ctLinesIn 1) ℓ = restMomentum P.m + ℓ 0 := by
    rw [lineMomentum_kinds]; rfl
  have hl2 : lineMomentum (ctAlpha kindsD2In) (fun i => (kindsD2In i).mom (restMomentum P.m) p')
      (ctLinesIn 2) ℓ = restMomentum P.m + ℓ 0 := by
    rw [lineMomentum_kinds]; rfl
  have hl3 : lineMomentum (ctAlpha kindsD2In) (fun i => (kindsD2In i).mom (restMomentum P.m) p')
      (ctLinesIn 3) ℓ = restMomentum P.m + ℓ 0 := by
    rw [lineMomentum_kinds]; rfl
  simp only [ctChainIn, elecChain, ch, ctBIn, hl0, hl1, hl2, hl3, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, Matrix.mul_one, fermionCtMatrix_eq_numerators, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_neg, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_neg, smul_eq_mul, contractP]
  simp only [Matrix.mul_assoc]
  ring

/-! ### The three coefficients, incoming class -/

/-- The coefficients `(a₀, a₁) = (-(δ₂ + δ_m), δ_m)` of the counterterm matrix. -/
noncomputable def ctCf (P : Params) : Fin 2 → ℂ := ![-((P.δ₂ : ℂ) + P.δm), (P.δm : ℂ)]

/-- The masses `(0, m)` of the counterterm slot. -/
noncomputable def ctCm (P : Params) : Fin 2 → ℝ := ![0, P.m]

/-- The overall constant `π⁴ c (Λ² - m_γ²)`. -/
noncomputable def ctK (P : Params) : ℂ :=
  (π : ℂ) ^ 4 * (vcConst P.e * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ))

/-- The electron numerators of the incoming chain at the shifted loop momenta. -/
noncomputable def ctEIn (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (c : ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  elecAt (ctAlpha kindsD2In) (ctMom kindsD2In P u) ![P.m, P.m, c, P.m] ctLinesIn
    (-loopShift (ctAlpha kindsD2In) (ctMom kindsD2In P u) z)

/-- `T₁` of the incoming class. -/
noncomputable def ctT1In (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : ℂ :=
  ∑ k : Fin 4 × Fin 2, ctK P * ctCf P k.2 *
    (((symanzikU (ctAlpha kindsD2In) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (6 * ch (ctBIn P.m (curveMomentum P.m u) (restMomentum P.m) k.1)
        (ctEIn P z u (ctCm P k.2) 0) (ctEIn P z u (ctCm P k.2) 1) (ctEIn P z u (ctCm P k.2) 2)
        (ctEIn P z u (ctCm P k.2) 3)))

/-- `T₂` of the incoming class. -/
noncomputable def ctT2In (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : ℂ :=
  ∑ k : Fin 4 × Fin 2, ctK P * ctCf P k.2 *
    (((symanzikU (ctAlpha kindsD2In) z ^ 2 : ℝ) : ℂ)⁻¹ *
      chainTwo (ctAlpha kindsD2In) (ctBIn P.m (curveMomentum P.m u) (restMomentum P.m) k.1)
        (ctEIn P z u (ctCm P k.2)) ctLinesIn (symanzikMatrix (ctAlpha kindsD2In) z))

/-- `T₃` of the incoming class. -/
noncomputable def ctT3In (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : ℂ :=
  ∑ k : Fin 4 × Fin 2, ctK P * ctCf P k.2 *
    (((symanzikU (ctAlpha kindsD2In) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (1 / 4 * chainFour (ctAlpha kindsD2In)
        (ctBIn P.m (curveMomentum P.m u) (restMomentum P.m) k.1) ctLinesIn
        (symanzikMatrix (ctAlpha kindsD2In) z)))

/-- **The projected numerator of the incoming class is `T₁ + T₂ V + T₃ V²`.** -/
theorem kindsNum_d2In_eq_T (P : Params) (x : Fin 7 → ℝ) (u : ℝ) :
    kindsNum kindsD2In (massesD2In P) P (fun p' μ k => numD2In P p' (restMomentum P.m) μ k) x u =
      ctT1In P (simplexPoint x) u + ctT2In P (simplexPoint x) u *
          ((symanzikV (ctAlpha kindsD2In) (ctMom kindsD2In P u) (massesD2In P)
            (simplexPoint x) : ℝ) : ℂ) +
        ctT3In P (simplexPoint x) u *
          ((symanzikV (ctAlpha kindsD2In) (ctMom kindsD2In P u) (massesD2In P)
            (simplexPoint x) : ℝ) : ℂ) ^ 2 := by
  have hq : ∀ j : Idx, ∃ Q : LoopQuartic,
      Q.eval = fun ℓ => numD2In P (curveMomentum P.m u) (restMomentum P.m) j.1 (ℓ 0) j.2.1 j.2.2 :=
    fun j => (isLoopPoly_numD2In P (curveMomentum P.m u) _ j.1 j.2.1 j.2.2).exists_loopQuartic
  have h1 : kindsNum kindsD2In (massesD2In P) P
      (fun p' μ k => numD2In P p' (restMomentum P.m) μ k) x u =
      -((π : ℂ) ^ 4) * paramNumOf (fun ℓ => ∑ j : Idx,
        pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
          numD2In P (curveMomentum P.m u) (restMomentum P.m) j.1 (ℓ 0) j.2.1 j.2.2)
        (ctAlpha kindsD2In) (ctMom kindsD2In P u) (massesD2In P) x := by
    rw [paramNumOf_sum _ _ _ _ _ _ hq, kindsNum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : (fun ℓ => ∑ j : Idx, pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
      numD2In P (curveMomentum P.m u) (restMomentum P.m) j.1 (ℓ 0) j.2.1 j.2.2) =
      fun ℓ => ∑ k : Fin 4 × Fin 2,
        (-(vcConst P.e * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) * ctCf P k.2) *
          ctChainIn P (curveMomentum P.m u) k.1 (ctCm P k.2) ℓ := by
    funext ℓ
    rw [sum_pauliWt_numD2In, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [Fin.sum_univ_two, ctCf, ctCm, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [h1, h2, paramNumOf_sum _ _ _ _ _ _
    (F := fun k : Fin 4 × Fin 2 => ctChainIn P (curveMomentum P.m u) k.1 (ctCm P k.2))
    (fun k => exists_quartic_elecChain _ _ _ _ _)]
  simp only [ctChainIn, paramNumOf_elecChain]
  norm_num [Nat.factorial]
  simp only [ctT1In, ctT2In, ctT3In, ctEIn, Finset.mul_sum, Finset.sum_mul, ←
    Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ctK]
  push_cast
  ring

/-! ### The contraction patterns of the incoming chain -/

section SlotsIn

variable (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ)

/-- The chain sum of the incoming class: `∑_μ tr(P_μ Y₀ γ^μ Y₁ Y₂ Y₃) = pw(P; Y₀, Y₁ Y₂ Y₃)`. -/
theorem sum_ch_ctBIn (m : ℝ) (p' p : Fin 4 → ℝ) :
    ∑ μ, ch (ctBIn m p' p μ) Y₀ Y₁ Y₂ Y₃ = pw (contractP (pauliMat m p' p)) Y₀ (Y₁ * Y₂ * Y₃) := by
  unfold ch ctBIn pw
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.mul_one, Matrix.mul_assoc]

theorem pw_sum_right (Q : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (W : Matrix (Fin 4) (Fin 4) ℂ)
    (Z : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : ∑ σ, pw Q W (Z σ) = pw Q W (∑ σ, Z σ) := by
  unfold pw
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [Matrix.mul_sum, Matrix.trace_sum]

theorem in01 : ∑ σ, pw P (gammaLower σ) (gamma σ * Y₂ * Y₃) = 2 * pw P 𝟙 (Y₂ * Y₃) := by
  have h := sum_pw_gammaLower_gamma P 𝟙 (Y₂ * Y₃)
  simp only [Matrix.one_mul] at h
  rw [← h]
  simp only [Matrix.mul_assoc]

theorem in02 : ∑ σ, pw P (gammaLower σ) (Y₁ * gamma σ * Y₃) =
    pw (contractP (mulLeftP Y₃ P)) 𝟙 Y₁ := by
  unfold pw
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [show contractP (mulLeftP Y₃ P) μ = ∑ σ, gamma σ * (Y₃ * P μ) * gammaLower σ from rfl,
    Matrix.mul_one]
  simp only [Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [show P μ * gammaLower σ * gamma μ * (Y₁ * gamma σ * Y₃) =
      (P μ * gammaLower σ * gamma μ * Y₁) * (gamma σ * Y₃) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem in03 : ∑ σ, pw P (gammaLower σ) (Y₁ * Y₂ * gamma σ) =
    pw (contractP P) 𝟙 (Y₁ * Y₂) := by
  unfold pw
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [show contractP P μ = ∑ σ, gamma σ * P μ * gammaLower σ from rfl, Matrix.mul_one]
  simp only [Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [show P μ * gammaLower σ * gamma μ * (Y₁ * Y₂ * gamma σ) =
      (P μ * gammaLower σ * gamma μ * (Y₁ * Y₂)) * gamma σ by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem in12 : ∑ σ, pw P Y₀ (gammaLower σ * gamma σ * Y₃) = -4 * pw P Y₀ Y₃ := by
  rw [pw_sum_right, ← Finset.sum_mul, sum_gammaLower_mul_gamma, Matrix.smul_mul, Matrix.one_mul,
    pw_smul_right]

theorem in13 : ∑ σ, pw P Y₀ (gammaLower σ * Y₂ * gamma σ) = pw P Y₀ (gamM Y₂) := by
  rw [pw_sum_right, sum_gammaLower_swap]

theorem in23 : ∑ σ, pw P Y₀ (Y₁ * gammaLower σ * gamma σ) = -4 * pw P Y₀ Y₁ := by
  have e : ∀ σ, Y₁ * gammaLower σ * gamma σ = Y₁ * (gammaLower σ * gamma σ) := fun σ => by
    rw [Matrix.mul_assoc]
  simp only [e]
  rw [pw_sum_right, ← Matrix.mul_sum, sum_gammaLower_mul_gamma, Matrix.mul_smul, Matrix.mul_one,
    pw_smul_right]

theorem in0123 : ∑ σ, ∑ τ, pw P (gammaLower σ) (gamma σ * gammaLower τ * gamma τ) =
    -8 * pw P 𝟙 𝟙 := by
  have e : ∀ σ, ∑ τ, pw P (gammaLower σ) (gamma σ * gammaLower τ * gamma τ) =
      -4 * pw P (gammaLower σ) (gamma σ) := fun σ => by
    have e' : ∀ τ, gamma σ * gammaLower τ * gamma τ = gamma σ * (gammaLower τ * gamma τ) :=
      fun τ => by rw [Matrix.mul_assoc]
    simp only [e']
    rw [pw_sum_right, ← Matrix.mul_sum, sum_gammaLower_mul_gamma, Matrix.mul_smul, Matrix.mul_one,
      pw_smul_right]
  simp only [e, ← Finset.mul_sum, sum_pw_gammaLower_gamma']
  ring

theorem in0213 : ∑ σ, ∑ τ, pw P (gammaLower σ) (gammaLower τ * gamma σ * gamma τ) =
    4 * pw P 𝟙 𝟙 := by
  have e : ∀ σ, ∑ τ, pw P (gammaLower σ) (gammaLower τ * gamma σ * gamma τ) =
      2 * pw P (gammaLower σ) (gamma σ) := fun σ => by
    rw [pw_sum_right, sum_gammaLower_gamma_gamma, pw_smul_right]
  simp only [e, ← Finset.mul_sum, sum_pw_gammaLower_gamma']
  ring

theorem in0312 : ∑ σ, ∑ τ, pw P (gammaLower σ) (gammaLower τ * gamma τ * gamma σ) =
    -8 * pw P 𝟙 𝟙 := by
  have e : ∀ σ, ∑ τ, pw P (gammaLower σ) (gammaLower τ * gamma τ * gamma σ) =
      -4 * pw P (gammaLower σ) (gamma σ) := fun σ => by
    rw [pw_sum_right, ← Finset.sum_mul, sum_gammaLower_mul_gamma, Matrix.smul_mul,
      Matrix.one_mul, pw_smul_right]
  simp only [e, ← Finset.mul_sum, sum_pw_gammaLower_gamma']
  ring

end SlotsIn

/-! ### The coefficients of the incoming class through base patterns -/

theorem contrC_ctLinesIn (A : Matrix (Fin 2) (Fin 2) ℝ) (k l : Fin 4) :
    contrC (ctAlpha kindsD2In) A (ctLinesIn k) (ctLinesIn l) = A⁻¹ 0 0 := by
  fin_cases k <;> fin_cases l <;>
    simp [contrC, castLoopMatrix, kindsD2In, LineKind.dir, ctLinesIn, Fin.sum_univ_two]

section CoeffIn

variable (m : ℝ) (p' p : Fin 4 → ℝ) (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
  (A : Matrix (Fin 2) (Fin 2) ℝ)

theorem sum_chainTwo_ctBIn :
    ∑ μ, chainTwo (ctAlpha kindsD2In) (ctBIn m p' p μ) E ctLinesIn A =
      ((A⁻¹ 0 0 : ℝ) : ℂ) * (2 * pw (contractP (pauliMat m p' p)) 𝟙 (E 2 * E 3) +
        pw (contractP (mulLeftP (E 3) (contractP (pauliMat m p' p)))) 𝟙 (E 1) +
        pw (contractP (contractP (pauliMat m p' p))) 𝟙 (E 1 * E 2) +
        -4 * pw (contractP (pauliMat m p' p)) (E 0) (E 3) +
        pw (contractP (pauliMat m p' p)) (E 0) (gamM (E 2)) +
        -4 * pw (contractP (pauliMat m p' p)) (E 0) (E 1)) := by
  set Q := contractP (pauliMat m p' p)
  have h01 : ∑ μ, ∑ ν, ch (ctBIn m p' p μ) (gammaLower ν) (gamma ν) (E 2) (E 3) =
      2 * pw Q 𝟙 (E 2 * E 3) := by
    rw [Finset.sum_comm]; simp only [sum_ch_ctBIn]; exact in01 _ _ _
  have h02 : ∑ μ, ∑ ν, ch (ctBIn m p' p μ) (gammaLower ν) (E 1) (gamma ν) (E 3) =
      pw (contractP (mulLeftP (E 3) Q)) 𝟙 (E 1) := by
    rw [Finset.sum_comm]; simp only [sum_ch_ctBIn]; exact in02 _ _ _
  have h03 : ∑ μ, ∑ ν, ch (ctBIn m p' p μ) (gammaLower ν) (E 1) (E 2) (gamma ν) =
      pw (contractP Q) 𝟙 (E 1 * E 2) := by
    rw [Finset.sum_comm]; simp only [sum_ch_ctBIn]; exact in03 _ _ _
  have h12 : ∑ μ, ∑ ν, ch (ctBIn m p' p μ) (E 0) (gammaLower ν) (gamma ν) (E 3) =
      -4 * pw Q (E 0) (E 3) := by
    rw [Finset.sum_comm]; simp only [sum_ch_ctBIn]; exact in12 _ _ _
  have h13 : ∑ μ, ∑ ν, ch (ctBIn m p' p μ) (E 0) (gammaLower ν) (E 2) (gamma ν) =
      pw Q (E 0) (gamM (E 2)) := by
    rw [Finset.sum_comm]; simp only [sum_ch_ctBIn]; exact in13 _ _ _
  have h23 : ∑ μ, ∑ ν, ch (ctBIn m p' p μ) (E 0) (E 1) (gammaLower ν) (gamma ν) =
      -4 * pw Q (E 0) (E 1) := by
    rw [Finset.sum_comm]; simp only [sum_ch_ctBIn]; exact in23 _ _ _
  simp only [chainTwo, contrC_ctLinesIn, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h01, h02, h03, h12, h13, h23]
  ring

theorem sum_chainFour_ctBIn :
    ∑ μ, chainFour (ctAlpha kindsD2In) (ctBIn m p' p μ) ctLinesIn A =
      ((A⁻¹ 0 0 : ℝ) : ℂ) ^ 2 * (-12 * pw (contractP (pauliMat m p' p)) 𝟙 𝟙) := by
  set Q := contractP (pauliMat m p' p)
  have h1 : ∑ μ, ∑ ν, ∑ ρ, ch (ctBIn m p' p μ) (gammaLower ν) (gamma ν) (gammaLower ρ) (gamma ρ) =
      -8 * pw Q 𝟙 𝟙 := by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun ν _ => Finset.sum_comm]
    simp only [sum_ch_ctBIn]
    exact in0123 _
  have h2 : ∑ μ, ∑ ν, ∑ ρ, ch (ctBIn m p' p μ) (gammaLower ν) (gammaLower ρ) (gamma ν) (gamma ρ) =
      4 * pw Q 𝟙 𝟙 := by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun ν _ => Finset.sum_comm]
    simp only [sum_ch_ctBIn]
    exact in0213 _
  have h3 : ∑ μ, ∑ ν, ∑ ρ, ch (ctBIn m p' p μ) (gammaLower ν) (gammaLower ρ) (gamma ρ) (gamma ν) =
      -8 * pw Q 𝟙 𝟙 := by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun ν _ => Finset.sum_comm]
    simp only [sum_ch_ctBIn]
    exact in0312 _
  simp only [chainFour, contrC_ctLinesIn, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1, h2, h3]
  ring

end CoeffIn

/-! ### The loop shift and the slot momenta -/

theorem symanzikMatrix_kinds (κ : Fin 8 → LineKind)
    (hκ : κ = kindsD2In ∨ κ = kindsD2Out) (z : Fin 8 → ℝ) :
    symanzikMatrix (castLoopMatrix fun i => (κ i).dir) z = !![ctX1 z, 0; 0, ctX2 z] := by
  rcases hκ with rfl | rfl <;>
  · ext s t
    fin_cases s <;> fin_cases t <;>
      simp [symanzikMatrix, castLoopMatrix, kindsD2In, kindsD2Out, LineKind.dir, Fin.sum_univ_eight,
        ctX1, ctX2]

theorem inv_symanzikMatrix_kinds (κ : Fin 8 → LineKind)
    (hκ : κ = kindsD2In ∨ κ = kindsD2Out) (z : Fin 8 → ℝ) (s t : Fin 2) :
    (symanzikMatrix (castLoopMatrix fun i => (κ i).dir) z)⁻¹ s t =
      (ctX1 z * ctX2 z)⁻¹ * !![ctX2 z, 0; 0, ctX1 z] s t := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', symanzikMatrix_kinds κ hκ z,
    Matrix.adjugate_fin_two_of, Matrix.det_fin_two_of, Matrix.smul_apply, smul_eq_mul]
  fin_cases s <;> fin_cases t <;> simp

/-- The outgoing-electron share `ζ = z₀/X₁` of the incoming class. -/
noncomputable def ctZetaIn (z : Fin 8 → ℝ) : ℝ := z 0 / ctX1 z

/-- The incoming-electron share `σ = (z₁ + z₂)/X₁` of the incoming class. -/
noncomputable def ctSigIn (z : Fin 8 → ℝ) : ℝ := (z 1 + z 2) / ctX1 z

/-- **The loop shift of the incoming class**: `S₀ = ζ p' + σ p`. -/
theorem loopShift_d2In (P : Params) (u : ℝ) {z : Fin 8 → ℝ} (hX1 : ctX1 z ≠ 0)
    (hX2 : ctX2 z ≠ 0) (μ : Fin 4) :
    loopShift (ctAlpha kindsD2In) (ctMom kindsD2In P u) z 0 μ =
      ctZetaIn z * curveMomentum P.m u μ + ctSigIn z * restMomentum P.m μ := by
  rw [QED.TwoLoop.LimitCovariance.loopShift_apply]
  simp only [Fin.sum_univ_two, inv_symanzikMatrix_kinds kindsD2In (Or.inl rfl)]
  simp [Fin.sum_univ_eight, castLoopMatrix, kindsD2In, LineKind.dir, LineKind.mom, ctZetaIn,
    ctSigIn, ctMom]
  simp only [ctX1, ctX2] at hX1 hX2 ⊢
  field_simp
  ring

/-- The outgoing slot momentum `p' - S₀ = -σ p + (1 - ζ) p'` of the incoming class. -/
noncomputable def ctQoIn (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : Fin 4 → ℝ :=
  fun μ => -ctSigIn z * restMomentum P.m μ + (1 - ctZetaIn z) * curveMomentum P.m u μ

/-- The incoming slot momentum `p - S₀ = (1 - σ) p - ζ p'` of the incoming class. -/
noncomputable def ctQiIn (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : Fin 4 → ℝ :=
  fun μ => (1 - ctSigIn z) * restMomentum P.m μ + -ctZetaIn z * curveMomentum P.m u μ

/-- **The slot numerators of the incoming class.** -/
theorem ctEIn_eq (P : Params) {z : Fin 8 → ℝ} (hX1 : ctX1 z ≠ 0) (hX2 : ctX2 z ≠ 0) (u c : ℝ) :
    ctEIn P z u c = ![electronNumerator P.m (ctQoIn P z u), electronNumerator P.m (ctQiIn P z u),
      electronNumerator c (ctQiIn P z u), electronNumerator P.m (ctQiIn P z u)] := by
  have hS := loopShift_d2In P u hX1 hX2
  funext k
  simp only [ctEIn, elecAt, lineMomentum_kinds]
  generalize loopShift (ctAlpha kindsD2In) (ctMom kindsD2In P u) z = L at hS ⊢
  fin_cases k <;>
  · congr 1
    funext μ
    simp [ctLinesIn, kindsD2In, LineKind.lineMom, ctQoIn, ctQiIn, hS]
    ring

/-! ### The planar form of the coefficients, incoming class -/

theorem ctQoIn_two (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : ctQoIn P z u 2 = 0 := by
  simp [ctQoIn, restMomentum_two, curveMomentum_two]

theorem ctQoIn_three (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : ctQoIn P z u 3 = 0 := by
  simp [ctQoIn, restMomentum_three, curveMomentum_three]

theorem ctQiIn_two (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : ctQiIn P z u 2 = 0 := by
  simp [ctQiIn, restMomentum_two, curveMomentum_two]

theorem ctQiIn_three (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : ctQiIn P z u 3 = 0 := by
  simp [ctQiIn, restMomentum_three, curveMomentum_three]

/-- The planar slot numerators of the incoming class. -/
noncomputable abbrev eoIn (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : Pl := ePl P.m (ctQoIn P z u)
/-- The planar slot numerators of the incoming class. -/
noncomputable abbrev eiIn (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : Pl := ePl P.m (ctQiIn P z u)
/-- The planar slot numerators of the incoming class. -/
noncomputable abbrev ecIn (P : Params) (z : Fin 8 → ℝ) (u c : ℝ) : Pl := ePl c (ctQiIn P z u)

theorem ctEIn_planar (P : Params) {z : Fin 8 → ℝ} (hX1 : ctX1 z ≠ 0) (hX2 : ctX2 z ≠ 0)
    (u c : ℝ) :
    ctEIn P z u c = ![toMat (eoIn P z u), toMat (eiIn P z u), toMat (ecIn P z u c),
      toMat (eiIn P z u)] := by
  rw [ctEIn_eq P hX1 hX2, electronNumerator_ePl P.m (ctQoIn_two P z u) (ctQoIn_three P z u),
    electronNumerator_ePl P.m (ctQiIn_two P z u) (ctQiIn_three P z u),
    electronNumerator_ePl c (ctQiIn_two P z u) (ctQiIn_three P z u)]

theorem gamM_toMat' (y : Pl) : gamM (toMat y) = toMat (gam y) := sum_gamma_toMat y

/-- **`T₁` of the incoming class as a planar expression.** -/
theorem ctT1In_planar (P : Params) {z : Fin 8 → ℝ} (hX1 : ctX1 z ≠ 0) (hX2 : ctX2 z ≠ 0)
    (u : ℝ) :
    ctT1In P z u = ∑ c : Fin 2, ctK P * ctCf P c *
      (((symanzikU (ctAlpha kindsD2In) z ^ 2 : ℝ) : ℂ)⁻¹ *
        (6 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) (eoIn P z u)
          (eiIn P z u * ecIn P z u (ctCm P c) * eiIn P z u))) := by
  have hP1 := planarPauli_contractP (planarPauli_ladder P u)
  unfold ctT1In
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [← Finset.mul_sum, sum_ch_ctBIn, ctEIn_planar P hX1 hX2, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, toMat_mul]
  rw [pw_planar hP1]

/-- **`T₂` of the incoming class as a planar expression.** -/
theorem ctT2In_planar (P : Params) {z : Fin 8 → ℝ} (hX1 : ctX1 z ≠ 0) (hX2 : ctX2 z ≠ 0)
    (u : ℝ) :
    ctT2In P z u = ∑ c : Fin 2, ctK P * ctCf P c *
      (((symanzikU (ctAlpha kindsD2In) z ^ 2 : ℝ) : ℂ)⁻¹ *
        ((((symanzikMatrix (ctAlpha kindsD2In) z)⁻¹ 0 0 : ℝ) : ℂ) *
          (2 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) 1
              (ecIn P z u (ctCm P c) * eiIn P z u) +
            pwPl (gam (eiIn P z u * gam (lQ0 P u))) (gam (eiIn P z u * gam (lQ1 P u)))
              (gamT (eiIn P z u * gamT (lR P u))) 1 (eiIn P z u) +
            pwPl (gam (gam (lQ0 P u))) (gam (gam (lQ1 P u))) (gamT (gamT (lR P u))) 1
              (eiIn P z u * ecIn P z u (ctCm P c)) +
            -4 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) (eoIn P z u) (eiIn P z u) +
            pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) (eoIn P z u)
              (gam (ecIn P z u (ctCm P c))) +
            -4 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) (eoIn P z u)
              (eiIn P z u)))) := by
  have hP1 := planarPauli_contractP (planarPauli_ladder P u)
  have hP2 := planarPauli_contractP hP1
  have hP3 := planarPauli_contractP (planarPauli_mulLeftP hP1 (eiIn P z u))
  unfold ctT2In
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [← Finset.mul_sum, sum_chainTwo_ctBIn, ctEIn_planar P hX1 hX2, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, toMat_mul, gamM_toMat']
  rw [← toMat_one]
  simp only [pw_planar hP1, pw_planar hP2, pw_planar hP3]

/-- **`T₃` of the incoming class as a planar expression.** -/
theorem ctT3In_planar (P : Params) (z : Fin 8 → ℝ) (u : ℝ) :
    ctT3In P z u = ∑ c : Fin 2, ctK P * ctCf P c *
      (((symanzikU (ctAlpha kindsD2In) z ^ 2 : ℝ) : ℂ)⁻¹ *
        (1 / 4 * ((((symanzikMatrix (ctAlpha kindsD2In) z)⁻¹ 0 0 : ℝ) : ℂ) ^ 2 *
          (-12 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) 1 1)))) := by
  have hP1 := planarPauli_contractP (planarPauli_ladder P u)
  unfold ctT3In
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [← Finset.mul_sum, sum_chainFour_ctBIn]
  rw [← toMat_one, pw_planar hP1]

end QED.TwoLoop.UnitSCCt

end
