/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLimCtCDNum

/-!
# Set (c), classes `CD0`, `CD1`: limits and covariance of the three products

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. For a product
`d(ε, k) N_μ(k)` of a numerator of degree four and inverse denominators given by line kinds
(`QED.TwoLoop.CountertermLimit.LineKind`), the `ε → 0⁺` limit `pieceLim d N` of its energy-first
integral is a parametric value divided by `auxLimit m` (`pieceLim_entry`,
`QED.TwoLoop.LimitCovariance.exists_paramValue_of_kinds`), and it is covariant under every
spinor-lifted `L` when the numerators are (`pieceLim_map`,
`QED.TwoLoop.ReflCovariance.conj_eq_vecAct_of_paramValue_div`).

The products of `QED/ChainProof/SetCLimCtCDNum.lean` fit: the numerators `numIn₁`, …, are of
degree four and covariant (`numIn₁_map`, …), the denominators `den₁`, `denIn₂`, `denOut₂` are those
of the kinds `kindsD3`, `kindsIn₂`, `kindsOut₂` with the auxiliary loop (`den₁_fac`, …).
-/

@[expose] public section

open Complex Matrix Filter Topology

namespace QED.ChainProof.SetCPauli

open QED.WickModel QED.TwoLoop.Insertion QED.TwoLoop.Bridge QED.TwoLoop.CountertermLimit
open QED.TwoLoop.LimitCovariance QED.TwoLoop.ReflCovariance QED.Dirac
open QED.Integration.TwoLoop (IntNoSubdivergenceRefined)
open QED.GradedProof.X0 (AffPoly)

/-! ### The general argument -/

/-- The `ε → 0⁺` limit of the energy-first integral of `d(ε, k) N_μ(k)`, entrywise. -/
noncomputable def pieceLim (d : ℝ → (Fin 4 → ℝ) → ℂ)
    (N : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => Matrix.of fun i j => limUnder (𝓝[>] (0 : ℝ)) fun ε =>
    QED.OneLoop.energyFirstIntegral fun k => d ε k * N μ k i j

section General

variable {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind) (Ms : Fin (m + 1) → ℝ)
  {mass μ₀ : ℝ} (hmass : 0 < mass) (hμ₀ : 0 < μ₀)
  (hMe : ∀ i, κ i ≠ .pho → Ms i ^ 2 = mass ^ 2) (hMp : ∀ i, κ i = .pho → μ₀ ^ 2 ≤ Ms i ^ 2)
  (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (κ i).dir)
  (hcard : ({0, 1, 2, 3} : Finset (Fin (m + 1))).card = 4)
  (hE : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))), κ e ≠ .aux)

include hm7 hmass hμ₀ hMe hMp hcrit hcard hE in
/-- **The limit of a product**: a parametric value divided by `auxLimit m`. -/
theorem pieceLim_entry {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -mass ^ 2)
    (hp' : Minkowski.dot p' p' = -mass ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (d : ℝ → (Fin 4 → ℝ) → ℂ) (N : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hN : ∀ μ i j, IsLoopPoly 2 4 fun ℓ => N μ (ℓ 0) i j)
    (hfac : ∀ ε : ℝ, 0 < ε → ∀ ℓ : Fin 2 → Fin 4 → ℝ,
      ∏ i, (propDenom (Ms i) ε ((κ i).lineMom p p' ℓ))⁻¹ =
        d ε (ℓ 0) * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3) (μ i j : Fin 4) :
    ∃ v, IsParamValue (kindsData hm7 κ Ms hmass hμ₀ hp hp' hq hMe hMp hcrit)
        (fun ℓ => N μ (ℓ 0) i j) v ∧
      Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun k => d ε k * N μ k i j) (𝓝[>] 0)
        (𝓝 (v / auxLimit mass)) ∧ pieceLim d N μ i j = v / auxLimit mass := by
  obtain ⟨v, hv, hT⟩ := exists_paramValue_of_kinds hm7 κ Ms hmass hμ₀ hp hp' hq hMe hMp hcrit
    hcard hE (fun k => N μ k i j) (hN μ i j) (fun ε k => d ε k * N μ k i j)
    (fun ε hε ℓ => by rw [hfac ε hε ℓ]; ring)
  exact ⟨v, hv, hT, hT.limUnder_eq⟩

include hm7 hmass hμ₀ hMe hMp hcrit hcard hE in
/-- **Covariance of the limit of a product** under a spinor-lifted `L`, with the external
momenta moved. -/
theorem pieceLim_map {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}
    (h : IsSpinLift L S T) (d : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ → (Fin 4 → ℝ) → ℂ)
    (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hN : ∀ p p' μ i j, IsLoopPoly 2 4 fun ℓ => N p p' μ (ℓ 0) i j)
    (hfac : ∀ p p' (ε : ℝ), 0 < ε → ∀ ℓ : Fin 2 → Fin 4 → ℝ,
      ∏ i, (propDenom (Ms i) ε ((κ i).lineMom p p' ℓ))⁻¹ =
        d p p' ε (ℓ 0) * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3)
    (hmap : ∀ p p' μ k, S * N (L *ᵥ p) (L *ᵥ p') μ (L *ᵥ k) * T =
      vecAct L (fun ν => N p p' ν k) μ)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -mass ^ 2)
    (hp' : Minkowski.dot p' p' = -mass ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (μ : Fin 4) :
    S * pieceLim (d (L *ᵥ p) (L *ᵥ p')) (N (L *ᵥ p) (L *ᵥ p')) μ * T =
      vecAct L (pieceLim (d p p') (N p p')) μ := by
  have hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -mass ^ 2 := by rw [h.dot_mulVec]; exact hp
  have hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -mass ^ 2 := by rw [h.dot_mulVec]; exact hp'
  have hqL : 0 ≤ Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p) := by
    rw [← Matrix.mulVec_sub, h.dot_mulVec]; exact hq
  refine conj_eq_vecAct_of_paramValue_div
    (kindsData hm7 κ Ms hmass hμ₀ hp hp' hq hMe hMp hcrit) h
    (fun i => (κ i).mom (L *ᵥ p) (L *ᵥ p')) (funext fun i => lineKind_mom_map p p' _)
    (N p p') (N (L *ᵥ p) (L *ᵥ p')) (hmap p p') _ _ (auxLimit mass)
    (fun μ i j => ?_) (fun μ i j => ?_) μ
  · obtain ⟨v, hv, -, hV⟩ := pieceLim_entry hm7 κ Ms hmass hμ₀ hMe hMp hcrit hcard hE hp hp' hq
      (d p p') (N p p') (hN p p') (hfac p p') μ i j
    exact ⟨v, hv, hV⟩
  · obtain ⟨v, hv, -, hV⟩ := pieceLim_entry hm7 κ Ms hmass hμ₀ hMe hMp hcrit hcard hE hpL hpL'
      hqL (d (L *ᵥ p) (L *ᵥ p')) (N (L *ᵥ p) (L *ᵥ p')) (hN _ _) (hfac _ _) μ i j
    obtain ⟨Q, hQ, hI, rfl⟩ := IsParamValue.exists_integrableOn hv
    exact ⟨Q, hQ, hI, hV⟩

end General

/-! ### The products of `CD0`, `CD1` -/

/-- The line kinds with the incoming line doubled. -/
def kindsIn₂ : Fin 10 → LineKind :=
  ![.out, .inn, .inn, .pho, .pho, .pho, .pho, .aux, .aux, .aux]

/-- The line kinds with the outgoing line doubled. -/
def kindsOut₂ : Fin 10 → LineKind :=
  ![.out, .out, .inn, .pho, .pho, .pho, .pho, .aux, .aux, .aux]

/-- The masses of `kindsIn₂`, `kindsOut₂`. -/
def massesD₂ (P : Params) : Fin 10 → ℝ :=
  ![P.m, P.m, P.m, P.mγ, P.Λ, P.mγ, P.Λ, P.m, P.m, P.m]

theorem intNoSubdivergenceRefined_kindsIn₂ :
    IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (kindsIn₂ i).dir := by
  decide

theorem intNoSubdivergenceRefined_kindsOut₂ :
    IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (kindsOut₂ i).dir := by
  decide

section Products

variable (P : Params)

theorem massesD₂_sq_of_ne_pho_in : ∀ i, kindsIn₂ i ≠ .pho → massesD₂ P i ^ 2 = P.m ^ 2 :=
  fun i hi => by fin_cases i <;> simp_all [kindsIn₂, massesD₂]

theorem massesD₂_sq_of_ne_pho_out : ∀ i, kindsOut₂ i ≠ .pho → massesD₂ P i ^ 2 = P.m ^ 2 :=
  fun i hi => by fin_cases i <;> simp_all [kindsOut₂, massesD₂]

theorem min_sq_le_massesD₂_sq_in (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    ∀ i, kindsIn₂ i = .pho → min P.mγ P.Λ ^ 2 ≤ massesD₂ P i ^ 2 := fun i hi => by
  obtain ⟨h1, h2⟩ := sq_min_le P hmγ hΛ
  fin_cases i <;> simp_all [kindsIn₂, massesD₂]

theorem min_sq_le_massesD₂_sq_out (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    ∀ i, kindsOut₂ i = .pho → min P.mγ P.Λ ^ 2 ≤ massesD₂ P i ^ 2 := fun i hi => by
  obtain ⟨h1, h2⟩ := sq_min_le P hmγ hΛ
  fin_cases i <;> simp_all [kindsOut₂, massesD₂]

theorem den₁_fac (p p' : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ i, (propDenom (massesD3 P i) ε ((kindsD3 i).lineMom p p' ℓ))⁻¹ =
      den₁ P p' p ε (ℓ 0) * ((propDenom P.m ε (ℓ 1))⁻¹) ^ 3 := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsD3, massesD3, den₁, phDen,
    LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

theorem denIn₂_fac (p p' : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ i, (propDenom (massesD₂ P i) ε ((kindsIn₂ i).lineMom p p' ℓ))⁻¹ =
      denIn₂ P p' p ε (ℓ 0) * ((propDenom P.m ε (ℓ 1))⁻¹) ^ 3 := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsIn₂, massesD₂, denIn₂, phDen,
    LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

theorem denOut₂_fac (p p' : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ i, (propDenom (massesD₂ P i) ε ((kindsOut₂ i).lineMom p p' ℓ))⁻¹ =
      denOut₂ P p' p ε (ℓ 0) * ((propDenom P.m ε (ℓ 1))⁻¹) ^ 3 := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsOut₂, massesD₂, denOut₂, phDen,
    LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

/-! #### Degree four -/

variable (p' p : Fin 4 → ℝ) (μ : Fin 4)

theorem affMat_numIn₁ : AffMat 4 (numIn₁ P p' p μ) :=
  affMat_vertexChain _ _ (AffMat.electronNumerator _ _) (AffMat.mergeY _ _ _ _).neg _ _ _

theorem affMat_numIn₂ : AffMat 4 (numIn₂ P p' p μ) :=
  affMat_vertexChain _ _ (AffMat.electronNumerator _ _)
    ((AffMat.electronNumerator _ _).smul _).neg _ _ _

theorem affMat_numOut₁ : AffMat 4 (numOut₁ P p' p μ) :=
  affMat_vertexChain _ _ (AffMat.mergeY _ _ _ _).neg (AffMat.electronNumerator _ _) _ _ _

theorem affMat_numOut₂ : AffMat 4 (numOut₂ P p' p μ) :=
  affMat_vertexChain _ _ ((AffMat.electronNumerator _ _).smul _).neg
    (AffMat.electronNumerator _ _) _ _ _

/-! #### Integrability at `ε > 0` -/

variable {ε : ℝ} (hε : 0 < ε) {N : (Fin 4 → ℝ) → ℂ} (hN : AffPoly 4 N)
include hε hN

theorem jointEnergyFirstIntegrable_den₁ :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ => den₁ P p' p ε (ℓ 0) * N (ℓ 0) := by
  have h := jointEnergyFirstIntegrable_affPoly_prod ![p', p, 0, 0, 0, 0]
    ![P.m, P.m, P.mγ, P.Λ, P.mγ, P.Λ] hε (by simp) hN
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, den₁, phDen, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero]
  simp only [add_comm (ℓ 0)]
  ring

theorem jointEnergyFirstIntegrable_denIn₂ :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ => denIn₂ P p' p ε (ℓ 0) * N (ℓ 0) := by
  have h := jointEnergyFirstIntegrable_affPoly_prod ![p', p, p, 0, 0, 0, 0]
    ![P.m, P.m, P.m, P.mγ, P.Λ, P.mγ, P.Λ] hε (by simp) hN
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, denIn₂, phDen, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero]
  simp only [add_comm (ℓ 0)]
  ring

theorem jointEnergyFirstIntegrable_denOut₂ :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ => denOut₂ P p' p ε (ℓ 0) * N (ℓ 0) := by
  have h := jointEnergyFirstIntegrable_affPoly_prod ![p', p', p, 0, 0, 0, 0]
    ![P.m, P.m, P.m, P.mγ, P.Λ, P.mγ, P.Λ] hε (by simp) hN
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, denOut₂, phDen, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero]
  simp only [add_comm (ℓ 0)]
  ring

end Products

/-! ### Covariance of the numerators -/

section Map

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

theorem mul_mergeY_mul (h : IsSpinLift L S T) (m δ₂ δm : ℝ) (u : Fin 4 → ℝ) :
    S * -mergeY m δ₂ δm (L *ᵥ u) * T = -mergeY m δ₂ δm u := by
  simp only [mergeY, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, h.mul_electronNumerator_mul, Matrix.mul_one, h.mul_eq_one]

theorem mul_mergeC_mul (h : IsSpinLift L S T) (m δ₂ δm : ℝ) (u : Fin 4 → ℝ) :
    S * -(mergeC m δ₂ δm • electronNumerator m (L *ᵥ u)) * T =
      -(mergeC m δ₂ δm • electronNumerator m u) := by
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul,
    h.mul_electronNumerator_mul]

variable (h : IsSpinLift L S T) (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) (k : Fin 4 → ℝ)
include h

theorem numIn₁_map :
    S * numIn₁ P (L *ᵥ p') (L *ᵥ p) μ (L *ᵥ k) * T = vecAct L (fun ν => numIn₁ P p' p ν k) μ := by
  simp only [numIn₁, vertexChain_eq_chain, Matrix.mul_smul, Matrix.smul_mul, h.mul_chain_mul,
    photonNum_eq_lowered, photonCtFactor_mulVec h, tensorAct_const_mul, tensorAct_lowered h,
    mulVec_add_mulVec, h.mul_electronNumerator_mul, mul_mergeY_mul h]
  rw [vecAct_smul]

theorem numIn₂_map :
    S * numIn₂ P (L *ᵥ p') (L *ᵥ p) μ (L *ᵥ k) * T = vecAct L (fun ν => numIn₂ P p' p ν k) μ := by
  simp only [numIn₂, vertexChain_eq_chain, Matrix.mul_smul, Matrix.smul_mul, h.mul_chain_mul,
    photonNum_eq_lowered, photonCtFactor_mulVec h, tensorAct_const_mul, tensorAct_lowered h,
    mulVec_add_mulVec, h.mul_electronNumerator_mul, mul_mergeC_mul h]
  rw [vecAct_smul]

theorem numOut₁_map :
    S * numOut₁ P (L *ᵥ p') (L *ᵥ p) μ (L *ᵥ k) * T =
      vecAct L (fun ν => numOut₁ P p' p ν k) μ := by
  simp only [numOut₁, vertexChain_eq_chain, Matrix.mul_smul, Matrix.smul_mul, h.mul_chain_mul,
    photonNum_eq_lowered, photonCtFactor_mulVec h, tensorAct_const_mul, tensorAct_lowered h,
    mulVec_add_mulVec, h.mul_electronNumerator_mul, mul_mergeY_mul h]
  rw [vecAct_smul]

theorem numOut₂_map :
    S * numOut₂ P (L *ᵥ p') (L *ᵥ p) μ (L *ᵥ k) * T =
      vecAct L (fun ν => numOut₂ P p' p ν k) μ := by
  simp only [numOut₂, vertexChain_eq_chain, Matrix.mul_smul, Matrix.smul_mul, h.mul_chain_mul,
    photonNum_eq_lowered, photonCtFactor_mulVec h, tensorAct_const_mul, tensorAct_lowered h,
    mulVec_add_mulVec, h.mul_electronNumerator_mul, mul_mergeC_mul h]
  rw [vecAct_smul]

end Map

end QED.ChainProof.SetCPauli

end
