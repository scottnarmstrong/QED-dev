/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.LimitCovarianceVP
public import QED.TwoLoop.CountertermLimit
public import QED.OneLoop.VertexFormFactors
import Mathlib.Tactic.Ring

/-!
# Covariance of the `ε → 0⁺` limits of the counterterm classes

Part of obligation O2-20 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4), for the seven counterterm
classes `QED.TwoLoop.Relabel.CtClass` of the order-`e⁵` vertex.

* **`δ₂`, `δ_m` and `δ₃` insertions.** Their limits come from the two-loop parametric
  representation of the product with an auxiliary loop
  (`QED/TwoLoop/CountertermLimitProduct.lean`); this file identifies the limit as a parametric
  value divided by `auxLimit m` (`exists_paramValue_of_kinds`). The numerators `numD2In`,
  `numD2Out`, `numD3` are vertex chains whose photon tensors are invariant, resp. lowered loop
  tensors (`photonNum_eq_lowered`), so they are covariant (`numD2In_cov`, …).
* **`δ₁` insertions.** The limit is `δ₁` times the one-loop vertex, whose closed form
  (`QED.OneLoop.VertexLimit.vertexLimit_entry_eq`) is an integral over Feynman parameters of the
  covariant matrices `closedFormMatrix` (`isLittleGroupCovariant_closedFormMatrix`).

The main statement is `isLittleGroupCovariant_ctLimitV`.
-/

@[expose] public section

open Complex Matrix Filter Topology MeasureTheory
open scoped Real

namespace QED.TwoLoop.LimitCovariance

open QED.Dirac QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.ClassLimit QED.TwoLoop.Insertion
open QED.TwoLoop.CountertermLimit QED.TwoLoop.Relabel
open QED.Integration.TwoLoop (LoopQuartic RefinedBound castLoopMatrix lineDenom lineMomentum
  NoSubdivergenceRefined IntNoSubdivergenceRefined noSubdivergenceRefined_castLoopMatrix_iff
  symanzikU symanzikV)

/-! ### The product limit with its value -/

/-- `exists_tendsto_energyFirstIntegral_of_product` with the limit identified. -/
theorem tendsto_energyFirstIntegral_of_product' {m : ℕ} (hm : 7 ≤ m)
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ)
    (Q : LoopQuartic) {E : Finset (Fin (m + 1))} (hcrit : NoSubdivergenceRefined 2 E α)
    (hB : RefinedBound α E 4 Q.eval) {c : ℝ} (hc : 0 < c)
    (hV : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU α z ≠ 0 →
      c ≤ symanzikV α p M z) {mass : ℝ} (hmass : 0 < mass) (F : ℝ → (Fin 4 → ℝ) → ℂ)
    (hfac : ∀ ε : ℝ, 0 < ε → ∀ ℓ : Fin 2 → Fin 4 → ℝ,
      Q.eval ℓ * ∏ i, (lineDenom α p M ε i ℓ)⁻¹ =
        F ε (ℓ 0) * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral (F ε)) (𝓝[>] 0)
      (𝓝 ((-((π : ℂ) ^ 4) * ∫ x in QED.Integration.Feynman.simplexSet m,
        paramIntegrand Q α p M 0 x) / auxLimit mass)) := by
  have hT := tendsto_jointEnergyFirstIntegral_of_refined Q α p M hm hcrit hB hc hV
  have hH := tendsto_energyFirstIntegral_aux hmass
  have hH0 := auxLimit_ne_zero hmass
  refine (hT.div hH hH0).congr' ?_
  filter_upwards [self_mem_nhdsWithin, hH.eventually_ne hH0] with ε (hε : 0 < ε) hne
  rw [Pi.div_apply, show (fun ℓ => Q.eval ℓ * ∏ i, (lineDenom α p M ε i ℓ)⁻¹) =
      fun ℓ => F ε (ℓ 0) * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3 from funext (hfac ε hε),
    jointEnergyFirstIntegral_two_mul (F ε) (fun k => ((propDenom mass ε k)⁻¹) ^ 3)]
  exact mul_div_cancel_right₀ _ hne

/-- The parametric data of product data given by line kinds. -/
noncomputable def kindsData {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
    (Ms : Fin (m + 1) → ℝ) {mass μ : ℝ} (hmass : 0 < mass) (hμ : 0 < μ) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hMe : ∀ i, κ i ≠ .pho → Ms i ^ 2 = mass ^ 2) (hMp : ∀ i, κ i = .pho → μ ^ 2 ≤ Ms i ^ 2)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (κ i).dir) : ParamData where
  m := m
  α := castLoopMatrix fun i => (κ i).dir
  p := fun i => (κ i).mom p p'
  M := Ms
  E := {0, 1, 2, 3}
  hm := hm7
  hcrit := (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit
  c := 3 / 4 * min (mass ^ 2) (μ ^ 2)
  hc := by positivity
  hV := fun _ hz hz1 hU => symanzikV_kinds_ge κ Ms hp hp' hq hMe hMp hz hz1 hU

/-- **The limit of a product-data integral as a parametric value divided by `auxLimit`.** -/
theorem exists_paramValue_of_kinds {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
    (Ms : Fin (m + 1) → ℝ) {mass μ : ℝ} (hmass : 0 < mass) (hμ : 0 < μ) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hMe : ∀ i, κ i ≠ .pho → Ms i ^ 2 = mass ^ 2) (hMp : ∀ i, κ i = .pho → μ ^ 2 ≤ Ms i ^ 2)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (κ i).dir)
    (hcard : ({0, 1, 2, 3} : Finset (Fin (m + 1))).card = 4)
    (hE : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))), κ e ≠ .aux)
    (N : (Fin 4 → ℝ) → ℂ) (hN : IsLoopPoly 2 4 fun ℓ => N (ℓ 0)) (F : ℝ → (Fin 4 → ℝ) → ℂ)
    (hfac : ∀ ε : ℝ, 0 < ε → ∀ ℓ : Fin 2 → Fin 4 → ℝ,
      N (ℓ 0) * ∏ i, (propDenom (Ms i) ε ((κ i).lineMom p p' ℓ))⁻¹ =
        F ε (ℓ 0) * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3) :
    ∃ v : ℂ, IsParamValue (kindsData hm7 κ Ms hmass hμ hp hp' hq hMe hMp hcrit)
        (fun ℓ => N (ℓ 0)) v ∧
      Tendsto (fun ε => QED.OneLoop.energyFirstIntegral (F ε)) (𝓝[>] 0) (𝓝 (v / auxLimit mass)) := by
  obtain ⟨Q, hQ⟩ := hN.exists_loopQuartic
  have hα : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))),
      (castLoopMatrix fun i => (κ i).dir) e = ![1, 0] := by
    intro e he
    have h := hE e he
    funext s
    rcases hk : κ e with _ | _ | _ | _
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · exact absurd hk h
  have hB : RefinedBound (castLoopMatrix fun i => (κ i).dir) {0, 1, 2, 3} 4 Q.eval :=
    refinedBound_of_dependsOnZero _ hcard hα Q fun ℓ => by simp only [hQ, Matrix.cons_val_zero]
  refine ⟨_, ⟨Q, hQ, hQ ▸ hB, rfl⟩, ?_⟩
  exact tendsto_energyFirstIntegral_of_product' hm7 _ _ Ms Q
    ((noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit) hB (by positivity)
    (fun z hz hz1 hU => symanzikV_kinds_ge κ Ms hp hp' hq hMe hMp hz hz1 hU) hmass F
    fun ε hε ℓ => by rw [hQ, prod_lineDenom_kinds]; exact hfac ε hε ℓ

theorem mulVec_lineKind_mom {L : Matrix (Fin 4) (Fin 4) ℝ} {p p' : Fin 4 → ℝ}
    (hp : L *ᵥ p = p) (hp' : L *ᵥ p' = p') (k : LineKind) :
    L *ᵥ k.mom p p' = k.mom p p' := by
  cases k <;> simp [LineKind.mom, hp, hp']


/-! ### Covariance of the counterterm numerators -/

section Num

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

theorem vertexChain_eq_chain (e : ℝ) (μ : Fin 4) (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (D : Fin 4 → Fin 4 → ℂ) :
    vertexChain e μ A B D = ((I * e) ^ 3 * (1 / I) ^ 3 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹) •
      IsSpinLift.chain D A B μ :=
  rfl

theorem tensorAct_pvPhotonNum (h : IsSpinLift L S T) (P : Params) :
    IsSpinLift.tensorAct L (pvPhotonNum P.mγ P.Λ) = pvPhotonNum P.mγ P.Λ := by
  funext ν' ρ'
  have := pvG_pair h P ν' ρ'
  simp only [pvG] at this
  simp only [IsSpinLift.tensorAct, pvPhotonNum]
  rw [← this]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem mul_fermionCtMatrix_mul (h : IsSpinLift L S T) (δ₂ δm m : ℝ) (u : Fin 4 → ℝ) :
    S * fermionCtMatrix δ₂ δm m (L *ᵥ u) * T = fermionCtMatrix δ₂ δm m u := by
  simp only [fermionCtMatrix, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, h.mul_eq_one, h.mul_slash_mul]

theorem mul_insertion_mul (h : IsSpinLift L S T) (δ₂ δm m : ℝ) (u : Fin 4 → ℝ) :
    S * (-(electronNumerator m (L *ᵥ u) * fermionCtMatrix δ₂ δm m (L *ᵥ u) *
      electronNumerator m (L *ᵥ u))) * T =
      -(electronNumerator m u * fermionCtMatrix δ₂ δm m u * electronNumerator m u) := by
  rw [Matrix.mul_neg, Matrix.neg_mul, h.mul_mul_mul, h.mul_mul_mul,
    h.mul_electronNumerator_mul, mul_fermionCtMatrix_mul h]

theorem add_mulVec_of_fix {p : Fin 4 → ℝ} (hp : L *ᵥ p = p) (k : Fin 4 → ℝ) :
    p + L *ᵥ k = L *ᵥ (p + k) := by
  rw [Matrix.mulVec_add, hp]

theorem numD2In_cov (h : IsSpinLift L S T) (P : Params) {p p' : Fin 4 → ℝ} (hp : L *ᵥ p = p)
    (hp' : L *ᵥ p' = p') (μ : Fin 4) (k : Fin 4 → ℝ) :
    S * numD2In P p' p μ (L *ᵥ k) * T = vecAct L (fun ν => numD2In P p' p ν k) μ := by
  simp only [numD2In, vertexChain_eq_chain, Matrix.mul_smul, Matrix.smul_mul, h.mul_chain_mul,
    tensorAct_pvPhotonNum h, add_mulVec_of_fix hp, add_mulVec_of_fix hp',
    h.mul_electronNumerator_mul, mul_insertion_mul h]
  rw [vecAct_smul]

theorem numD2Out_cov (h : IsSpinLift L S T) (P : Params) {p p' : Fin 4 → ℝ} (hp : L *ᵥ p = p)
    (hp' : L *ᵥ p' = p') (μ : Fin 4) (k : Fin 4 → ℝ) :
    S * numD2Out P p' p μ (L *ᵥ k) * T = vecAct L (fun ν => numD2Out P p' p ν k) μ := by
  simp only [numD2Out, vertexChain_eq_chain, Matrix.mul_smul, Matrix.smul_mul, h.mul_chain_mul,
    tensorAct_pvPhotonNum h, add_mulVec_of_fix hp, add_mulVec_of_fix hp',
    h.mul_electronNumerator_mul, mul_insertion_mul h]
  rw [vecAct_smul]

theorem photonCtFactor_mulVec (h : IsSpinLift L S T) (δ₃ : ℝ) (k : Fin 4 → ℝ) :
    photonCtFactor δ₃ (L *ᵥ k) = upperAct L (photonCtFactor δ₃ k) := by
  funext a b
  have hl := h.lorentz_left a b
  simp only [upperAct, photonCtFactor, h.dot_mulVec]
  have e : ∀ a' b', ((L a a' : ℝ) : ℂ) * ((L b b' : ℝ) : ℂ) *
      (-(I / 2) * ((δ₃ * (Minkowski.dot k k * Minkowski.metric a' b' - k a' * k b') : ℝ) : ℂ)) =
      -(I / 2) * ((δ₃ * (Minkowski.dot k k * (L a a' * L b b' * Minkowski.metric a' b') -
        (L a a' * k a') * (L b b' * k b')) : ℝ) : ℂ) := fun a' b' => by
    push_cast
    ring
  simp only [e, ← Finset.mul_sum, ← ofReal_sum]
  have hk : (L *ᵥ k) a * (L *ᵥ k) b = ∑ a', ∑ b', L a a' * k a' * (L b b' * k b') := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul_sum]
  rw [hk, ← hl]
  simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem photonNum_eq_lowered (P : Params) (k : Fin 4 → ℝ) :
    photonNum P.δ₃ P.mγ P.Λ k = fun ν ρ => (1 / I) * lowered P (photonCtFactor P.δ₃ k) ν ρ := by
  funext ν ρ
  simp only [photonNum, lowered, pvPhotonNum, pvG]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem tensorAct_const_mul (L : Matrix (Fin 4) (Fin 4) ℝ) (c : ℂ) (D : Fin 4 → Fin 4 → ℂ) :
    IsSpinLift.tensorAct L (fun ν ρ => c * D ν ρ) = fun ν ρ => c * IsSpinLift.tensorAct L D ν ρ := by
  funext ν ρ
  simp only [IsSpinLift.tensorAct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem numD3_cov (h : IsSpinLift L S T) (P : Params) {p p' : Fin 4 → ℝ} (hp : L *ᵥ p = p)
    (hp' : L *ᵥ p' = p') (μ : Fin 4) (k : Fin 4 → ℝ) :
    S * numD3 P p' p μ (L *ᵥ k) * T = vecAct L (fun ν => numD3 P p' p ν k) μ := by
  simp only [numD3, vertexChain_eq_chain, Matrix.mul_smul, Matrix.smul_mul, h.mul_chain_mul,
    photonNum_eq_lowered, photonCtFactor_mulVec h, tensorAct_const_mul, tensorAct_lowered h,
    add_mulVec_of_fix hp, add_mulVec_of_fix hp', h.mul_electronNumerator_mul]
  rw [vecAct_smul]

end Num


/-! ### The one-loop closed form -/

theorem vertexNumeratorMatrix_eq_chain (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 4 → ℝ) :
    QED.OneLoop.vertexNumeratorMatrix m p' p μ ℓ =
      IsSpinLift.chain (fun ν ρ => ((Minkowski.metric ν ρ : ℝ) : ℂ))
        (electronNumerator m (p' + ℓ)) (electronNumerator m (p + ℓ)) μ :=
  rfl

theorem tensorAct_metric {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}
    (h : IsSpinLift L S T) :
    IsSpinLift.tensorAct L (fun ν ρ => ((Minkowski.metric ν ρ : ℝ) : ℂ)) =
      fun ν ρ => ((Minkowski.metric ν ρ : ℝ) : ℂ) := by
  funext ν' ρ'
  rw [← h.lorentz_right ν' ρ']
  simp only [IsSpinLift.tensorAct, ofReal_sum, ofReal_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The closed-form integrand of the one-loop vertex is covariant**, at every point `z` of the
Feynman-parameter square. -/
theorem isLittleGroupCovariant_closedFormMatrix (m mγ Λ : ℝ) (p' p : Fin 4 → ℝ) (z : ℝ × ℝ) :
    IsLittleGroupCovariant p' p fun μ => QED.OneLoop.VertexLimit.closedFormMatrix m mγ Λ p' p μ z := by
  intro L S T hST hγ hLp hLp' μ
  have h : IsSpinLift L S T := ⟨hST, hγ⟩
  have hfix : ∀ u, L *ᵥ u = u → S * electronNumerator m u * T = electronNumerator m u := by
    intro u hu
    have := h.mul_electronNumerator_mul m u
    rwa [hu] at this
  have hsh : L *ᵥ QED.OneLoop.VertexLimit.shiftK p' p z = QED.OneLoop.VertexLimit.shiftK p' p z := by
    simp [QED.OneLoop.VertexLimit.shiftK, Matrix.mulVec_smul, Matrix.mulVec_add, hLp, hLp']
  have h1 : L *ᵥ (p' + -QED.OneLoop.VertexLimit.shiftK p' p z) =
      p' + -QED.OneLoop.VertexLimit.shiftK p' p z := by
    rw [Matrix.mulVec_add, Matrix.mulVec_neg, hsh, hLp']
  have h2 : L *ᵥ (p + -QED.OneLoop.VertexLimit.shiftK p' p z) =
      p + -QED.OneLoop.VertexLimit.shiftK p' p z := by
    rw [Matrix.mulVec_add, Matrix.mulVec_neg, hsh, hLp]
  have hv : S * QED.OneLoop.vertexNumeratorMatrix m p' p μ
      (-QED.OneLoop.VertexLimit.shiftK p' p z) * T =
      vecAct L (fun ν => QED.OneLoop.vertexNumeratorMatrix m p' p ν
        (-QED.OneLoop.VertexLimit.shiftK p' p z)) μ := by
    rw [vertexNumeratorMatrix_eq_chain, h.mul_chain_mul, tensorAct_metric h, hfix _ h1,
      hfix _ h2]
    rfl
  simp only [QED.OneLoop.VertexLimit.closedFormMatrix, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, hγ μ, hv]
  rw [vecAct_smul, vecAct_add, vecAct_smul, vecAct_smul]

theorem isLittleGroupCovariant_smul {p' p : Fin 4 → ℝ} (a : ℂ)
    {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hV : IsLittleGroupCovariant p' p V) :
    IsLittleGroupCovariant p' p fun μ => a • V μ := by
  intro L S T hST hγ hLp hLp' μ
  rw [Matrix.mul_smul, Matrix.smul_mul, hV L S T hST hγ hLp hLp' μ, vecAct_smul]

/-! ### The counterterm-class limits -/

/-- The vertex of `ε → 0⁺` limits of the counterterm class `c` at `(p', p)`. -/
noncomputable def ctLimitV (c : CtClass) (P : Params) (p p' : Fin 4 → ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => Matrix.of fun i j => limUnder (𝓝[>] (0 : ℝ)) fun ε =>
    contractionValue₂ { P with ε := ε } c.rep (fun _ => p') (fun _ => p) (fun _ => p' - p)
      (fun _ => i) (fun _ => j) (fun _ => μ)

/-- Covariance of a vertex of parametric values divided by a constant, for numerators depending
on `ℓ₀` only. -/
theorem isLittleGroupCovariant_of_kinds {p' p : Fin 4 → ℝ} (D : ParamData)
    (hD : ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ), IsSpinLift L S T →
      L *ᵥ p = p → L *ᵥ p' = p' → ∀ i, L *ᵥ D.p i = D.p i)
    (N : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hN : ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ), IsSpinLift L S T →
      L *ᵥ p = p → L *ᵥ p' = p' → ∀ μ k, S * N μ (L *ᵥ k) * T = vecAct L (fun ν => N ν k) μ)
    (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (a : ℂ)
    (hV : ∀ μ i j, ∃ v, IsParamValue D (fun ℓ => N μ (ℓ 0) i j) v ∧ V μ i j = v / a) :
    IsLittleGroupCovariant p' p V := by
  choose v hv hVv using hV
  have hW : IsLittleGroupCovariant p' p fun μ => Matrix.of (v μ) :=
    isLittleGroupCovariant_of_paramValue D hD (fun μ ℓ => N μ (ℓ 0))
      (fun L S T h hLp hLp' μ ℓ => hN L S T h hLp hLp' μ (ℓ 0)) _ fun μ i j => hv μ i j
  have e : V = fun μ => a⁻¹ • Matrix.of (v μ) := by
    funext μ
    ext i j
    simp only [hVv, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [e]
  exact isLittleGroupCovariant_smul _ hW


section CtLimits

variable (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p p' : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hm hmγ hΛ hp hp' hq

omit hm hmγ hΛ hp hp' hq in
theorem hmom_pair : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
  simp

theorem isLittleGroupCovariant_ctLimitV_d2In :
    IsLittleGroupCovariant p' p (ctLimitV .d2In P p p') := by
  obtain ⟨h1, h2⟩ := sq_min_le P hmγ hΛ
  have hMe : ∀ i, kindsD2In i ≠ .pho → massesD2In P i ^ 2 = P.m ^ 2 := fun i hi => by
    fin_cases i <;> simp_all [kindsD2In, massesD2In]
  have hMp : ∀ i, kindsD2In i = .pho → min P.mγ P.Λ ^ 2 ≤ massesD2In P i ^ 2 := fun i hi => by
    fin_cases i <;> simp_all [kindsD2In, massesD2In]
  have hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (kindsD2In i).dir := by decide
  refine isLittleGroupCovariant_of_kinds (kindsData (by norm_num) kindsD2In (massesD2In P) hm
    (lt_min hmγ hΛ) hp hp' hq hMe hMp hcrit)
    (fun L S T _ hLp hLp' i => mulVec_lineKind_mom hLp hLp' _) (fun μ k => numD2In P p' p μ k)
    (fun L S T h hLp hLp' μ k => numD2In_cov h P hLp hLp' μ k) _ (auxLimit P.m) fun μ i j => ?_
  obtain ⟨v, hv, hT⟩ := exists_paramValue_of_kinds (by norm_num) kindsD2In (massesD2In P) hm
    (lt_min hmγ hΛ) hp hp' hq hMe hMp hcrit (by decide) (by decide)
    (fun k => numD2In P p' p μ k i j) (isLoopPoly_numD2In P _ _ _ _ _)
    (fun ε k => vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' + k))
      (electronInsertion P.m ε P.δ₂ P.δm (p + k)) (QED.OneLoop.photonPropagator P.mγ P.Λ ε k) i j)
    (fun ε hε ℓ => by
      rw [integrand_d2In_eq P hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsD2In, massesD2In,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)
  refine ⟨v, hv, ?_⟩
  simp only [ctLimitV, Matrix.of_apply]
  have hcv : ∀ ε : ℝ, contractionValue₂ { P with ε := ε } (CtClass.rep .d2In) (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) =
      QED.OneLoop.energyFirstIntegral fun ℓ =>
        vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' + ℓ))
          (electronInsertion P.m ε P.δ₂ P.δm (p + ℓ))
          (QED.OneLoop.photonPropagator P.mγ P.Λ ε ℓ) i j := fun ε =>
    contractionValue₂_repD2In { P with ε := ε } hmom_pair (fun _ => i) (fun _ => j) (fun _ => μ)
  simp only [hcv]
  exact hT.limUnder_eq

theorem isLittleGroupCovariant_ctLimitV_d2Out :
    IsLittleGroupCovariant p' p (ctLimitV .d2Out P p p') := by
  obtain ⟨h1, h2⟩ := sq_min_le P hmγ hΛ
  have hMe : ∀ i, kindsD2Out i ≠ .pho → massesD2In P i ^ 2 = P.m ^ 2 := fun i hi => by
    fin_cases i <;> simp_all [kindsD2Out, massesD2In]
  have hMp : ∀ i, kindsD2Out i = .pho → min P.mγ P.Λ ^ 2 ≤ massesD2In P i ^ 2 := fun i hi => by
    fin_cases i <;> simp_all [kindsD2Out, massesD2In]
  have hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (kindsD2Out i).dir := by decide
  refine isLittleGroupCovariant_of_kinds (kindsData (by norm_num) kindsD2Out (massesD2In P) hm
    (lt_min hmγ hΛ) hp hp' hq hMe hMp hcrit)
    (fun L S T _ hLp hLp' i => mulVec_lineKind_mom hLp hLp' _) (fun μ k => numD2Out P p' p μ k)
    (fun L S T h hLp hLp' μ k => numD2Out_cov h P hLp hLp' μ k) _ (auxLimit P.m) fun μ i j => ?_
  obtain ⟨v, hv, hT⟩ := exists_paramValue_of_kinds (by norm_num) kindsD2Out (massesD2In P) hm
    (lt_min hmγ hΛ) hp hp' hq hMe hMp hcrit (by decide) (by decide)
    (fun k => numD2Out P p' p μ k i j) (isLoopPoly_numD2Out P _ _ _ _ _)
    (fun ε k => vertexChain P.e μ (electronInsertion P.m ε P.δ₂ P.δm (p' + k))
      (QED.OneLoop.electronPropagator P.m ε (p + k)) (QED.OneLoop.photonPropagator P.mγ P.Λ ε k) i j)
    (fun ε hε ℓ => by
      rw [integrand_d2Out_eq P hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsD2Out, massesD2In,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)
  refine ⟨v, hv, ?_⟩
  simp only [ctLimitV, Matrix.of_apply]
  have hcv : ∀ ε : ℝ, contractionValue₂ { P with ε := ε } (CtClass.rep .d2Out) (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) =
      QED.OneLoop.energyFirstIntegral fun ℓ =>
        vertexChain P.e μ (electronInsertion P.m ε P.δ₂ P.δm (p' + ℓ))
          (QED.OneLoop.electronPropagator P.m ε (p + ℓ))
          (QED.OneLoop.photonPropagator P.mγ P.Λ ε ℓ) i j := fun ε =>
    contractionValue₂_repD2Out { P with ε := ε } hmom_pair (fun _ => i) (fun _ => j) (fun _ => μ)
  simp only [hcv]
  exact hT.limUnder_eq

theorem isLittleGroupCovariant_ctLimitV_d3Slot0 :
    IsLittleGroupCovariant p' p (ctLimitV .d3Slot0 P p p') := by
  obtain ⟨h1, h2⟩ := sq_min_le P hmγ hΛ
  have hMe : ∀ i, kindsD3 i ≠ .pho → massesD3 P i ^ 2 = P.m ^ 2 := fun i hi => by
    fin_cases i <;> simp_all [kindsD3, massesD3]
  have hMp : ∀ i, kindsD3 i = .pho → min P.mγ P.Λ ^ 2 ≤ massesD3 P i ^ 2 := fun i hi => by
    fin_cases i <;> simp_all [kindsD3, massesD3]
  have hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (kindsD3 i).dir := by decide
  refine isLittleGroupCovariant_of_kinds (kindsData (by norm_num) kindsD3 (massesD3 P) hm
    (lt_min hmγ hΛ) hp hp' hq hMe hMp hcrit)
    (fun L S T _ hLp hLp' i => mulVec_lineKind_mom hLp hLp' _) (fun μ k => numD3 P p' p μ k)
    (fun L S T h hLp hLp' μ k => numD3_cov h P hLp hLp' μ k) _ (auxLimit P.m) fun μ i j => ?_
  obtain ⟨v, hv, hT⟩ := exists_paramValue_of_kinds (by norm_num) kindsD3 (massesD3 P) hm
    (lt_min hmγ hΛ) hp hp' hq hMe hMp hcrit (by decide) (by decide)
    (fun k => numD3 P p' p μ k i j) (isLoopPoly_numD3 P _ _ _ _ _)
    (fun ε k => vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' + k))
      (QED.OneLoop.electronPropagator P.m ε (p + k)) (photonInsertion P.δ₃ P.mγ P.Λ ε k) i j)
    (fun ε hε ℓ => by
      rw [integrand_d3_eq P hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsD3, massesD3,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)
  refine ⟨v, hv, ?_⟩
  simp only [ctLimitV, Matrix.of_apply]
  have hcv : ∀ ε : ℝ, contractionValue₂ { P with ε := ε } (CtClass.rep .d3Slot0) (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) =
      QED.OneLoop.energyFirstIntegral fun ℓ =>
        vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' + ℓ))
          (QED.OneLoop.electronPropagator P.m ε (p + ℓ))
          (photonInsertion P.δ₃ P.mγ P.Λ ε ℓ) i j := fun ε =>
    contractionValue₂_repD3Slot0 { P with ε := ε } hmom_pair (fun _ => i) (fun _ => j)
      (fun _ => μ)
  simp only [hcv]
  exact hT.limUnder_eq

theorem isLittleGroupCovariant_ctLimitV_d3Slot1 :
    IsLittleGroupCovariant p' p (ctLimitV .d3Slot1 P p p') := by
  have e : ctLimitV .d3Slot1 P p p' = ctLimitV .d3Slot0 P p p' := by
    funext μ
    ext i j
    simp only [ctLimitV, Matrix.of_apply]
    congr 1
    funext ε
    exact (contractionValue₂_d3Slot0_eq_d3Slot1 { P with ε := ε }
      hmom_pair (fun _ => i) (fun _ => j) (fun _ => μ)).symm
  rw [e]
  exact isLittleGroupCovariant_ctLimitV_d3Slot0 P hm hmγ hΛ hp hp' hq

end CtLimits


theorem limit_d1_eq (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0)
    (hp0' : 0 < p' 0) (μ i j : Fin 4) {f : ℝ → ℂ}
    (hf : ∀ ε : ℝ, f ε = (P.δ₁ : ℂ) * vertexValue { P with ε := ε } p' p μ i j) :
    limUnder (𝓝[>] (0 : ℝ)) f = ((P.δ₁ : ℂ) * (I * ((P.e ^ 3 / (16 * π ^ 2) : ℝ) : ℂ))) *
      ∫ z, QED.OneLoop.VertexLimit.closedFormMatrix P.m P.mγ P.Λ p' p μ z i j
        ∂QED.Integration.feynmanMeasure := by
  have hT := tendsto_vertexValue P hm hmγ hΛ (pOut := fun _ => p') (pIn := fun _ => p) hp hp'
    hp0 hp0' (fun _ => i) (fun _ => j) (fun _ => μ)
  have hE := QED.OneLoop.VertexLimit.vertexLimit_entry_eq (e := P.e) hm hmγ hΛ hp' hp hp0' hp0 μ i j
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hX : ∫ v, QED.OneLoop.VertexLimit.spatialG P.e P.m P.mγ P.Λ 0 p' p μ i j v =
      I * (((P.e ^ 3 / (16 * π ^ 2) : ℝ) : ℂ) *
        ∫ z, QED.OneLoop.VertexLimit.closedFormMatrix P.m P.mγ P.Λ p' p μ z i j
          ∂QED.Integration.feynmanMeasure) := by
    rw [← hE]
    field_simp
  rw [funext hf, ((hT.const_mul (P.δ₁ : ℂ))).limUnder_eq, hX]
  ring

theorem isLittleGroupCovariant_ctLimitV_d1 (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0) (hp0' : 0 < p' 0) {c : CtClass}
    (hc : c = .d1At1 ∨ c = .d1At2 ∨ c = .d1At3) :
    IsLittleGroupCovariant p' p (ctLimitV c P p p') := by
  have hval : ∀ (μ i j : Fin 4) (ε : ℝ), contractionValue₂ { P with ε := ε } c.rep (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) =
      (P.δ₁ : ℂ) * vertexValue { P with ε := ε } p' p μ i j := by
    intro μ i j ε
    rcases hc with rfl | rfl | rfl
    · exact contractionValue₂_d1At1 { P with ε := ε } hmom_pair (fun _ => i) (fun _ => j)
        (fun _ => μ)
    · exact contractionValue₂_d1At2 { P with ε := ε } hmom_pair (fun _ => i) (fun _ => j)
        (fun _ => μ)
    · exact contractionValue₂_d1At3 { P with ε := ε } hmom_pair (fun _ => i) (fun _ => j)
        (fun _ => μ)
  have e : ctLimitV c P p p' = fun μ => ((P.δ₁ : ℂ) * (I * ((P.e ^ 3 / (16 * π ^ 2) : ℝ) : ℂ))) •
      VertexCovariance.integralVertex QED.Integration.feynmanMeasure
        (fun z μ => QED.OneLoop.VertexLimit.closedFormMatrix P.m P.mγ P.Λ p' p μ z) μ := by
    funext μ
    ext i j
    simp only [ctLimitV, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      VertexCovariance.integralVertex]
    exact limit_d1_eq P hm hmγ hΛ hp hp' hp0 hp0' μ i j (hval μ i j)
  rw [e]
  exact isLittleGroupCovariant_smul _ (VertexCovariance.isLittleGroupCovariant_integral
    (fun μ i j => QED.OneLoop.VertexLimit.integrable_closedFormMatrix hm hmγ hΛ hp' hp hp0' hp0
      μ i j)
    fun z => isLittleGroupCovariant_closedFormMatrix _ _ _ _ _ z)

/-- **Covariance of the counterterm-class limits.** -/
theorem isLittleGroupCovariant_ctLimitV (c : CtClass) (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0) (hp0' : 0 < p' 0)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) :
    IsLittleGroupCovariant p' p (ctLimitV c P p p') := by
  cases c
  · exact isLittleGroupCovariant_ctLimitV_d2In P hm hmγ hΛ hp hp' hq
  · exact isLittleGroupCovariant_ctLimitV_d2Out P hm hmγ hΛ hp hp' hq
  · exact isLittleGroupCovariant_ctLimitV_d3Slot0 P hm hmγ hΛ hp hp' hq
  · exact isLittleGroupCovariant_ctLimitV_d3Slot1 P hm hmγ hΛ hp hp' hq
  · exact isLittleGroupCovariant_ctLimitV_d1 P hm hmγ hΛ hp hp' hp0 hp0' (Or.inl rfl)
  · exact isLittleGroupCovariant_ctLimitV_d1 P hm hmγ hΛ hp hp' hp0 hp0' (Or.inr (Or.inl rfl))
  · exact isLittleGroupCovariant_ctLimitV_d1 P hm hmγ hΛ hp hp' hp0 hp0' (Or.inr (Or.inr rfl))

end QED.TwoLoop.LimitCovariance

end
