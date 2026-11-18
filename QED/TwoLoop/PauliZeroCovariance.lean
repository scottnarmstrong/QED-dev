/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.FormFactorClause
import Mathlib.Tactic.Ring

/-!
# Covariance of the order-`e⁵` vertex limit under Lorentz maps that move the external momenta

Part of obligation O2-22 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4). For a real `L` with a
spinor lift `(S, T)` (`QED.TwoLoop.LimitCovariance.IsSpinLift`), on-shell `p, p'` with `q² ≥ 0`
such that `p, p', L p, L p'` have positive energy, the `ε → 0⁺` limits `V` at `(p', p)` and `W` at
`(L p', L p)` of the order-`e⁵` vertex satisfy

`S W^μ T = L^μ_ν V^ν`  (`conj_vertexLimit_map`),

and the Pauli projector is invariant (`formFactorProj₂_vertexLimit_map`):
`P₂(L p', L p; W) = P₂(p', p; V)`.

The classes of five gauge vertices and the counterterm classes `δ₂ in`, `δ₃` (slot `0`) were done
in `QED/TwoLoop/ReflCovariance*.lean`. This file adds `δ₂ out` (`ctLimitV_d2Out_map`, the same
proof as `δ₂ in`), `δ₃` (slot `1`) (equal to slot `0`), and the three `δ₁` classes
(`ctLimitV_d1_map`, from the covariance of the one-loop closed-form integrand,
`closedFormMatrix_map`; this uses the positive energies of both pairs).

The invariance of the trace projector (`formFactorProj₂_map`) is algebra: conjugation by `S`
preserves traces, `S (m - (L u)̸) T = m - u̸`, and `Lᵀ g L = g`.
-/

@[expose] public section

open Complex Matrix Filter Topology MeasureTheory
open scoped Real

namespace QED.TwoLoop.PauliZero

open QED.Dirac QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.ClassLimit QED.TwoLoop.Insertion
open QED.TwoLoop.CountertermLimit QED.TwoLoop.Relabel QED.TwoLoop.LimitCovariance
open QED.TwoLoop.ReflCovariance QED.TwoLoop.Enumeration
open QED.Integration.TwoLoop (LoopQuartic IntNoSubdivergenceRefined)

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

/-! ### The counterterm class `δ₂ out` -/

theorem numD2Out_map (h : IsSpinLift L S T) (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (k : Fin 4 → ℝ) :
    S * numD2Out P (L *ᵥ p') (L *ᵥ p) μ (L *ᵥ k) * T =
      vecAct L (fun ν => numD2Out P p' p ν k) μ := by
  simp only [numD2Out, vertexChain_eq_chain, Matrix.mul_smul, Matrix.smul_mul, h.mul_chain_mul,
    tensorAct_pvPhotonNum h, mulVec_add_mulVec, h.mul_electronNumerator_mul, mul_insertion_mul h]
  rw [vecAct_smul]

section D2Out

variable (P : Params)

theorem massesD2In_sq_of_ne_pho_out :
    ∀ i, kindsD2Out i ≠ .pho → massesD2In P i ^ 2 = P.m ^ 2 := fun i hi => by
  fin_cases i <;> simp_all [kindsD2Out, massesD2In]

theorem min_sq_le_massesD2In_sq_out (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    ∀ i, kindsD2Out i = .pho → min P.mγ P.Λ ^ 2 ≤ massesD2In P i ^ 2 := fun i hi => by
  obtain ⟨h1, h2⟩ := sq_min_le P hmγ hΛ
  fin_cases i <;> simp_all [kindsD2Out, massesD2In]

theorem intNoSubdivergenceRefined_kindsD2Out :
    IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (kindsD2Out i).dir := by
  decide

variable (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
variable {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
  (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hm hmγ hΛ hp hp' hq

/-- The parametric data of the `δ₂ out` class at `(p', p)`. -/
noncomputable def d2OutData : ParamData :=
  kindsData (by norm_num) kindsD2Out (massesD2In P) hm (lt_min hmγ hΛ) hp hp' hq
    (massesD2In_sq_of_ne_pho_out P) (min_sq_le_massesD2In_sq_out P hmγ hΛ)
    intNoSubdivergenceRefined_kindsD2Out

/-- The entries of the `δ₂ out` limit as parametric values divided by `auxLimit m`. -/
theorem ctLimitV_d2Out_entry (μ i j : Fin 4) :
    ∃ v, IsParamValue (d2OutData P hm hmγ hΛ hp hp' hq)
        (fun ℓ => numD2Out P p' p μ (ℓ 0) i j) v ∧
      ctLimitV .d2Out P p p' μ i j = v / auxLimit P.m := by
  obtain ⟨v, hv, hT⟩ := exists_paramValue_of_kinds (by norm_num) kindsD2Out (massesD2In P) hm
    (lt_min hmγ hΛ) hp hp' hq (massesD2In_sq_of_ne_pho_out P)
    (min_sq_le_massesD2In_sq_out P hmγ hΛ) intNoSubdivergenceRefined_kindsD2Out (by decide)
    (by decide) (fun k => numD2Out P p' p μ k i j) (isLoopPoly_numD2Out P _ _ _ _ _)
    (fun ε k => vertexChain P.e μ (electronInsertion P.m ε P.δ₂ P.δm (p' + k))
      (QED.OneLoop.electronPropagator P.m ε (p + k))
      (QED.OneLoop.photonPropagator P.mγ P.Λ ε k) i j)
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
    contractionValue₂_repD2Out { P with ε := ε } hmom_pair (fun _ => i) (fun _ => j)
      (fun _ => μ)
  simp only [hcv]
  exact hT.limUnder_eq

omit hp hp' hq in
/-- **Covariance of the `δ₂ out` limit under `L`, with the external momenta moved.** -/
theorem ctLimitV_d2Out_map (h : IsSpinLift L S T) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (μ : Fin 4) :
    S * ctLimitV .d2Out P (L *ᵥ p) (L *ᵥ p') μ * T = vecAct L (ctLimitV .d2Out P p p') μ := by
  have hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp
  have hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp'
  have hqL : 0 ≤ Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p) := by
    rw [← Matrix.mulVec_sub, h.dot_mulVec]; exact hq
  refine conj_eq_vecAct_of_paramValue_div (d2OutData P hm hmγ hΛ hp hp' hq) h
    (fun i => (kindsD2Out i).mom (L *ᵥ p) (L *ᵥ p')) (funext fun i => lineKind_mom_map p p' _)
    (fun μ k => numD2Out P p' p μ k) (fun μ k => numD2Out P (L *ᵥ p') (L *ᵥ p) μ k)
    (fun μ k => numD2Out_map h P p' p μ k) _ _ (auxLimit P.m)
    (fun μ i j => ctLimitV_d2Out_entry P hm hmγ hΛ hp hp' hq μ i j) (fun μ i j => ?_) μ
  obtain ⟨v, hv, hV⟩ := ctLimitV_d2Out_entry P hm hmγ hΛ hpL hpL' hqL μ i j
  obtain ⟨Q, hQ, hI, rfl⟩ := IsParamValue.exists_integrableOn hv
  exact ⟨Q, hQ, hI, hV⟩

end D2Out

/-! ### The counterterm class `δ₃` (slot `1`) -/

theorem ctLimitV_d3Slot1_eq (P : Params) (p p' : Fin 4 → ℝ) :
    ctLimitV .d3Slot1 P p p' = ctLimitV .d3Slot0 P p p' := by
  funext μ
  ext i j
  simp only [ctLimitV, Matrix.of_apply]
  congr 1
  funext ε
  exact (contractionValue₂_d3Slot0_eq_d3Slot1 { P with ε := ε }
    hmom_pair (fun _ => i) (fun _ => j) (fun _ => μ)).symm

/-! ### The `δ₁` classes -/

theorem feynmanMass_map (h : IsSpinLift L S T) (m M x y : ℝ) (p' p : Fin 4 → ℝ) :
    QED.OneLoop.feynmanMass m M x y (L *ᵥ p') (L *ᵥ p) = QED.OneLoop.feynmanMass m M x y p' p := by
  have e : y • (x • (L *ᵥ p') + (1 - x) • (L *ᵥ p)) = L *ᵥ (y • (x • p' + (1 - x) • p)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [QED.OneLoop.feynmanMass, e, h.dot_mulVec]

theorem shiftK_map (p' p : Fin 4 → ℝ) (z : ℝ × ℝ) :
    QED.OneLoop.VertexLimit.shiftK (L *ᵥ p') (L *ᵥ p) z =
      L *ᵥ QED.OneLoop.VertexLimit.shiftK p' p z := by
  simp only [QED.OneLoop.VertexLimit.shiftK, Matrix.mulVec_smul, Matrix.mulVec_add]

/-- **The closed-form integrand of the one-loop vertex under `L`, with the external momenta
moved.** -/
theorem closedFormMatrix_map (h : IsSpinLift L S T) (m mγ Λ : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (z : ℝ × ℝ) :
    S * QED.OneLoop.VertexLimit.closedFormMatrix m mγ Λ (L *ᵥ p') (L *ᵥ p) μ z * T =
      vecAct L (fun ν => QED.OneLoop.VertexLimit.closedFormMatrix m mγ Λ p' p ν z) μ := by
  have h1 : L *ᵥ p' + -QED.OneLoop.VertexLimit.shiftK (L *ᵥ p') (L *ᵥ p) z =
      L *ᵥ (p' + -QED.OneLoop.VertexLimit.shiftK p' p z) := by
    rw [shiftK_map, Matrix.mulVec_add, Matrix.mulVec_neg]
  have h2 : L *ᵥ p + -QED.OneLoop.VertexLimit.shiftK (L *ᵥ p') (L *ᵥ p) z =
      L *ᵥ (p + -QED.OneLoop.VertexLimit.shiftK p' p z) := by
    rw [shiftK_map, Matrix.mulVec_add, Matrix.mulVec_neg]
  have hv : S * QED.OneLoop.vertexNumeratorMatrix m (L *ᵥ p') (L *ᵥ p) μ
      (-QED.OneLoop.VertexLimit.shiftK (L *ᵥ p') (L *ᵥ p) z) * T =
      vecAct L (fun ν => QED.OneLoop.vertexNumeratorMatrix m p' p ν
        (-QED.OneLoop.VertexLimit.shiftK p' p z)) μ := by
    rw [vertexNumeratorMatrix_eq_chain, h.mul_chain_mul, tensorAct_metric h, h1, h2,
      h.mul_electronNumerator_mul, h.mul_electronNumerator_mul]
    rfl
  simp only [QED.OneLoop.VertexLimit.closedFormMatrix, feynmanMass_map h, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, h.mul_gamma_mul μ, hv]
  rw [vecAct_smul, vecAct_add, vecAct_smul, vecAct_smul]
  rfl

theorem isD1_rep {c : CtClass} (hc : c = .d1At1 ∨ c = .d1At2 ∨ c = .d1At3) (P : Params)
    (p p' : Fin 4 → ℝ) (μ i j : Fin 4) (ε : ℝ) :
    contractionValue₂ { P with ε := ε } c.rep (fun _ => p') (fun _ => p) (fun _ => p' - p)
      (fun _ => i) (fun _ => j) (fun _ => μ) =
      (P.δ₁ : ℂ) * vertexValue { P with ε := ε } p' p μ i j := by
  rcases hc with rfl | rfl | rfl
  · exact contractionValue₂_d1At1 { P with ε := ε } hmom_pair (fun _ => i) (fun _ => j)
      (fun _ => μ)
  · exact contractionValue₂_d1At2 { P with ε := ε } hmom_pair (fun _ => i) (fun _ => j)
      (fun _ => μ)
  · exact contractionValue₂_d1At3 { P with ε := ε } hmom_pair (fun _ => i) (fun _ => j)
      (fun _ => μ)

/-- The `δ₁` limits as `δ₁` times the closed form of the one-loop vertex. -/
theorem ctLimitV_d1_eq (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp0 : 0 < p 0) (hp0' : 0 < p' 0) {c : CtClass}
    (hc : c = .d1At1 ∨ c = .d1At2 ∨ c = .d1At3) :
    ctLimitV c P p p' = fun μ => ((P.δ₁ : ℂ) * (I * ((P.e ^ 3 / (16 * π ^ 2) : ℝ) : ℂ))) •
      VertexCovariance.integralVertex QED.Integration.feynmanMeasure
        (fun z μ => QED.OneLoop.VertexLimit.closedFormMatrix P.m P.mγ P.Λ p' p μ z) μ := by
  funext μ
  ext i j
  simp only [ctLimitV, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    VertexCovariance.integralVertex]
  exact limit_d1_eq P hm hmγ hΛ hp hp' hp0 hp0' μ i j (isD1_rep hc P p p' μ i j)

/-- **Covariance of the `δ₁` limits under `L`, with the external momenta moved**, for pairs
`(p', p)` and `(L p', L p)` of positive energy. -/
theorem ctLimitV_d1_map (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (h : IsSpinLift L S T) {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0) (hp0' : 0 < p' 0)
    (hLp0 : 0 < (L *ᵥ p) 0) (hLp0' : 0 < (L *ᵥ p') 0) {c : CtClass}
    (hc : c = .d1At1 ∨ c = .d1At2 ∨ c = .d1At3) (μ : Fin 4) :
    S * ctLimitV c P (L *ᵥ p) (L *ᵥ p') μ * T = vecAct L (ctLimitV c P p p') μ := by
  have hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp
  have hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp'
  have hI₁ := fun μ i j => QED.OneLoop.VertexLimit.integrable_closedFormMatrix (mγ := P.mγ)
    (Λ := P.Λ) hm hmγ hΛ hpL' hpL hLp0' hLp0 μ i j
  have hI₂ := fun μ i j => QED.OneLoop.VertexLimit.integrable_closedFormMatrix (mγ := P.mγ)
    (Λ := P.Λ) hm hmγ hΛ hp' hp hp0' hp0 μ i j
  rw [ctLimitV_d1_eq P hm hmγ hΛ hpL hpL' hLp0 hLp0' hc,
    ctLimitV_d1_eq P hm hmγ hΛ hp hp' hp0 hp0' hc]
  dsimp only
  rw [Matrix.mul_smul, Matrix.smul_mul, VertexCovariance.integralVertex_mul hI₁, vecAct_smul,
    VertexCovariance.integralVertex_vecAct hI₂]
  congr 1
  simp only [VertexCovariance.integralVertex]
  ext i j
  simp only [Matrix.of_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
    dsimp only
    rw [closedFormMatrix_map h])

/-! ### All counterterm classes -/

/-- **Covariance of every counterterm-class limit under `L`, with the external momenta moved.** -/
theorem ctLimitV_map (c : CtClass) (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (h : IsSpinLift L S T) {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0) (hp0' : 0 < p' 0)
    (hLp0 : 0 < (L *ᵥ p) 0) (hLp0' : 0 < (L *ᵥ p') 0)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (μ : Fin 4) :
    S * ctLimitV c P (L *ᵥ p) (L *ᵥ p') μ * T = vecAct L (ctLimitV c P p p') μ := by
  cases c
  · exact ctLimitV_d2In_map P hm hmγ hΛ h hp hp' hq μ
  · exact ctLimitV_d2Out_map P hm hmγ hΛ h hp hp' hq μ
  · exact ctLimitV_d3Slot0_map P hm hmγ hΛ h hp hp' hq μ
  · rw [ctLimitV_d3Slot1_eq, ctLimitV_d3Slot1_eq]
    exact ctLimitV_d3Slot0_map P hm hmγ hΛ h hp hp' hq μ
  · exact ctLimitV_d1_map P hm hmγ hΛ h hp hp' hp0 hp0' hLp0 hLp0' (Or.inl rfl) μ
  · exact ctLimitV_d1_map P hm hmγ hΛ h hp hp' hp0 hp0' hLp0 hLp0' (Or.inr (Or.inl rfl)) μ
  · exact ctLimitV_d1_map P hm hmγ hΛ h hp hp' hp0 hp0' hLp0 hLp0' (Or.inr (Or.inr rfl)) μ

/-! ### The vertex limit -/

/-- **The vertex limit as the sum of the class limits.** -/
theorem eq_classLimits_of_isVertexOrderFiveLimit (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p' p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0)
    (hp0' : 0 < p' 0) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hV : IsVertexOrderFiveLimit P p' p V) :
    V = fun μ => (1 / I) •
      ((∑ c ∈ Furry.nonFurry, (c.sign : ℂ) • classLimitV c P p p' μ) +
        ∑ c ∈ (Finset.univ : Finset CtClass), (1 : ℂ) • ctLimitV c P p p' μ) := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  funext μ
  ext i j
  have e : ∀ ε : ℝ, vertexOrderFive { P with ε := ε } p' p μ i j = (1 / I) *
      (∑ c ∈ Furry.nonFurry, (c.sign : ℂ) * contractionValue₂ { P with ε := ε } c.rep
          (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) +
        ∑ c : CtClass, contractionValue₂ { P with ε := ε } c.rep
          (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ)) :=
    fun ε => by
      rw [← onePIFunction₂_five_sub_four_eq_classes { P with ε := ε } hmom (fun _ => i)
        (fun _ => j) (fun _ => μ)]
      rfl
  have h₁ : ∀ c ∈ Furry.nonFurry, Tendsto (fun ε => (c.sign : ℂ) * contractionValue₂
      { P with ε := ε } c.rep (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
      (fun _ => j) (fun _ => μ)) (𝓝[>] 0) (𝓝 ((c.sign : ℂ) * classLimitV c P p p' μ i j)) :=
    fun c hc => (tendsto_nhds_limUnder (VertexLimit.exists_tendsto_contractionValue₂_nonFurry hc
      P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ (pOut := fun _ => p') (pIn := fun _ => p)
      (kIn := fun _ => p' - p) hmom hp hp' hq (fun _ => i) (fun _ => j)
      (fun _ => μ))).const_mul _
  have h₂ : ∀ c ∈ (Finset.univ : Finset CtClass), Tendsto (fun ε => contractionValue₂
      { P with ε := ε } c.rep (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
      (fun _ => j) (fun _ => μ)) (𝓝[>] 0) (𝓝 (ctLimitV c P p p' μ i j)) :=
    fun c _ => tendsto_nhds_limUnder (CountertermLimit.exists_tendsto_contractionValue₂_ctClass c
      P hm hmγ hΛ (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) hmom hp hp'
      hp0 hp0' hq (fun _ => i) (fun _ => j) (fun _ => μ))
  have hT := ((tendsto_finsetSum _ h₁).add (tendsto_finsetSum _ h₂)).const_mul (1 / I)
  have hT' := hT.congr' (Eventually.of_forall fun ε => (e ε).symm)
  rw [tendsto_nhds_unique (hV μ i j) hT']
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sum_apply, smul_eq_mul, one_mul]

/-- **Covariance of the order-`e⁵` vertex limit under `L`, with the external momenta moved.**
For `m, m_γ, Λ > 0`, `M₁, M₂ ≥ m` with the Pauli–Villars conditions, any counterterms, on-shell
`p, p'` with `q² ≥ 0`, `p, p', L p, L p'` of positive energy, and the limits `V` at `(p', p)` and
`W` at `(L p', L p)`: `S W^μ T = L^μ_ν V^ν`. -/
theorem conj_vertexLimit_map (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (h : IsSpinLift L S T)
    {p' p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp0 : 0 < p 0) (hp0' : 0 < p' 0) (hLp0 : 0 < (L *ᵥ p) 0) (hLp0' : 0 < (L *ᵥ p') 0)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : IsVertexOrderFiveLimit P p' p V) (hW : IsVertexOrderFiveLimit P (L *ᵥ p') (L *ᵥ p) W)
    (μ : Fin 4) : S * W μ * T = vecAct L V μ := by
  have hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp
  have hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp'
  have hqL : 0 ≤ Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p) := by
    rw [← Matrix.mulVec_sub, h.dot_mulVec]; exact hq
  rw [eq_classLimits_of_isVertexOrderFiveLimit P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hpL hpL' hLp0 hLp0'
    hqL hW, eq_classLimits_of_isVertexOrderFiveLimit P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp hp' hp0 hp0'
    hq hV]
  dsimp only
  rw [Matrix.mul_smul, Matrix.smul_mul, vecAct_smul]
  congr 1
  rw [Matrix.mul_add, Matrix.add_mul, vecAct_add]
  congr 1
  · rw [Matrix.mul_sum, Matrix.sum_mul, VertexCovariance.vecAct_finset_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    by_cases hVP : c = .VP
    · subst hVP
      exact classLimitV_VP_map P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ h hp hp' hq μ
    · exact classLimitV_map (VertexLimit.mem_openClasses_of_mem_nonFurry c hc hVP) P hm hmγ hΛ h
        hp hp' hq μ
  · rw [Matrix.mul_sum, Matrix.sum_mul, VertexCovariance.vecAct_finset_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    exact ctLimitV_map c P hm hmγ hΛ h hp hp' hp0 hp0' hLp0 hLp0' hq μ

/-! ### The trace projectors under `L` -/

theorem trace_conj (h : IsSpinLift L S T) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    trace (S * X * T) = trace X := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h.mul_eq_one', Matrix.one_mul]

theorem mul_four_mul (h : IsSpinLift L S T) (A B C D : Matrix (Fin 4) (Fin 4) ℂ) :
    S * (A * B * C * D) * T = (S * A * T) * (S * B * T) * (S * C * T) * (S * D * T) := by
  rw [h.mul_mul_mul, h.mul_mul_mul, h.mul_mul_mul]

theorem mul_three_mul (h : IsSpinLift L S T) (A B C : Matrix (Fin 4) (Fin 4) ℂ) :
    S * (A * B * C) * T = (S * A * T) * (S * B * T) * (S * C * T) := by
  rw [h.mul_mul_mul, h.mul_mul_mul]

theorem mul_massSlash_mul (h : IsSpinLift L S T) (m : ℝ) (u : Fin 4 → ℝ) :
    S * ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - slash (L *ᵥ u)) * T =
      (m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - slash u :=
  h.mul_electronNumerator_mul m u

/-- `S γ_μ T = L_μ^ν γ_ν` in lowered form: `∑_μ L^μ_ν (S γ_μ T) = γ_ν`. -/
theorem sum_mul_gammaLower_mul (h : IsSpinLift L S T) (ν : Fin 4) :
    ∑ μ, ((L μ ν : ℝ) : ℂ) • (S * gammaLower μ * T) = gammaLower ν := by
  have hg : ∀ μ, S * gammaLower μ * T =
      ∑ σ, ((∑ ρ, Minkowski.metric μ ρ * L ρ σ : ℝ) : ℂ) • gamma σ := by
    intro μ
    simp only [gammaLower, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      h.mul_gamma_mul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← Finset.sum_smul]
    push_cast
    rfl
  simp only [hg, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  unfold gammaLower
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rw [← h.lorentz_right ν σ]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem traceGammaProj_map (h : IsSpinLift L S T) (m : ℝ) (p' p : Fin 4 → ℝ)
    {V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hW : ∀ μ, S * W μ * T = vecAct L V μ) :
    traceGammaProj m (L *ᵥ p') (L *ᵥ p) W = traceGammaProj m p' p V := by
  unfold traceGammaProj
  have e : ∀ μ, trace (((m : ℂ) • 1 - slash (L *ᵥ p')) * W μ * ((m : ℂ) • 1 - slash (L *ᵥ p)) *
      gammaLower μ) = ∑ ν, ((L μ ν : ℝ) : ℂ) *
        trace (((m : ℂ) • 1 - slash p') * V ν * ((m : ℂ) • 1 - slash p) *
          (S * gammaLower μ * T)) := by
    intro μ
    rw [← trace_conj h, mul_four_mul h, mul_massSlash_mul h, mul_massSlash_mul h, hW μ]
    simp only [vecAct, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← sum_mul_gammaLower_mul h ν]
  simp only [Finset.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]

theorem traceVecProj_map (h : IsSpinLift L S T) (m : ℝ) (p' p a : Fin 4 → ℝ)
    {V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hW : ∀ μ, S * W μ * T = vecAct L V μ) :
    traceVecProj m (L *ᵥ p') (L *ᵥ p) (L *ᵥ a) W = traceVecProj m p' p a V := by
  unfold traceVecProj
  have e : ∀ μ, trace (((m : ℂ) • 1 - slash (L *ᵥ p')) * W μ * ((m : ℂ) • 1 - slash (L *ᵥ p))) =
      ∑ ν, ((L μ ν : ℝ) : ℂ) * trace (((m : ℂ) • 1 - slash p') * V ν * ((m : ℂ) • 1 - slash p)) := by
    intro μ
    rw [← trace_conj h, mul_three_mul h, mul_massSlash_mul h, mul_massSlash_mul h, hW μ]
    simp only [vecAct, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  simp only [e, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← h.lower_mulVec_contract a ν]
  push_cast
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun μ _ => by ring

/-- **The Pauli projector is invariant**: if `S W^μ T = L^μ_ν V^ν`, then
`P₂(L p', L p; W) = P₂(p', p; V)`. -/
theorem formFactorProj₂_map (h : IsSpinLift L S T) (e m : ℝ) (p' p : Fin 4 → ℝ)
    {V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hW : ∀ μ, S * W μ * T = vecAct L V μ) :
    QED.OneLoop.formFactorProj₂ e m (L *ᵥ p') (L *ᵥ p) W =
      QED.OneLoop.formFactorProj₂ e m p' p V := by
  have hK : L *ᵥ p' + L *ᵥ p = L *ᵥ (p' + p) := (Matrix.mulVec_add _ _ _).symm
  have hq : Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p) =
      Minkowski.dot (p' - p) (p' - p) := by
    rw [← Matrix.mulVec_sub, h.dot_mulVec]
  unfold QED.OneLoop.formFactorProj₂
  rw [hK, hq, traceGammaProj_map h m p' p hW, traceVecProj_map h m p' p (p' + p) hW]

/-- **The projector onto `F₁` is invariant.** -/
theorem formFactorProj₁_map (h : IsSpinLift L S T) (e m : ℝ) (p' p : Fin 4 → ℝ)
    {V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hW : ∀ μ, S * W μ * T = vecAct L V μ) :
    QED.OneLoop.formFactorProj₁ e m (L *ᵥ p') (L *ᵥ p) W =
      QED.OneLoop.formFactorProj₁ e m p' p V := by
  have hK : L *ᵥ p' + L *ᵥ p = L *ᵥ (p' + p) := (Matrix.mulVec_add _ _ _).symm
  have hq : Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p) =
      Minkowski.dot (p' - p) (p' - p) := by
    rw [← Matrix.mulVec_sub, h.dot_mulVec]
  unfold QED.OneLoop.formFactorProj₁
  rw [hK, hq, traceGammaProj_map h m p' p hW, traceVecProj_map h m p' p (p' + p) hW]

/-- **The Pauli projector of the vertex limit is invariant under `L`**, under the hypotheses of
`conj_vertexLimit_map`. -/
theorem formFactorProj₂_vertexLimit_map (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (h : IsSpinLift L S T)
    {p' p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp0 : 0 < p 0) (hp0' : 0 < p' 0) (hLp0 : 0 < (L *ᵥ p) 0) (hLp0' : 0 < (L *ᵥ p') 0)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : IsVertexOrderFiveLimit P p' p V) (hW : IsVertexOrderFiveLimit P (L *ᵥ p') (L *ᵥ p) W)
    (e : ℝ) :
    QED.OneLoop.formFactorProj₂ e P.m (L *ᵥ p') (L *ᵥ p) W =
      QED.OneLoop.formFactorProj₂ e P.m p' p V :=
  formFactorProj₂_map h e P.m p' p fun μ =>
    conj_vertexLimit_map P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ h hp hp' hp0 hp0' hLp0 hLp0' hq hV hW μ

end QED.TwoLoop.PauliZero

end
