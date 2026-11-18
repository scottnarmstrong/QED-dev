/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ReflCovarianceParam
public import QED.TwoLoop.LimitCovarianceVP

/-!
# Covariance of the class limits under Lorentz maps that move the external momenta

Part of obligations O2-20 and O2-21 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4). For a real `L`
with a spinor lift `(S, T)` (`QED.TwoLoop.LimitCovariance.IsSpinLift`; `L` may be improper and
time-reversing, e.g. the reflection `R_K`) and on-shell `p, p'` with `q² ≥ 0`, the vertex
`W_c(p, p')` of `ε → 0⁺` limits of the class `c` (`QED.TwoLoop.LimitCovariance.classLimitV`)
satisfies

`S W_c(L p, L p')^μ T = L^μ_ν W_c(p, p')^ν`

for the six open-line classes (`classLimitV_map`) and for `VP` (`classLimitV_VP_map`). No
positive-energy hypothesis is used: the limits exist at `(L p, L p')` because the on-shell
conditions and `q²` are `L`-invariant.

The numerators transform with the external data (`classNumM_map`, `vpPieceM_map`); the parametric
values transform by `QED.TwoLoop.ReflCovariance.conj_eq_vecAct_of_paramValue`.
-/

@[expose] public section

open Complex Matrix Filter Topology
open scoped Real

namespace QED.TwoLoop.ReflCovariance

open QED.Dirac QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
  QED.TwoLoop.ClassLimit
open QED.Integration.TwoLoop (LoopQuartic RefinedBound castLoopMatrix class5LoopMatrixPV lineDenom
  lineMomentum)

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

theorem dot_mulVec_sub (h : IsSpinLift L S T) (p p' : Fin 4 → ℝ) :
    Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p) = Minkowski.dot (p' - p) (p' - p) := by
  rw [← Matrix.mulVec_sub, h.dot_mulVec]

/-! ### The open-line classes -/

theorem extMomenta_map (c : Class5) (p p' : Fin 4 → ℝ) (i : Fin 6) :
    extMomenta c (L *ᵥ p) (L *ᵥ p') i = L *ᵥ extMomenta c p p' i := by
  cases c <;> fin_cases i <;>
    simp [extMomenta, QED.Integration.TwoLoop.classLXMomenta,
      QED.Integration.TwoLoop.classCpSpMomenta, QED.Integration.TwoLoop.classCmSmMomenta,
      QED.Integration.TwoLoop.classVPMomenta]

theorem pvMomentaE_map (c : Class5) (p p' : Fin 4 → ℝ) :
    pvMomentaE c (L *ᵥ p) (L *ᵥ p') = fun i => L *ᵥ pvMomentaE c p p' i :=
  funext fun _ => extMomenta_map c p p' _

theorem classMomE_map (c : Class5) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line c.rep) :
    classMomE c (L *ᵥ p) (L *ᵥ p') (loopAct L ℓ) f = L *ᵥ classMomE c p p' ℓ f := by
  unfold classMomE
  rw [show extMomenta c (L *ᵥ p) (L *ᵥ p') = fun i => L *ᵥ extMomenta c p p' i from
    funext (extMomenta_map c p p')]
  exact lineMomentum_map _ _ _ ℓ

theorem classNumM_map_of_chain {c : Class5} (σ : Equiv.Perm (Fin 5))
    (line : Fin 4 → FermionLine c.rep)
    (heq : ∀ (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)
      (ℓ : Fin 2 → Fin 4 → ℝ),
      classNumeratorE c P pOut pIn kIn αOut βIn μ ℓ = (I * P.e) ^ 5 * (1 / I) ^ 4 *
        chainNum P σ (fun i => electronNumerator P.m
          (classMomE c (pIn 0) (pOut 0) ℓ (.inl (line i)))) (μ 0) (αOut 0) (βIn 0))
    (h : IsSpinLift L S T) (p p' : Fin 4 → ℝ) (P : Params) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * classNumM c P (L *ᵥ p) (L *ᵥ p') μ (loopAct L ℓ) * T =
      vecAct L (fun ν => classNumM c P p p' ν ℓ) μ := by
  have hM : ∀ (q q' : Fin 4 → ℝ) ν ℓ', classNumM c P q q' ν ℓ' = ((I * P.e) ^ 5 * (1 / I) ^ 4) •
      chainNum P σ (fun i => electronNumerator P.m (classMomE c q q' ℓ' (.inl (line i)))) ν := by
    intro q q' ν ℓ'
    ext i j
    simp only [classNumM, Matrix.of_apply, heq, Matrix.smul_apply, smul_eq_mul]
  simp only [hM, Matrix.mul_smul, Matrix.smul_mul, mul_chainNum_mul h, classMomE_map,
    h.mul_electronNumerator_mul]
  rw [vecAct_smul L _ _ μ]

/-- **Covariance of the open-class numerators with the external data transformed**:
`S N^μ(L p, L p'; L ℓ) T = L^μ_ν N^ν(p, p'; ℓ)`. -/
theorem classNumM_map {c : Class5} (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses)
    (h : IsSpinLift L S T) (p p' : Fin 4 → ℝ) (P : Params) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * classNumM c P (L *ᵥ p) (L *ᵥ p') μ (loopAct L ℓ) * T =
      vecAct L (fun ν => classNumM c P p p' ν ℓ) μ := by
  simp only [QED.TwoLoop.ClassIntegrable.openClasses, Finset.mem_insert,
    Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact classNumM_map_of_chain permL lineL chain_L h p p' P μ ℓ
  · exact classNumM_map_of_chain permX lineX chain_X h p p' P μ ℓ
  · exact classNumM_map_of_chain permCp lineCp chain_Cp h p p' P μ ℓ
  · exact classNumM_map_of_chain permCm lineCm chain_Cm h p p' P μ ℓ
  · exact classNumM_map_of_chain permSp lineSp chain_Sp h p p' P μ ℓ
  · exact classNumM_map_of_chain permSm lineSm chain_Sm h p p' P μ ℓ

/-- The limit of an open class as the parametric value of its numerator, at any on-shell pair. -/
theorem exists_quartic_classLimitV {c : Class5} (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses)
    (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (μ i j : Fin 4) :
    ∃ Q : LoopQuartic, Q.eval = (fun ℓ => (twoLoopNorm • classNumM c P p p' μ ℓ) i j) ∧
      MeasureTheory.IntegrableOn (paramIntegrand Q (castLoopMatrix (class5LoopMatrixPV c))
        (pvMomentaE c p p') (pvMasses P) 0) (QED.Integration.Feynman.simplexSet 7) ∧
      classLimitV c P p p' μ i j = -((π : ℂ) ^ 4) * ∫ x in QED.Integration.Feynman.simplexSet 7,
        paramIntegrand Q (castLoopMatrix (class5LoopMatrixPV c)) (pvMomentaE c p p')
          (pvMasses P) 0 x := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  obtain ⟨Q, hQ, hI, hT⟩ := tendsto_contractionValue₂_open hc P hm hmγ hΛ
    (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) hmom hp hp' hq
    (fun _ => i) (fun _ => j) (fun _ => μ)
  refine ⟨Q, ?_, hI, hT.limUnder_eq⟩
  rw [hQ]
  funext ℓ
  simp only [Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul]

/-- **Covariance of the open-class limits under `L`, with the external momenta moved.** -/
theorem classLimitV_map {c : Class5} (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses)
    (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (h : IsSpinLift L S T)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (μ : Fin 4) :
    S * classLimitV c P (L *ᵥ p) (L *ᵥ p') μ * T = vecAct L (classLimitV c P p p') μ := by
  have hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp
  have hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp'
  have hqL : 0 ≤ Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p) := by
    rw [dot_mulVec_sub h]; exact hq
  refine conj_eq_vecAct_of_paramValue (openData hc P hm hmγ hΛ hp hp' hq) h
    (pvMomentaE c (L *ᵥ p) (L *ᵥ p')) (pvMomentaE_map c p p')
    (fun μ ℓ => twoLoopNorm • classNumM c P p p' μ ℓ)
    (fun μ ℓ => twoLoopNorm • classNumM c P (L *ᵥ p) (L *ᵥ p') μ ℓ) (fun μ ℓ => ?_) _ _
    (fun μ i j => ?_) (fun μ i j => ?_) μ
  · rw [Matrix.mul_smul, Matrix.smul_mul, classNumM_map hc h, vecAct_smul]
  · obtain ⟨Q, hQ, -, hv⟩ := exists_quartic_classLimitV hc P hm hmγ hΛ hp hp' hq μ i j
    refine ⟨Q, hQ, ?_, hv⟩
    have hF : (fun ℓ => (twoLoopNorm • classNumM c P p p' μ ℓ) i j) =
        fun ℓ => twoLoopNorm * classNumeratorE c P (fun _ => p') (fun _ => p)
          (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) ℓ := by
      funext ℓ
      simp only [Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul]
    rw [hF]
    exact (QED.TwoLoop.ClassIntegrable.refinedBound_classNumeratorE hc P (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ)).const_mul _
  · exact exists_quartic_classLimitV hc P hm hmγ hΛ hpL hpL' hqL μ i j

/-! ### The vacuum-polarization class -/

theorem vpChainM_map (h : IsSpinLift L S T) (P : Params) (p kext k : Fin 4 → ℝ)
    (X : Fin 4 → Fin 4 → ℂ) (μ : Fin 4) :
    S * vpChainM P (L *ᵥ p) (L *ᵥ kext) (L *ᵥ k) (upperAct L X) μ * T =
      vecAct L (vpChainM P p kext k X) μ := by
  have e1 : L *ᵥ p + L *ᵥ kext - L *ᵥ k = L *ᵥ (p + kext - k) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_add]
  have e2 : L *ᵥ p - L *ᵥ k = L *ᵥ (p - k) := by rw [Matrix.mulVec_sub]
  simp only [vpChainM, h.mul_chain_mul, tensorAct_lowered h, e1, e2, h.mul_electronNumerator_mul]
  rfl

theorem vpE0M_map (h : IsSpinLift L S T) (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * vpE0M P (L *ᵥ p) (L *ᵥ p') μ (loopAct L ℓ) * T =
      vecAct L (fun ν => vpE0M P p p' ν ℓ) μ := by
  have hk : L *ᵥ p' - L *ᵥ p = L *ᵥ (p' - p) := by rw [Matrix.mulVec_sub]
  have e : loopAct L ℓ 0 + -loopAct L ℓ 1 = L *ᵥ (ℓ 0 + -ℓ 1) := by
    simp [loopAct, Matrix.mulVec_add, Matrix.mulVec_neg]
  have hX : traceT (electronNumerator 0 (loopAct L ℓ 0))
      (electronNumerator 0 (loopAct L ℓ 0 + -loopAct L ℓ 1)) =
      upperAct L (traceT (electronNumerator 0 (ℓ 0)) (electronNumerator 0 (ℓ 0 + -ℓ 1))) := by
    funext a b
    rw [e, show loopAct L ℓ 0 = L *ᵥ ℓ 0 from rfl, electronNumerator_mulVec h,
      electronNumerator_mulVec h, traceT_conj h]
  simp only [vpE0M_eq]
  rw [hX, neg_loopAct_one, hk]
  simp only [Matrix.mul_smul, Matrix.smul_mul, vpChainM_map h P]
  rw [vecAct_smul]

theorem vpE2M_map (h : IsSpinLift L S T) (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * vpE2M P (L *ᵥ p) (L *ᵥ p') μ (loopAct L ℓ) * T =
      vecAct L (fun ν => vpE2M P p p' ν ℓ) μ := by
  have hk : L *ᵥ p' - L *ᵥ p = L *ᵥ (p' - p) := by rw [Matrix.mulVec_sub]
  have hX : traceT 1 1 = upperAct L (traceT 1 1) := by
    funext a b
    rw [← traceT_conj h, Matrix.mul_one, h.mul_eq_one']
  have hX' : vpChainM P (L *ᵥ p) (L *ᵥ p' - L *ᵥ p) (-loopAct L ℓ 1) (traceT 1 1) =
      vpChainM P (L *ᵥ p) (L *ᵥ (p' - p)) (L *ᵥ (-ℓ 1)) (upperAct L (traceT 1 1)) := by
    rw [neg_loopAct_one, ← hX, hk]
  simp only [vpE2M_eq, hX', Matrix.mul_smul, Matrix.smul_mul, vpChainM_map h P]
  rw [vecAct_smul]

theorem classVPMomenta_map (p p' : Fin 4 → ℝ) (i : Fin 6) :
    QED.Integration.TwoLoop.classVPMomenta (L *ᵥ p) (L *ᵥ p') i =
      L *ᵥ QED.Integration.TwoLoop.classVPMomenta p p' i := by
  fin_cases i <;> simp [QED.Integration.TwoLoop.classVPMomenta]

theorem vpShapeMomenta_map (t : Fin 4) (p p' : Fin 4 → ℝ) :
    vpShapeMomenta t (L *ᵥ p) (L *ᵥ p') = fun i => L *ᵥ vpShapeMomenta t p p' i :=
  funext fun _ => classVPMomenta_map p p' _

theorem vpCoeff2_map (h : IsSpinLift L S T) (P : Params) (p p' : Fin 4 → ℝ) (j : Fin 5)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    vpCoeff2 P (L *ᵥ p) (L *ᵥ p') j (loopAct L ℓ) = vpCoeff2 P p p' j ℓ := by
  simp only [vpCoeff2, vpShapeMomenta_map, lineDenom_map h]

/-- **Covariance of the piece numerators of `VP` with the external data transformed.** -/
theorem vpPieceM_map (h : IsSpinLift L S T) (P : Params) (p p' : Fin 4 → ℝ) (j : Fin 5)
    (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * vpPieceM P (L *ᵥ p) (L *ᵥ p') j μ (loopAct L ℓ) * T =
      vecAct L (fun ν => vpPieceM P p p' j ν ℓ) μ := by
  simp only [vpPieceM_eq, vpCoeff2_map h P p p', Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, vpE0M_map h P p p', vpE2M_map h P p p']
  rw [vecAct_add, vecAct_smul, vecAct_smul]

/-- The limit of `VP` as a sum of five parametric values, at any on-shell pair. -/
theorem exists_quartic_classLimitV_VP (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) :
    ∃ Q : Fin 4 → Fin 4 → Fin 4 → Fin 5 → LoopQuartic,
      (∀ μ i j k, (Q μ i j k).eval = fun ℓ => vpPieceM P p p' k μ ℓ i j) ∧
      (∀ μ i j k, MeasureTheory.IntegrableOn (paramIntegrand (Q μ i j k)
        (castLoopMatrix (vpShapeMatrix (vpPieceShape k))) (vpShapeMomenta (vpPieceShape k) p p')
        (vpShapeMasses P (vpPieceShape k)) 0) (QED.Integration.Feynman.simplexSet 9)) ∧
      classLimitV .VP P p p' = fun μ => ∑ k ∈ Finset.univ, (1 : ℂ) • Matrix.of fun i j =>
        -((π : ℂ) ^ 4) * ∫ x in QED.Integration.Feynman.simplexSet 9, paramIntegrand (Q μ i j k)
          (castLoopMatrix (vpShapeMatrix (vpPieceShape k)))
          (vpShapeMomenta (vpPieceShape k) p p') (vpShapeMasses P (vpPieceShape k)) 0 x := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hVP := fun (μ α β : Fin 4) => tendsto_contractionValue₂_VP P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂
    (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) hmom hp hp' hq
    (fun _ => α) (fun _ => β) (fun _ => μ)
  choose Q hQ hI hT using hVP
  refine ⟨Q, fun μ i j k => ?_, hI, ?_⟩
  · rw [hQ]
    funext ℓ
    simp only [vpPieceM, Matrix.of_apply]
  · funext μ
    ext α β
    simp only [classLimitV, Matrix.of_apply, (hT μ α β).limUnder_eq, one_smul, Matrix.sum_apply]

/-- **Covariance of the limit of `VP` under `L`, with the external momenta moved.** -/
theorem classLimitV_VP_map (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (h : IsSpinLift L S T)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (μ : Fin 4) :
    S * classLimitV .VP P (L *ᵥ p) (L *ᵥ p') μ * T = vecAct L (classLimitV .VP P p p') μ := by
  have h₁ : P.m ^ 2 ≤ P.M₁ ^ 2 := pow_le_pow_left₀ hm.le hM₁ 2
  have h₂ : P.m ^ 2 ≤ P.M₂ ^ 2 := pow_le_pow_left₀ hm.le hM₂ 2
  have hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp
  have hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp'
  have hqL : 0 ≤ Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p) := by
    rw [dot_mulVec_sub h]; exact hq
  obtain ⟨Q, hQ, -, hW⟩ := exists_quartic_classLimitV_VP P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp hp' hq
  obtain ⟨Q₂, hQ₂, hI₂, hW₂⟩ :=
    exists_quartic_classLimitV_VP P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hpL hpL' hqL
  rw [hW, hW₂, VertexCovariance.vecAct_finset_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  exact conj_eq_vecAct_of_paramValue (vpData P hmγ hΛ hm h₁ h₂ hp hp' hq k) h
    (vpShapeMomenta (vpPieceShape k) (L *ᵥ p) (L *ᵥ p')) (vpShapeMomenta_map _ p p')
    (fun μ ℓ => vpPieceM P p p' k μ ℓ) (fun μ ℓ => vpPieceM P (L *ᵥ p) (L *ᵥ p') k μ ℓ)
    (fun μ ℓ => vpPieceM_map h P p p' k μ ℓ) _ _
    (fun μ i j => ⟨Q μ i j k, hQ μ i j k, by
      have hF : (fun ℓ => vpPieceM P p p' k μ ℓ i j) = vpPieceNumer P (fun _ => p') (fun _ => p)
          (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) k := by
        funext ℓ
        simp only [vpPieceM, Matrix.of_apply]
      rw [hF]
      exact refinedBound_vpPieceNumer P _ _ _ _ _ _ k, rfl⟩)
    (fun μ i j => ⟨Q₂ μ i j k, hQ₂ μ i j k, hI₂ μ i j k, rfl⟩) μ

end QED.TwoLoop.ReflCovariance

end
