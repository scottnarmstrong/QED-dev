/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ReflCovarianceClasses
public import QED.GradedProof.V5ZeroLimVP

/-!
# Covariance of the limit of the vacuum-polarization class, for small regulator masses

Helper level for V5Zero, part A. With the hypothesis `M₁, M₂ ≥ m` replaced by
`0 < m₀ ≤ m, M₁, M₂` for some `m₀`:

* `vpData`: the parametric data of the five pieces of `VP` (as
  `QED.TwoLoop.LimitCovariance.vpData`, with lower bound `vpLowerBound P m₀` for `V`);
* `exists_quartic_classLimitV_VP`: the limit vertex `classLimitV .VP P p p'` is a sum of five
  parametric values (as `QED.TwoLoop.ReflCovariance.exists_quartic_classLimitV_VP`);
* `classLimitV_VP_map`: `S W_VP(L p, L p')^μ T = L^μ_ν W_VP(p, p')^ν` (as
  `QED.TwoLoop.ReflCovariance.classLimitV_VP_map`);
* `isLittleGroupCovariant_classLimitV_VP` (as
  `QED.TwoLoop.LimitCovariance.isLittleGroupCovariant_classLimitV_VP`).

The proofs are those of the originals, with the relaxed limit
`QED.GradedProof.V5Zero.Lim.tendsto_contractionValue₂_VP` and the relaxed lower bound
`QED.GradedProof.V5Zero.Lim.symanzikV_vpShape_ge_relaxed`.
-/

@[expose] public section

open Complex Matrix Filter Topology
open scoped Real

namespace QED.GradedProof.V5Zero.Lim

open QED.Dirac QED.WickModel QED.TwoLoop QED.TwoLoop.Enumeration QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance hiding vpData isLittleGroupCovariant_classLimitV_VP
open QED.TwoLoop.ReflCovariance hiding exists_quartic_classLimitV_VP classLimitV_VP_map
open QED.TwoLoop.ClassLimit hiding tendsto_contractionValue₂_VP
  existsUnique_tendsto_contractionValue₂_VP
open QED.Integration.TwoLoop (LoopQuartic RefinedBound castLoopMatrix)

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

/-- **The parametric data of the `j`-th piece of `VP`, for small regulator masses**: as
`QED.TwoLoop.LimitCovariance.vpData`, for `0 < m₀ ≤ m, M₁, M₂`, with lower bound
`vpLowerBound P m₀` for `V`. -/
noncomputable def vpData (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀) (hm : m₀ ≤ P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : m₀ ≤ P.M₁) (hM₂ : m₀ ≤ P.M₂) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (j : Fin 5) : ParamData where
  m := 9
  α := castLoopMatrix (vpShapeMatrix (vpPieceShape j))
  p := vpShapeMomenta (vpPieceShape j) p p'
  M := vpShapeMasses P (vpPieceShape j)
  E := vpPieceLines j
  hm := by norm_num
  hcrit := noSubdivergenceRefined_vpPiece j
  c := vpLowerBound P m₀
  hc := vpLowerBound_pos P hm₀ hm hmγ hΛ
  hV := fun _ hz hz1 hU =>
    symanzikV_vpShape_ge_relaxed P hm₀ hm hM₁ hM₂ hmγ hΛ _ hp hp' hq hz hz1 hU

/-- **The limit of `VP` as a sum of five parametric values, at any on-shell pair**, for
`0 < m₀ ≤ m, M₁, M₂`. -/
theorem exists_quartic_classLimitV_VP (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀) (hm : m₀ ≤ P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : m₀ ≤ P.M₁) (hM₂ : m₀ ≤ P.M₂)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0)
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
  have hVP := fun (μ α β : Fin 4) => tendsto_contractionValue₂_VP P hm₀ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂
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

/-- **Covariance of the limit of `VP` under `L`, with the external momenta moved**, for
`0 < m₀ ≤ m, M₁, M₂`. -/
theorem classLimitV_VP_map (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀) (hm : m₀ ≤ P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : m₀ ≤ P.M₁) (hM₂ : m₀ ≤ P.M₂)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (h : IsSpinLift L S T)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (μ : Fin 4) :
    S * classLimitV .VP P (L *ᵥ p) (L *ᵥ p') μ * T = vecAct L (classLimitV .VP P p p') μ := by
  have hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp
  have hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp'
  have hqL : 0 ≤ Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p) := by
    rw [dot_mulVec_sub h]; exact hq
  obtain ⟨Q, hQ, -, hW⟩ := exists_quartic_classLimitV_VP P hm₀ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp hp' hq
  obtain ⟨Q₂, hQ₂, hI₂, hW₂⟩ :=
    exists_quartic_classLimitV_VP P hm₀ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hpL hpL' hqL
  rw [hW, hW₂, VertexCovariance.vecAct_finset_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  exact conj_eq_vecAct_of_paramValue (vpData P hm₀ hm hmγ hΛ hM₁ hM₂ hp hp' hq k) h
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

/-- **Little-group covariance of the limit of `VP`**, for `0 < m₀ ≤ m, M₁, M₂`. -/
theorem isLittleGroupCovariant_classLimitV_VP (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀) (hm : m₀ ≤ P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : m₀ ≤ P.M₁) (hM₂ : m₀ ≤ P.M₂)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) :
    IsLittleGroupCovariant p' p (classLimitV .VP P p p') := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hVP := fun (μ α β : Fin 4) => tendsto_contractionValue₂_VP P hm₀ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂
    (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) hmom hp hp' hq
    (fun _ => α) (fun _ => β) (fun _ => μ)
  choose Q hQ _ hT using hVP
  set D := vpData P hm₀ hm hmγ hΛ hM₁ hM₂ hp hp' hq with hD
  set W : Fin 5 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := fun j μ => Matrix.of fun α β =>
    -((π : ℂ) ^ 4) * ∫ x in QED.Integration.Feynman.simplexSet 9, paramIntegrand (Q μ α β j)
      (castLoopMatrix (vpShapeMatrix (vpPieceShape j)))
      (vpShapeMomenta (vpPieceShape j) p p') (vpShapeMasses P (vpPieceShape j)) 0 x with hW
  have hlim : classLimitV .VP P p p' = fun μ => ∑ j ∈ Finset.univ, (1 : ℂ) • W j μ := by
    funext μ
    ext α β
    simp only [classLimitV, Matrix.of_apply, (hT μ α β).limUnder_eq, one_smul, Matrix.sum_apply,
      hW]
  rw [hlim]
  refine VertexCovariance.isLittleGroupCovariant_sum _ _ fun j _ => ?_
  refine isLittleGroupCovariant_of_paramValue (D j)
    (fun L S T _ hLp hLp' i => mulVec_classVPMomenta hLp hLp' _)
    (fun μ ℓ => vpPieceM P p p' j μ ℓ) (fun L S T h hLp hLp' μ ℓ => vpPieceM_cov h P hLp hLp' j μ ℓ)
    (W j) fun μ α β => ?_
  have hF : (fun ℓ => vpPieceM P p p' j μ ℓ α β) = vpPieceNumer P (fun _ => p') (fun _ => p)
      (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) j := by
    funext ℓ
    simp only [vpPieceM, Matrix.of_apply]
  rw [hF]
  exact ⟨Q μ α β j, hQ μ α β j, refinedBound_vpPieceNumer P _ _ _ _ _ _ j, rfl⟩

end QED.GradedProof.V5Zero.Lim

end
