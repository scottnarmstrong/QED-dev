/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitLimit
public import QED.TwoLoop.ReflCovarianceClasses

/-!
# Two-loop vertex units with a free mass on each photon line: covariance

Helper level for set (c) (stage L1). The two-mass units of `QED/ChainProof/SetCUnitLimit.lean`
are covariant exactly as the Phase 4 class limits
(`QED.TwoLoop.LimitCovariance.isLittleGroupCovariant_classLimitV`,
`QED.TwoLoop.ReflCovariance.classLimitV_map`): the covariance argument is a statement about
parametric values (`IsParamValue`, `conj_eq_vecAct_of_paramValue`), which do not see the masses
beyond the positivity of `V`.

* `unitData`: the parametric data of the unit at masses `unitMasses m a A b B ≥ μ₀`;
* `isParamValue_unitLimitV`: each entry of the unit limit is the parametric value of the numerator;
* **`isLittleGroupCovariant_unitLimitV`**: covariance under the little group of `(p, p')`;
* **`unitLimitV_map`**: `S W^μ T = L^μ_ν V^ν` for the unit limits `V` at `(p, p')` and `W` at
  `(L p, L p')`, every spinor-lifted `L` (the form used by `SetCCovLink`).
-/

@[expose] public section

open Complex Matrix Filter Topology
open scoped Real

namespace QED.ChainProof.SetCUnit

open QED.Dirac QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge
open QED.TwoLoop.ClassIntegrable QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.ReflCovariance
open QED.Integration.TwoLoop (LoopQuartic RefinedBound castLoopMatrix class5LoopMatrixPV)

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

/-- The parametric data of the two-mass unit of an open-line class. -/
noncomputable def unitData {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) : ParamData where
  m := 7
  α := castLoopMatrix (class5LoopMatrixPV c)
  p := pvMomentaE c p p'
  M := unitMasses P.m a A b B
  E := {0, 1, 2, 3}
  hm := by norm_num
  hcrit := noSubdivergenceRefined_unit hc
  c := unitConst P.m μ₀
  hc := unitConst_pos hm hμ₀
  hV := fun _ hz hz1 hU => symanzikV_unit_ge hc hμ₀ hM hp hp' hq hz hz1 hU

theorem unitNum_eq_classNumM (c : Class5) (P : Params) (p p' : Fin 4 → ℝ) (μ i j : Fin 4) :
    unitNum c P p p' μ i j = fun ℓ => (twoLoopNorm • classNumM c P p p' μ ℓ) i j := by
  funext ℓ
  simp only [unitNum, Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul]

section Cov

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {μ₀ a A b B : ℝ}
  (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B) {p p' : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hc hm hμ₀ hM hp hp' hq

/-- The unit limit at `(p, p')` as a quartic parametric integral, in the form consumed by
`conj_eq_vecAct_of_paramValue`. -/
theorem exists_quartic_unitLimitV (μ i j : Fin 4) :
    ∃ Q : LoopQuartic, Q.eval = (fun ℓ => (twoLoopNorm • classNumM c P p p' μ ℓ) i j) ∧
      MeasureTheory.IntegrableOn (paramIntegrand Q (castLoopMatrix (class5LoopMatrixPV c))
        (pvMomentaE c p p') (unitMasses P.m a A b B) 0) (QED.Integration.Feynman.simplexSet 7) ∧
      unitLimitV c P (unitMasses P.m a A b B) p p' μ i j =
        -((π : ℂ) ^ 4) * ∫ x in QED.Integration.Feynman.simplexSet 7,
          paramIntegrand Q (castLoopMatrix (class5LoopMatrixPV c)) (pvMomentaE c p p')
            (unitMasses P.m a A b B) 0 x := by
  obtain ⟨Q, hQ⟩ := exists_unitQuartic hc P p p' μ i j
  refine ⟨Q, hQ.trans (unitNum_eq_classNumM c P p p' μ i j), ?_, ?_⟩
  · exact (tendsto_unitValue hc P hm hμ₀ hM hp hp' hq μ i j hQ).1
  · exact unitLimitV_eq hc P hm hμ₀ hM hp hp' hq μ i j hQ

/-- Each entry of the unit limit is the parametric value of its numerator. -/
theorem isParamValue_unitLimitV (μ i j : Fin 4) :
    IsParamValue (unitData hc P hm hμ₀ hM hp hp' hq)
      (fun ℓ => (twoLoopNorm • classNumM c P p p' μ ℓ) i j)
      (unitLimitV c P (unitMasses P.m a A b B) p p' μ i j) := by
  obtain ⟨Q, hQ, -, hv⟩ := exists_quartic_unitLimitV hc P hm hμ₀ hM hp hp' hq μ i j
  refine ⟨Q, hQ, ?_, hv⟩
  rw [← unitNum_eq_classNumM]
  exact refinedBound_unitNum hc P p p' μ i j

/-- **Little-group covariance of the two-mass unit limits.** -/
theorem isLittleGroupCovariant_unitLimitV :
    IsLittleGroupCovariant p' p (unitLimitV c P (unitMasses P.m a A b B) p p') :=
  isLittleGroupCovariant_of_paramValue (unitData hc P hm hμ₀ hM hp hp' hq)
    (fun L S T _ hLp hLp' i => mulVec_extMomenta hLp hLp' c _)
    (fun μ ℓ => twoLoopNorm • classNumM c P p p' μ ℓ)
    (fun L S T h hLp hLp' μ ℓ => by
      rw [Matrix.mul_smul, Matrix.smul_mul, classNumM_cov hc h hLp hLp', vecAct_smul]) _
    fun μ i j => isParamValue_unitLimitV hc P hm hμ₀ hM hp hp' hq μ i j

/-- **Covariance of the two-mass unit limits with the external momenta moved**:
`S W^μ T = L^μ_ν V^ν`, `V` the unit limit at `(p, p')`, `W` at `(L p, L p')`, the line masses
unchanged. -/
theorem unitLimitV_map (h : IsSpinLift L S T) (μ : Fin 4) :
    S * unitLimitV c P (unitMasses P.m a A b B) (L *ᵥ p) (L *ᵥ p') μ * T =
      vecAct L (unitLimitV c P (unitMasses P.m a A b B) p p') μ := by
  have hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp
  have hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp'
  have hqL : 0 ≤ Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p) := by
    rw [dot_mulVec_sub h]; exact hq
  exact conj_eq_vecAct_of_paramValue (unitData hc P hm hμ₀ hM hp hp' hq) h
    (pvMomentaE c (L *ᵥ p) (L *ᵥ p')) (pvMomentaE_map c p p')
    (fun μ ℓ => twoLoopNorm • classNumM c P p p' μ ℓ)
    (fun μ ℓ => twoLoopNorm • classNumM c P (L *ᵥ p) (L *ᵥ p') μ ℓ)
    (fun μ ℓ => by rw [Matrix.mul_smul, Matrix.smul_mul, classNumM_map hc h, vecAct_smul]) _ _
    (fun μ i j => isParamValue_unitLimitV hc P hm hμ₀ hM hp hp' hq μ i j)
    (fun μ i j => exists_quartic_unitLimitV hc P hm hμ₀ hM hpL hpL' hqL μ i j) μ

end Cov

end QED.ChainProof.SetCUnit

end
