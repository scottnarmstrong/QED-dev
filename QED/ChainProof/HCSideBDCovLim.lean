/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCSideBDCovPieces

/-!
# The limits of the bubble–`δ₃` and `δ₃`–bubble classes as parametric values

Helper for the covariance of the limits of `QED.ChainProof.Enum.repBD s` and `repDB s`. At
admissible parameters and an on-shell pair `(p, p')` with `(p' - p)² ≥ 0`, the `ε → 0⁺` limit
of the joint integral of the value integrand (`QED.ChainProof.RepsInt.bdG`, `dbG`) is

`K₁ ∑ⱼ v₁ⱼ + K₂ ∑ⱼ v₂ⱼ + κ w₁ - κ w₂`,

with `v₁ⱼ`, `v₂ⱼ` the parametric values of the five `VP` piece numerators
(`QED.TwoLoop.LimitCovariance.vpPieceM`) with one, resp. two, extra photon lines (`ext1Data`,
`ext2Data`), and `w₁`, `w₂` those of the two longitudinal numerators (`bdL1N`, `bdL2N`,
resp. `dbL1N`, `dbL2N`; data `L1Data`, `L2Data`); the pieces with a factor `ε` vanish
(`bd_lim`, `db_lim`). The coefficients `K₁ = bdK1 P`, `K₂ = bdK2 P`, `κ = bdκL P` do not
depend on the external momenta.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Matrix
open scoped Real

namespace QED.ChainProof.HCSide

open QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit
  QED.ChainProof.Enum QED.ChainProof.RepsInt QED.TwoLoop.ClassIntegrable
open QED.TwoLoop.LimitCovariance QED.TwoLoop.ReflCovariance QED.Dirac QED.ChainProof.HCValue
open QED.TwoLoop.ClassLimit (vpPieceShape vpPieceLines vpPieceNumer vpEpsNumer vpDenomProd
  integrand_VP_eq isLoopPoly_vpPieceNumer refinedBound_vpPieceNumer isLoopPoly_vpEpsNumer
  refinedBound_vpEpsNumer twoLoopNorm)
open QED.Integration.TwoLoop (lineDenom castLoopMatrix class5LoopMatrix classVPMomenta
  RefinedBound IntNoSubdivergenceRefined)

/-- The refined criterion for the `VP` pieces with one extra photon line. -/
theorem crit_ext1_piece (j : Fin 5) :
    IntNoSubdivergenceRefined 2 ((vpPieceLines j).map Fin.castSuccEmb)
      fun i => class5LoopMatrix .VP (vpExt1Lines (vpPieceShape j) i) := by
  fin_cases j
  exacts [crit_vpExt1 0, crit_vpExt1 1, crit_vpExt1 2, crit_vpExt1_three.1, crit_vpExt1_three.2]

/-- The refined criterion for the `VP` pieces with two extra photon lines. -/
theorem crit_ext2_piece (j : Fin 5) :
    IntNoSubdivergenceRefined 2 ((vpPieceLines j).map (Fin.castLEEmb (by norm_num : 10 ≤ 12)))
      fun i => class5LoopMatrix .VP (vpExt2Lines (vpPieceShape j) i) := by
  fin_cases j
  exacts [crit_vpExt2 0, crit_vpExt2 1, crit_vpExt2 2, crit_vpExt2_three.1, crit_vpExt2_three.2]

section Data

theorem adm_cpos {P : Params} (hA : ChainAdmissible P) : 0 < 3 / 4 * min (P.m ^ 2) (P.mγ ^ 2) :=
  mul_pos (by norm_num) (lt_min (pow_pos hA.hm 2) (pow_pos hA.hmγ 2))

theorem adm_h₁ {P : Params} (hA : ChainAdmissible P) : P.m ^ 2 ≤ P.M₁ ^ 2 :=
  pow_le_pow_left₀ hA.hm.le hA.hM₁.le 2
theorem adm_h₂ {P : Params} (hA : ChainAdmissible P) : P.m ^ 2 ≤ P.M₂ ^ 2 :=
  pow_le_pow_left₀ hA.hm.le hA.hM₂.le 2
theorem adm_hΛ {P : Params} (hA : ChainAdmissible P) : P.mγ ^ 2 ≤ P.Λ ^ 2 :=
  pow_le_pow_left₀ hA.hmγ.le hA.hmγΛ.le 2

variable {P : Params} (hA : ChainAdmissible P) {p p' : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))

/-- The data of the `j`-th `VP` piece with the extra photon line of mass `Λ`. -/
noncomputable def ext1Data (j : Fin 5) : ParamData :=
  rowsData (by norm_num) (vpExt1Lines (vpPieceShape j)) (vpExt1Masses P (vpPieceShape j) P.Λ) p p'
    _ (crit_ext1_piece j) (adm_cpos hA)
    (symanzikV_vpRows_ge _ _ (vpExt1Masses_ge P (adm_h₁ hA) (adm_h₂ hA) (adm_hΛ hA) (adm_hΛ hA) _)
      hp hp' hq)

/-- The data of the `j`-th `VP` piece with the extra photon lines of masses `m_γ`, `Λ`. -/
noncomputable def ext2Data (j : Fin 5) : ParamData :=
  rowsData (by norm_num) (vpExt2Lines (vpPieceShape j)) (vpExt2Masses P (vpPieceShape j) P.mγ P.Λ)
    p p' _ (crit_ext2_piece j) (adm_cpos hA)
    (symanzikV_vpRows_ge _ _ (vpExt2Masses_ge P (adm_h₁ hA) (adm_h₂ hA) (adm_hΛ hA) le_rfl
      (adm_hΛ hA) _) hp hp' hq)

include hA hp hp' hq in
/-- **The `VP` shapes with one extra photon line `Λ`**: the limit is the sum of the parametric
values of the five piece numerators. -/
theorem ext1_lim (α β μ : Fin 4) : ∃ v : Fin 5 → ℂ,
    (∀ j, IsParamValue (ext1Data hA hp hp' hq j) (fun ℓ => vpPieceM P p p' j μ ℓ α β) (v j)) ∧
    JointLimV (fun ε ℓ => twoLoopNorm * ∑ t : Fin 4, vpTermNumer { P with ε := ε } (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) t ℓ *
        ((∏ i : Fin 10, (vpDenom { P with ε := ε } t p p' i ℓ)⁻¹) * (propDenom P.Λ ε (ℓ 1))⁻¹))
      (∑ j, v j) := by
  have hv : ∀ j, ∃ v, IsParamValue (ext1Data hA hp hp' hq j)
      (fun ℓ => vpPieceM P p p' j μ ℓ α β) v := fun j =>
    exists_paramValue _ (isLoopPoly_vpPieceNumer P (fun _ => p') (fun _ => p) (fun _ => p' - p)
      (fun _ => α) (fun _ => β) (fun _ => μ) j)
      (RefinedBound.map_rows Fin.castSuccEmb (vpExt1_rows (vpPieceShape j))
        (refinedBound_vpPieceNumer P (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α)
          (fun _ => β) (fun _ => μ) j))
  choose v hv using hv
  refine ⟨v, hv, ?_⟩
  have hE := jointHasLim_vpRows (by norm_num) (vpExt1Lines 3) (vpExt1Masses P 3 P.Λ) p p'
    (crit_vpExt1 3) (isLoopPoly_vpEpsNumer P (fun _ => p) (fun _ => p' - p) (fun _ => α)
      (fun _ => β) (fun _ => μ))
    (RefinedBound.map_rows _ (vpExt1_rows 3) (refinedBound_vpEpsNumer P (fun _ => p)
      (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ))) (adm_cpos hA)
    (symanzikV_vpRows_ge _ _ (vpExt1Masses_ge P (adm_h₁ hA) (adm_h₂ hA) (adm_hΛ hA) (adm_hΛ hA) 3)
      hp hp' hq)
  obtain ⟨w, hw⟩ := JointLimV.of_jointHasLim hE
  have h := (((((jointLimV_of_paramValue (hv 0)).add (jointLimV_of_paramValue (hv 1))).add
    (jointLimV_of_paramValue (hv 2))).add (jointLimV_of_paramValue (hv 3))).add
      (jointLimV_of_paramValue (hv 4))).add hw.eps_mul
  have e : ∑ j, v j = v 0 + v 1 + v 2 + v 3 + v 4 + 0 := by
    rw [Fin.sum_univ_five, add_zero]
  rw [e]
  refine h.congr (Eventually.of_forall fun ε ℓ => ?_)
  have key := integrand_VP_eq P ε (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α)
    (fun _ => β) (fun _ => μ) ℓ
  set X := (propDenom P.Λ ε (ℓ 1))⁻¹
  have hA' : ∀ j : Fin 5, vpPieceM P p p' j μ ℓ α β *
      ∏ i, (lineDenom (ext1Data hA hp hp' hq j).α (ext1Data hA hp hp' hq j).p
        (ext1Data hA hp hp' hq j).M ε i ℓ)⁻¹ =
      vpPieceNumer P (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β)
        (fun _ => μ) j ℓ * (vpDenomProd P (vpPieceShape j) p p' ε ℓ * X) := fun j =>
    congrArg (_ * ·) (prod_vpExt1 { P with ε := ε } (vpPieceShape j) P.Λ p p' ℓ)
  rw [hA' 0, hA' 1, hA' 2, hA' 3, hA' 4]
  have hX : twoLoopNorm * ∑ t : Fin 4, vpTermNumer { P with ε := ε } (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) t ℓ *
        ((∏ i : Fin 10, (vpDenom { P with ε := ε } t p p' i ℓ)⁻¹) * X) =
      (twoLoopNorm * ∑ t : Fin 4, vpTermNumer { P with ε := ε } (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) t ℓ *
        ∏ i : Fin 10, (vpDenom { P with ε := ε } t p p' i ℓ)⁻¹) * X := by
    rw [mul_assoc, Finset.sum_mul]
    simp only [mul_assoc]
  rw [hX, key]
  have s0 : vpPieceShape 0 = 0 := rfl
  have s1 : vpPieceShape 1 = 1 := rfl
  have s2 : vpPieceShape 2 = 2 := rfl
  have s3 : vpPieceShape 3 = 3 := rfl
  have s4 : vpPieceShape 4 = 3 := rfl
  have hEps : vpEpsNumer P (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) ℓ *
      ∏ i, (propDenom (vpExt1Masses P 3 P.Λ i) ε (classLineVP p p' (vpExt1Lines 3 i) ℓ))⁻¹ =
      vpEpsNumer P (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) ℓ *
        (vpDenomProd P 3 p p' ε ℓ * X) :=
    congrArg (_ * ·) (prod_vpExt1 { P with ε := ε } 3 P.Λ p p' ℓ)
  rw [hEps, s0, s1, s2, s3, s4]
  ring

include hA hp hp' hq in
/-- **The `VP` shapes with the extra photon lines `m_γ`, `Λ`**, as `ext1_lim`. -/
theorem ext2_lim (α β μ : Fin 4) : ∃ v : Fin 5 → ℂ,
    (∀ j, IsParamValue (ext2Data hA hp hp' hq j) (fun ℓ => vpPieceM P p p' j μ ℓ α β) (v j)) ∧
    JointLimV (fun ε ℓ => twoLoopNorm * ∑ t : Fin 4, vpTermNumer { P with ε := ε } (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) t ℓ *
        ((∏ i : Fin 10, (vpDenom { P with ε := ε } t p p' i ℓ)⁻¹) *
          ((propDenom P.mγ ε (ℓ 1))⁻¹ * (propDenom P.Λ ε (ℓ 1))⁻¹)))
      (∑ j, v j) := by
  have hv : ∀ j, ∃ v, IsParamValue (ext2Data hA hp hp' hq j)
      (fun ℓ => vpPieceM P p p' j μ ℓ α β) v := fun j =>
    exists_paramValue _ (isLoopPoly_vpPieceNumer P (fun _ => p') (fun _ => p) (fun _ => p' - p)
      (fun _ => α) (fun _ => β) (fun _ => μ) j)
      (RefinedBound.map_rows _ (vpExt2_rows (vpPieceShape j))
        (refinedBound_vpPieceNumer P (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α)
          (fun _ => β) (fun _ => μ) j))
  choose v hv using hv
  refine ⟨v, hv, ?_⟩
  have hE := jointHasLim_vpRows (by norm_num) (vpExt2Lines 3) (vpExt2Masses P 3 P.mγ P.Λ) p p'
    (crit_vpExt2 3) (isLoopPoly_vpEpsNumer P (fun _ => p) (fun _ => p' - p) (fun _ => α)
      (fun _ => β) (fun _ => μ))
    (RefinedBound.map_rows _ (vpExt2_rows 3) (refinedBound_vpEpsNumer P (fun _ => p)
      (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ))) (adm_cpos hA)
    (symanzikV_vpRows_ge _ _ (vpExt2Masses_ge P (adm_h₁ hA) (adm_h₂ hA) (adm_hΛ hA) le_rfl
      (adm_hΛ hA) 3) hp hp' hq)
  obtain ⟨w, hw⟩ := JointLimV.of_jointHasLim hE
  have h := (((((jointLimV_of_paramValue (hv 0)).add (jointLimV_of_paramValue (hv 1))).add
    (jointLimV_of_paramValue (hv 2))).add (jointLimV_of_paramValue (hv 3))).add
      (jointLimV_of_paramValue (hv 4))).add hw.eps_mul
  have e : ∑ j, v j = v 0 + v 1 + v 2 + v 3 + v 4 + 0 := by
    rw [Fin.sum_univ_five, add_zero]
  rw [e]
  refine h.congr (Eventually.of_forall fun ε ℓ => ?_)
  have key := integrand_VP_eq P ε (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α)
    (fun _ => β) (fun _ => μ) ℓ
  set X := (propDenom P.mγ ε (ℓ 1))⁻¹ * (propDenom P.Λ ε (ℓ 1))⁻¹
  have hA' : ∀ j : Fin 5, vpPieceM P p p' j μ ℓ α β *
      ∏ i, (lineDenom (ext2Data hA hp hp' hq j).α (ext2Data hA hp hp' hq j).p
        (ext2Data hA hp hp' hq j).M ε i ℓ)⁻¹ =
      vpPieceNumer P (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β)
        (fun _ => μ) j ℓ * (vpDenomProd P (vpPieceShape j) p p' ε ℓ * X) := fun j =>
    congrArg (_ * ·) (prod_vpExt2 { P with ε := ε } (vpPieceShape j) P.mγ P.Λ p p' ℓ)
  rw [hA' 0, hA' 1, hA' 2, hA' 3, hA' 4]
  have hX : twoLoopNorm * ∑ t : Fin 4, vpTermNumer { P with ε := ε } (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) t ℓ *
        ((∏ i : Fin 10, (vpDenom { P with ε := ε } t p p' i ℓ)⁻¹) * X) =
      (twoLoopNorm * ∑ t : Fin 4, vpTermNumer { P with ε := ε } (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) t ℓ *
        ∏ i : Fin 10, (vpDenom { P with ε := ε } t p p' i ℓ)⁻¹) * X := by
    rw [mul_assoc, Finset.sum_mul]
    simp only [mul_assoc]
  rw [hX, key]
  have s0 : vpPieceShape 0 = 0 := rfl
  have s1 : vpPieceShape 1 = 1 := rfl
  have s2 : vpPieceShape 2 = 2 := rfl
  have s3 : vpPieceShape 3 = 3 := rfl
  have s4 : vpPieceShape 4 = 3 := rfl
  have hEps : vpEpsNumer P (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) ℓ *
      ∏ i, (propDenom (vpExt2Masses P 3 P.mγ P.Λ i) ε (classLineVP p p' (vpExt2Lines 3 i) ℓ))⁻¹ =
      vpEpsNumer P (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) ℓ *
        (vpDenomProd P 3 p p' ε ℓ * X) :=
    congrArg (_ * ·) (prod_vpExt2 { P with ε := ε } 3 P.mγ P.Λ p p' ℓ)
  rw [hEps, s0, s1, s2, s3, s4]
  ring

/-- The data of the longitudinal piece with the loop `b₀ b₁ b₂`. -/
noncomputable def L1Data : ParamData :=
  rowsData (by norm_num) lineL1 (massL1 P) p p' ({1, 0} ∪ {2} ∪ {8}) crit_L.1 (adm_cpos hA)
    (symanzikV_vpRows_ge _ _ (massL_ge P (adm_h₁ hA) (adm_h₂ hA) (adm_hΛ hA)).1 hp hp' hq)

/-- The data of the longitudinal piece with the loop `a₀ a₁ a₂`. -/
noncomputable def L2Data : ParamData :=
  rowsData (by norm_num) lineL2 (massL1 P) p p' ({1, 0} ∪ {2} ∪ {8}) crit_L.2.1 (adm_cpos hA)
    (symanzikV_vpRows_ge _ _ (massL_ge P (adm_h₁ hA) (adm_h₂ hA) (adm_hΛ hA)).2.1 hp hp' hq)

end Data

/-- The numerator matrices of the longitudinal pieces of `repBD`. -/
noncomputable def bdL1N (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun α β => bdN P p (p' - p) μ α β (-ℓ 1) (ℓ 0)

/-- The numerator matrix with the loop `a₀ a₁ a₂`. -/
noncomputable def bdL2N (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun α β => bdN P p (p' - p) μ α β (-ℓ 1) (ℓ 0 + -ℓ 1)

/-- The numerator matrices of the longitudinal pieces of `repDB`. -/
noncomputable def dbL1N (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun α β => dbN P p (p' - p) μ α β (-ℓ 1) (ℓ 0)

/-- The numerator matrix with the loop `a₀ a₁ a₂`. -/
noncomputable def dbL2N (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun α β => dbN P p (p' - p) μ α β (-ℓ 1) (ℓ 0 + -ℓ 1)

/-- The coefficient of the `VP` pieces with one extra photon line. -/
noncomputable def bdK1 (P : Params) : ℂ := -(P.δ₃ / 2 : ℂ) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)

/-- The limit coefficient of the `VP` pieces with two extra photon lines. -/
noncomputable def bdK2 (P : Params) : ℂ :=
  (P.δ₃ / 2 : ℂ) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) * (((P.mγ ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I)

section Lim

variable {P : Params} (hA : ChainAdmissible P) {p p' : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))

include hA hp hp' hq in
/-- **The limit of the integrand of `repBD s` as a combination of parametric values.** -/
theorem bd_lim (s : Fin 2) (α β μ : Fin 4) : ∃ (v1 v2 : Fin 5 → ℂ) (w1 w2 : ℂ),
    (∀ j, IsParamValue (ext1Data hA hp hp' hq j) (fun ℓ => vpPieceM P p p' j μ ℓ α β) (v1 j)) ∧
    (∀ j, IsParamValue (ext2Data hA hp hp' hq j) (fun ℓ => vpPieceM P p p' j μ ℓ α β) (v2 j)) ∧
    IsParamValue (L1Data hA hp hp' hq) (fun ℓ => bdL1N P p p' μ ℓ α β) w1 ∧
    IsParamValue (L2Data hA hp hp' hq) (fun ℓ => bdL2N P p p' μ ℓ α β) w2 ∧
    JointLimV (fun ε => bdG { P with ε := ε } (fun _ => α) (fun _ => β) (fun _ => μ) s
      (fun _ => p) (fun _ => p' - p))
      (bdK1 P * ∑ j, v1 j + bdK2 P * ∑ j, v2 j + bdκL P * w1 + -bdκL P * w2) := by
  have hpp : p + (p' - p) = p' := by abel
  have hp'' : Minkowski.dot (p + (p' - p)) (p + (p' - p)) = -P.m ^ 2 := by rw [hpp]; exact hp'
  have hq'' : 0 ≤ Minkowski.dot (p + (p' - p) - p) (p + (p' - p) - p) := by rw [hpp]; exact hq
  obtain ⟨v1, hv1, h1⟩ := ext1_lim hA hp hp' hq α β μ
  obtain ⟨v2, hv2, h2⟩ := ext2_lim hA hp hp' hq α β μ
  obtain ⟨m1, m2, m3a, m3b, m3c⟩ := massL_ge P (adm_h₁ hA) (adm_h₂ hA) (adm_hΛ hA)
  obtain ⟨c1, c2, c3a, c3b, c3c⟩ := crit_L
  obtain ⟨b1p, b1B⟩ := bdPiece_bounds P lineL1 p (p' - p) μ α β 8 isLoopAffine_zero' rfl rfl rfl
    (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.1.symm) (by decide) (by decide) (by decide)
    (by decide)
  obtain ⟨b2p, b2B⟩ := bdPiece_bounds P lineL2 p (p' - p) μ α β 8
    (IsLoopAffine.add' isLoopAffine_zero' isLoopAffine_neg_one) rfl rfl rfl
    (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.1.symm) (by decide) (by decide) (by decide)
    (by decide)
  obtain ⟨w1, hw1⟩ := exists_paramValue (L1Data hA hp hp' hq) b1p b1B
  obtain ⟨w2, hw2⟩ := exists_paramValue (L2Data hA hp hp' hq) b2p b2B
  refine ⟨v1, v2, w1, w2, hv1, hv2, hw1, hw2, ?_⟩
  obtain ⟨_, h3a⟩ := JointLimV.of_jointHasLim (jointHasLim_bdPiece P (by norm_num) lineL3a
    (massL3a P) p (p' - p) μ α β 3 isLoopAffine_neg_one rfl rfl rfl
    (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.2.1.symm) (by decide) (by decide) (by decide)
    (by decide) c3a (-(bdκL P * I)) (adm_cpos hA) (symanzikV_vpRows_ge _ _ m3a hp hp'' hq''))
  obtain ⟨_, h3b⟩ := JointLimV.of_jointHasLim (jointHasLim_bdPiece P (by norm_num) lineL3b
    (massL3b P) p (p' - p) μ α β 3 isLoopAffine_neg_one rfl rfl rfl
    (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.2.1.symm) (by decide) (by decide) (by decide)
    (by decide) c3b (-(bdκL P * I)) (adm_cpos hA) (symanzikV_vpRows_ge _ _ m3b hp hp'' hq''))
  obtain ⟨_, h3c⟩ := JointLimV.of_jointHasLim (jointHasLim_bdPiece P (by norm_num) lineL3c
    (massL3c P) p (p' - p) μ α β 3 isLoopAffine_neg_one rfl rfl rfl
    (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.2.1.symm) (by decide) (by decide) (by decide)
    (by decide) c3c (-(bdκL P * I)) (adm_cpos hA) (symanzikV_vpRows_ge _ _ m3c hp hp'' hq''))
  have h := ((((((h1.const_mul (bdK1 P)).add (h2.mul_left (tendsto_mγ_sub P
    ((P.δ₃ / 2 : ℂ) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ))))).add
    ((jointLimV_of_paramValue hw1).const_mul (bdκL P))).add
    ((jointLimV_of_paramValue hw2).const_mul (-bdκL P))).add h3a.eps_mul).add h3b.eps_mul).add
      h3c.eps_mul
  simp only [add_zero] at h
  refine h.congr ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  intro ℓ
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  rw [bdG_eq { P with ε := ε } (fun _ => α) (fun _ => β) (fun _ => μ) s (pOut := fun _ => p')
    hε.ne' hA.hPV₁ hA.hPV₂ hmom ℓ]
  have e1 : bdκL { P with ε := ε } = bdκL P := rfl
  have e3 : massL1 { P with ε := ε } = massL1 P := rfl
  have e3a : massL3a { P with ε := ε } = massL3a P := rfl
  have e3b : massL3b { P with ε := ε } = massL3b P := rfl
  have e3c : massL3c { P with ε := ε } = massL3c P := rfl
  have e2 : ∀ a b c d e f g, bdN { P with ε := ε } a b c d e f g = bdN P a b c d e f g :=
    fun _ _ _ _ _ _ _ => rfl
  have eL1 : ∀ x, lineDenom (L1Data hA hp hp' hq).α (L1Data hA hp hp' hq).p
      (L1Data hA hp hp' hq).M ε x ℓ = propDenom (massL1 P x) ε (classLineVP p p' (lineL1 x) ℓ) :=
    fun _ => rfl
  have eL2 : ∀ x, lineDenom (L2Data hA hp hp' hq).α (L2Data hA hp hp' hq).p
      (L2Data hA hp hp' hq).M ε x ℓ = propDenom (massL1 P x) ε (classLineVP p p' (lineL2 x) ℓ) :=
    fun _ => rfl
  simp only [e1, e2, e3, e3a, e3b, e3c, hpp, bdK1, twoLoopNorm, eL1,
    eL2]
  set A := ∑ t : Fin 4, vpTermNumer { P with ε := ε } (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) t ℓ *
        ((∏ i : Fin 10, (vpDenom { P with ε := ε } t p p' i ℓ)⁻¹) * (propDenom P.Λ ε (ℓ 1))⁻¹)
  set B := ∑ t : Fin 4, vpTermNumer { P with ε := ε } (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) t ℓ *
        ((∏ i : Fin 10, (vpDenom { P with ε := ε } t p p' i ℓ)⁻¹) *
          ((propDenom P.mγ ε (ℓ 1))⁻¹ * (propDenom P.Λ ε (ℓ 1))⁻¹))
  set c := (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹
  ring_nf
  rfl

include hA hp hp' hq in
/-- **The limit of the integrand of `repDB s` as a combination of parametric values.** -/
theorem db_lim (s : Fin 2) (α β μ : Fin 4) : ∃ (v1 v2 : Fin 5 → ℂ) (w1 w2 : ℂ),
    (∀ j, IsParamValue (ext1Data hA hp hp' hq j) (fun ℓ => vpPieceM P p p' j μ ℓ α β) (v1 j)) ∧
    (∀ j, IsParamValue (ext2Data hA hp hp' hq j) (fun ℓ => vpPieceM P p p' j μ ℓ α β) (v2 j)) ∧
    IsParamValue (L1Data hA hp hp' hq) (fun ℓ => dbL1N P p p' μ ℓ α β) w1 ∧
    IsParamValue (L2Data hA hp hp' hq) (fun ℓ => dbL2N P p p' μ ℓ α β) w2 ∧
    JointLimV (fun ε => dbG { P with ε := ε } (fun _ => α) (fun _ => β) (fun _ => μ) s
      (fun _ => p) (fun _ => p' - p))
      (bdK1 P * ∑ j, v1 j + bdK2 P * ∑ j, v2 j + bdκL P * w1 + -bdκL P * w2) := by
  have hpp : p + (p' - p) = p' := by abel
  have hp'' : Minkowski.dot (p + (p' - p)) (p + (p' - p)) = -P.m ^ 2 := by rw [hpp]; exact hp'
  have hq'' : 0 ≤ Minkowski.dot (p + (p' - p) - p) (p + (p' - p) - p) := by rw [hpp]; exact hq
  obtain ⟨v1, hv1, h1⟩ := ext1_lim hA hp hp' hq α β μ
  obtain ⟨v2, hv2, h2⟩ := ext2_lim hA hp hp' hq α β μ
  obtain ⟨m1, m2, m3a, m3b, m3c⟩ := massL_ge P (adm_h₁ hA) (adm_h₂ hA) (adm_hΛ hA)
  obtain ⟨c1, c2, c3a, c3b, c3c⟩ := crit_L
  obtain ⟨b1p, b1B⟩ := dbPiece_bounds P lineL1 p (p' - p) μ α β 8 isLoopAffine_zero' rfl rfl rfl
    (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.1.symm) (by decide) (by decide) (by decide)
    (by decide)
  obtain ⟨b2p, b2B⟩ := dbPiece_bounds P lineL2 p (p' - p) μ α β 8
    (IsLoopAffine.add' isLoopAffine_zero' isLoopAffine_neg_one) rfl rfl rfl
    (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.1.symm) (by decide) (by decide) (by decide)
    (by decide)
  obtain ⟨w1, hw1⟩ := exists_paramValue (L1Data hA hp hp' hq) b1p b1B
  obtain ⟨w2, hw2⟩ := exists_paramValue (L2Data hA hp hp' hq) b2p b2B
  refine ⟨v1, v2, w1, w2, hv1, hv2, hw1, hw2, ?_⟩
  obtain ⟨_, h3a⟩ := JointLimV.of_jointHasLim (jointHasLim_dbPiece P (by norm_num) lineL3a
    (massL3a P) p (p' - p) μ α β 3 isLoopAffine_neg_one rfl rfl rfl
    (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.2.1.symm) (by decide) (by decide) (by decide)
    (by decide) c3a (-(bdκL P * I)) (adm_cpos hA) (symanzikV_vpRows_ge _ _ m3a hp hp'' hq''))
  obtain ⟨_, h3b⟩ := JointLimV.of_jointHasLim (jointHasLim_dbPiece P (by norm_num) lineL3b
    (massL3b P) p (p' - p) μ α β 3 isLoopAffine_neg_one rfl rfl rfl
    (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.2.1.symm) (by decide) (by decide) (by decide)
    (by decide) c3b (-(bdκL P * I)) (adm_cpos hA) (symanzikV_vpRows_ge _ _ m3b hp hp'' hq''))
  obtain ⟨_, h3c⟩ := JointLimV.of_jointHasLim (jointHasLim_dbPiece P (by norm_num) lineL3c
    (massL3c P) p (p' - p) μ α β 3 isLoopAffine_neg_one rfl rfl rfl
    (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.2.1.symm) (by decide) (by decide) (by decide)
    (by decide) c3c (-(bdκL P * I)) (adm_cpos hA) (symanzikV_vpRows_ge _ _ m3c hp hp'' hq''))
  have h := ((((((h1.const_mul (bdK1 P)).add (h2.mul_left (tendsto_mγ_sub P
    ((P.δ₃ / 2 : ℂ) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ))))).add
    ((jointLimV_of_paramValue hw1).const_mul (bdκL P))).add
    ((jointLimV_of_paramValue hw2).const_mul (-bdκL P))).add h3a.eps_mul).add h3b.eps_mul).add
      h3c.eps_mul
  simp only [add_zero] at h
  refine h.congr ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  intro ℓ
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  rw [dbG_eq { P with ε := ε } (fun _ => α) (fun _ => β) (fun _ => μ) s (pOut := fun _ => p')
    hε.ne' hA.hPV₁ hA.hPV₂ hmom ℓ]
  have e1 : bdκL { P with ε := ε } = bdκL P := rfl
  have e3 : massL1 { P with ε := ε } = massL1 P := rfl
  have e3a : massL3a { P with ε := ε } = massL3a P := rfl
  have e3b : massL3b { P with ε := ε } = massL3b P := rfl
  have e3c : massL3c { P with ε := ε } = massL3c P := rfl
  have e2 : ∀ a b c d e f g, dbN { P with ε := ε } a b c d e f g = dbN P a b c d e f g :=
    fun _ _ _ _ _ _ _ => rfl
  have eL1 : ∀ x, lineDenom (L1Data hA hp hp' hq).α (L1Data hA hp hp' hq).p
      (L1Data hA hp hp' hq).M ε x ℓ = propDenom (massL1 P x) ε (classLineVP p p' (lineL1 x) ℓ) :=
    fun _ => rfl
  have eL2 : ∀ x, lineDenom (L2Data hA hp hp' hq).α (L2Data hA hp hp' hq).p
      (L2Data hA hp hp' hq).M ε x ℓ = propDenom (massL1 P x) ε (classLineVP p p' (lineL2 x) ℓ) :=
    fun _ => rfl
  simp only [e1, e2, e3, e3a, e3b, e3c, hpp, bdK1, twoLoopNorm, eL1,
    eL2]
  set A := ∑ t : Fin 4, vpTermNumer { P with ε := ε } (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) t ℓ *
        ((∏ i : Fin 10, (vpDenom { P with ε := ε } t p p' i ℓ)⁻¹) * (propDenom P.Λ ε (ℓ 1))⁻¹)
  set B := ∑ t : Fin 4, vpTermNumer { P with ε := ε } (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) t ℓ *
        ((∏ i : Fin 10, (vpDenom { P with ε := ε } t p p' i ℓ)⁻¹) *
          ((propDenom P.mγ ε (ℓ 1))⁻¹ * (propDenom P.Λ ε (ℓ 1))⁻¹))
  set c := (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹
  ring_nf
  rfl

end Lim

end QED.ChainProof.HCSide

end
