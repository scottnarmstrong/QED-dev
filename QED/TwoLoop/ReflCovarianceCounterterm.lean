/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ReflCovarianceParam
public import QED.TwoLoop.LimitCovarianceCounterterm

/-!
# Covariance of two counterterm-class limits under Lorentz maps that move the external momenta

Part of obligations O2-20 and O2-21 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4). For a real `L`
with a spinor lift `(S, T)` and on-shell `p, p'` with `q² ≥ 0` (of either energy sign), the
vertices of `ε → 0⁺` limits of the counterterm classes `δ₂ in` and `δ₃` (slot `0`)
(`QED.TwoLoop.LimitCovariance.ctLimitV`) satisfy `S W(L p, L p')^μ T = L^μ_ν W(p, p')^ν`
(`ctLimitV_d2In_map`, `ctLimitV_d3Slot0_map`). These are the two counterterm classes whose
reflection covariance the mirror identity of the counterterm part needs
(`QED.TwoLoop.CountertermMirror.isMirrorSymmetric_ctPart`).

The limits are parametric values of the product with an auxiliary loop divided by `auxLimit m`
(`QED.TwoLoop.LimitCovariance.exists_paramValue_of_kinds`), which does not use positive energies.
-/

@[expose] public section

open Complex Matrix Filter Topology
open scoped Real

namespace QED.TwoLoop.ReflCovariance

open QED.Dirac QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.ClassLimit QED.TwoLoop.Insertion
open QED.TwoLoop.CountertermLimit QED.TwoLoop.Relabel QED.TwoLoop.LimitCovariance
open QED.Integration.TwoLoop (LoopQuartic IntNoSubdivergenceRefined)

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

theorem lineKind_mom_map (p p' : Fin 4 → ℝ) (k : LineKind) :
    k.mom (L *ᵥ p) (L *ᵥ p') = L *ᵥ k.mom p p' := by
  cases k <;> simp [LineKind.mom]

theorem mulVec_add_mulVec (p k : Fin 4 → ℝ) : L *ᵥ p + L *ᵥ k = L *ᵥ (p + k) :=
  (Matrix.mulVec_add _ _ _).symm

theorem numD2In_map (h : IsSpinLift L S T) (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (k : Fin 4 → ℝ) :
    S * numD2In P (L *ᵥ p') (L *ᵥ p) μ (L *ᵥ k) * T = vecAct L (fun ν => numD2In P p' p ν k) μ := by
  simp only [numD2In, vertexChain_eq_chain, Matrix.mul_smul, Matrix.smul_mul, h.mul_chain_mul,
    tensorAct_pvPhotonNum h, mulVec_add_mulVec, h.mul_electronNumerator_mul, mul_insertion_mul h]
  rw [vecAct_smul]

theorem numD3_map (h : IsSpinLift L S T) (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (k : Fin 4 → ℝ) :
    S * numD3 P (L *ᵥ p') (L *ᵥ p) μ (L *ᵥ k) * T = vecAct L (fun ν => numD3 P p' p ν k) μ := by
  simp only [numD3, vertexChain_eq_chain, Matrix.mul_smul, Matrix.smul_mul, h.mul_chain_mul,
    photonNum_eq_lowered, photonCtFactor_mulVec h, tensorAct_const_mul, tensorAct_lowered h,
    mulVec_add_mulVec, h.mul_electronNumerator_mul]
  rw [vecAct_smul]

section CtLimits

variable (P : Params)

theorem massesD2In_sq_of_ne_pho :
    ∀ i, kindsD2In i ≠ .pho → massesD2In P i ^ 2 = P.m ^ 2 := fun i hi => by
  fin_cases i <;> simp_all [kindsD2In, massesD2In]

theorem min_sq_le_massesD2In_sq (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    ∀ i, kindsD2In i = .pho → min P.mγ P.Λ ^ 2 ≤ massesD2In P i ^ 2 := fun i hi => by
  obtain ⟨h1, h2⟩ := sq_min_le P hmγ hΛ
  fin_cases i <;> simp_all [kindsD2In, massesD2In]

theorem intNoSubdivergenceRefined_kindsD2In :
    IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (kindsD2In i).dir := by
  decide

theorem massesD3_sq_of_ne_pho :
    ∀ i, kindsD3 i ≠ .pho → massesD3 P i ^ 2 = P.m ^ 2 := fun i hi => by
  fin_cases i <;> simp_all [kindsD3, massesD3]

theorem min_sq_le_massesD3_sq (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    ∀ i, kindsD3 i = .pho → min P.mγ P.Λ ^ 2 ≤ massesD3 P i ^ 2 := fun i hi => by
  obtain ⟨h1, h2⟩ := sq_min_le P hmγ hΛ
  fin_cases i <;> simp_all [kindsD3, massesD3]

theorem intNoSubdivergenceRefined_kindsD3 :
    IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (kindsD3 i).dir := by
  decide

variable (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
variable {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
  (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hm hmγ hΛ hp hp' hq

/-- The parametric data of the `δ₂ in` class at `(p', p)`. -/
noncomputable def d2InData : ParamData :=
  kindsData (by norm_num) kindsD2In (massesD2In P) hm (lt_min hmγ hΛ) hp hp' hq
    (massesD2In_sq_of_ne_pho P) (min_sq_le_massesD2In_sq P hmγ hΛ)
    intNoSubdivergenceRefined_kindsD2In

/-- The parametric data of the `δ₃` classes at `(p', p)`. -/
noncomputable def d3Data : ParamData :=
  kindsData (by norm_num) kindsD3 (massesD3 P) hm (lt_min hmγ hΛ) hp hp' hq
    (massesD3_sq_of_ne_pho P) (min_sq_le_massesD3_sq P hmγ hΛ) intNoSubdivergenceRefined_kindsD3

/-- The entries of the `δ₂ in` limit as parametric values divided by `auxLimit m`. -/
theorem ctLimitV_d2In_entry (μ i j : Fin 4) :
    ∃ v, IsParamValue (d2InData P hm hmγ hΛ hp hp' hq) (fun ℓ => numD2In P p' p μ (ℓ 0) i j) v ∧
      ctLimitV .d2In P p p' μ i j = v / auxLimit P.m := by
  obtain ⟨v, hv, hT⟩ := exists_paramValue_of_kinds (by norm_num) kindsD2In (massesD2In P) hm
    (lt_min hmγ hΛ) hp hp' hq (massesD2In_sq_of_ne_pho P) (min_sq_le_massesD2In_sq P hmγ hΛ)
    intNoSubdivergenceRefined_kindsD2In (by decide) (by decide)
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

/-- The entries of the `δ₃` (slot `0`) limit as parametric values divided by `auxLimit m`. -/
theorem ctLimitV_d3Slot0_entry (μ i j : Fin 4) :
    ∃ v, IsParamValue (d3Data P hm hmγ hΛ hp hp' hq) (fun ℓ => numD3 P p' p μ (ℓ 0) i j) v ∧
      ctLimitV .d3Slot0 P p p' μ i j = v / auxLimit P.m := by
  obtain ⟨v, hv, hT⟩ := exists_paramValue_of_kinds (by norm_num) kindsD3 (massesD3 P) hm
    (lt_min hmγ hΛ) hp hp' hq (massesD3_sq_of_ne_pho P) (min_sq_le_massesD3_sq P hmγ hΛ)
    intNoSubdivergenceRefined_kindsD3 (by decide) (by decide)
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

omit hp hp' hq in
/-- **Covariance of the `δ₂ in` limit under `L`, with the external momenta moved.** -/
theorem ctLimitV_d2In_map (h : IsSpinLift L S T) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (μ : Fin 4) :
    S * ctLimitV .d2In P (L *ᵥ p) (L *ᵥ p') μ * T = vecAct L (ctLimitV .d2In P p p') μ := by
  have hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp
  have hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp'
  have hqL : 0 ≤ Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p) := by
    rw [← Matrix.mulVec_sub, h.dot_mulVec]; exact hq
  refine conj_eq_vecAct_of_paramValue_div (d2InData P hm hmγ hΛ hp hp' hq) h
    (fun i => (kindsD2In i).mom (L *ᵥ p) (L *ᵥ p')) (funext fun i => lineKind_mom_map p p' _)
    (fun μ k => numD2In P p' p μ k) (fun μ k => numD2In P (L *ᵥ p') (L *ᵥ p) μ k)
    (fun μ k => numD2In_map h P p' p μ k) _ _ (auxLimit P.m)
    (fun μ i j => ctLimitV_d2In_entry P hm hmγ hΛ hp hp' hq μ i j) (fun μ i j => ?_) μ
  obtain ⟨v, hv, hV⟩ := ctLimitV_d2In_entry P hm hmγ hΛ hpL hpL' hqL μ i j
  obtain ⟨Q, hQ, hI, rfl⟩ := IsParamValue.exists_integrableOn hv
  exact ⟨Q, hQ, hI, hV⟩

omit hp hp' hq in
/-- **Covariance of the `δ₃` (slot `0`) limit under `L`, with the external momenta moved.** -/
theorem ctLimitV_d3Slot0_map (h : IsSpinLift L S T) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (μ : Fin 4) :
    S * ctLimitV .d3Slot0 P (L *ᵥ p) (L *ᵥ p') μ * T = vecAct L (ctLimitV .d3Slot0 P p p') μ := by
  have hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp
  have hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp'
  have hqL : 0 ≤ Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p) := by
    rw [← Matrix.mulVec_sub, h.dot_mulVec]; exact hq
  refine conj_eq_vecAct_of_paramValue_div (d3Data P hm hmγ hΛ hp hp' hq) h
    (fun i => (kindsD3 i).mom (L *ᵥ p) (L *ᵥ p')) (funext fun i => lineKind_mom_map p p' _)
    (fun μ k => numD3 P p' p μ k) (fun μ k => numD3 P (L *ᵥ p') (L *ᵥ p) μ k)
    (fun μ k => numD3_map h P p' p μ k) _ _ (auxLimit P.m)
    (fun μ i j => ctLimitV_d3Slot0_entry P hm hmγ hΛ hp hp' hq μ i j) (fun μ i j => ?_) μ
  obtain ⟨v, hv, hV⟩ := ctLimitV_d3Slot0_entry P hm hmγ hΛ hpL hpL' hqL μ i j
  obtain ⟨Q, hQ, hI, rfl⟩ := IsParamValue.exists_integrableOn hv
  exact ⟨Q, hQ, hI, hV⟩

end CtLimits

end QED.TwoLoop.ReflCovariance

end
