/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCSideDD
public import QED.TwoLoop.ReflCovarianceCounterterm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Covariance of the `δ₃`–`δ₃` class limits of set (b)

Helper level, Phase 5 Stage 1a (O3-8 for the one-loop classes). The `ε → 0⁺` limit of the
`δ₃`–`δ₃` integrand (`QED.ChainProof.HCLimit.exists_tendsto_ddIntegrand`) comes from two one-loop
integrals with the numerator `numD3` of the two-loop `δ₃` class and seven, resp. eight,
propagators (`ddPiece1`, `ddPiece2`), each brought into the two-loop parametric representation by
the auxiliary loop. Here the limits are identified as parametric values divided by `auxLimit m`:

* `dd1Data`, `dd2Data`: the parametric data of the two pieces (line kinds `kindsDD1`,
  `kindsDD2`);
* `tendsto_efi_ddIntegrand_param`: the limit of every entry of the integrand is
  `ddCoeff (v₁/auxLimit m - m_γ² v₂/auxLimit m)`, with `v₁`, `v₂` the parametric values of the
  entry of `numD3` for the two data;
* **`conj_classLimit_repDD`**: for a real `L` with a spinor lift `(S, T)` and an admissible pair
  `(p', p)`, the limits `Y` at `(p', p)` and `Z` at `(L p', L p)` of the class vertex
  `QED.ChainProof.HCValue.classV (repDD s₀ s₁)` satisfy `S Z^μ T = L^μ_ν Y^ν`. As for the two-loop
  `δ₃` class (`QED.TwoLoop.ReflCovariance.ctLimitV_d3Slot0_map`), covariance comes from the
  covariance of `numD3` (`QED.TwoLoop.ReflCovariance.numD3_map`) and of the parametric value
  (`QED.TwoLoop.ReflCovariance.conj_eq_vecAct_of_paramValue_div`); positive energies are not used.
-/

@[expose] public section

open Complex Matrix MeasureTheory Filter Topology
open scoped Real

namespace QED.ChainProof.HCSide

open QED.WickModel QED.TwoLoop.Insertion QED.TwoLoop.Bridge QED.TwoLoop.CountertermLimit
open QED.ChainProof.Enum QED.ChainProof.HCValue QED.ChainProof.HCLimit
open QED.TwoLoop.LimitCovariance QED.TwoLoop.ReflCovariance QED.Dirac
open QED.Integration.TwoLoop (IntNoSubdivergenceRefined LoopQuartic)

/-! ### The parametric data of the two pieces -/

section Data

variable (P : Params)

theorem massesDD1_sq_of_ne_pho : ∀ i, kindsDD1 i ≠ .pho → massesDD1 P i ^ 2 = P.m ^ 2 :=
  fun i hi => by fin_cases i <;> simp_all [kindsDD1, massesDD1]

theorem min_sq_le_massesDD1_sq (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    ∀ i, kindsDD1 i = .pho → min P.mγ P.Λ ^ 2 ≤ massesDD1 P i ^ 2 := fun i hi => by
  obtain ⟨h1, h2⟩ := sq_min_le P hmγ hΛ
  fin_cases i <;> simp_all [kindsDD1, massesDD1]

theorem intNoSubdivergenceRefined_kindsDD1 :
    IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (kindsDD1 i).dir := by
  decide

theorem massesDD2_sq_of_ne_pho : ∀ i, kindsDD2 i ≠ .pho → massesDD2 P i ^ 2 = P.m ^ 2 :=
  fun i hi => by fin_cases i <;> simp_all [kindsDD2, massesDD2]

theorem min_sq_le_massesDD2_sq (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    ∀ i, kindsDD2 i = .pho → min P.mγ P.Λ ^ 2 ≤ massesDD2 P i ^ 2 := fun i hi => by
  obtain ⟨h1, h2⟩ := sq_min_le P hmγ hΛ
  fin_cases i <;> simp_all [kindsDD2, massesDD2]

theorem intNoSubdivergenceRefined_kindsDD2 :
    IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (kindsDD2 i).dir := by
  decide

variable (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
variable {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
  (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))

/-- The parametric data of the first piece at `(p', p)`. -/
noncomputable def dd1Data : ParamData :=
  kindsData (by norm_num) kindsDD1 (massesDD1 P) hm (lt_min hmγ hΛ) hp hp' hq
    (massesDD1_sq_of_ne_pho P) (min_sq_le_massesDD1_sq P hmγ hΛ)
    intNoSubdivergenceRefined_kindsDD1

/-- The parametric data of the second piece at `(p', p)`. -/
noncomputable def dd2Data : ParamData :=
  kindsData (by norm_num) kindsDD2 (massesDD2 P) hm (lt_min hmγ hΛ) hp hp' hq
    (massesDD2_sq_of_ne_pho P) (min_sq_le_massesDD2_sq P hmγ hΛ)
    intNoSubdivergenceRefined_kindsDD2

/-- **The limit of each entry of the `δ₃`–`δ₃` integrand through parametric values.** -/
theorem tendsto_efi_ddIntegrand_param (μ i j : Fin 4) :
    ∃ v₁ v₂ : ℂ,
      IsParamValue (dd1Data P hm hmγ hΛ hp hp' hq) (fun ℓ => numD3 P p' p μ (ℓ 0) i j) v₁ ∧
      IsParamValue (dd2Data P hm hmγ hΛ hp hp' hq) (fun ℓ => numD3 P p' p μ (ℓ 0) i j) v₂ ∧
      Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun k => ddIntegrand P p' p μ ε k i j)
        (𝓝[>] 0) (𝓝 (ddCoeff P * (v₁ / auxLimit P.m -
          ((P.mγ ^ 2 : ℝ) : ℂ) * (v₂ / auxLimit P.m)))) := by
  obtain ⟨v₁, hv₁, hT₁⟩ := exists_paramValue_of_kinds (by norm_num) kindsDD1 (massesDD1 P) hm
    (lt_min hmγ hΛ) hp hp' hq (massesDD1_sq_of_ne_pho P) (min_sq_le_massesDD1_sq P hmγ hΛ)
    intNoSubdivergenceRefined_kindsDD1 (by decide) (by decide)
    (fun k => numD3 P p' p μ k i j) (isLoopPoly_numD3 P _ _ _ _ _) (ddPiece1 P p' p μ i j)
    (fun ε hε ℓ => by
      rw [ddPiece1, integrand_d3_eq P hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsDD1, massesDD1,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)
  obtain ⟨v₂, hv₂, hT₂⟩ := exists_paramValue_of_kinds (by norm_num) kindsDD2 (massesDD2 P) hm
    (lt_min hmγ hΛ) hp hp' hq (massesDD2_sq_of_ne_pho P) (min_sq_le_massesDD2_sq P hmγ hΛ)
    intNoSubdivergenceRefined_kindsDD2 (by decide) (by decide)
    (fun k => numD3 P p' p μ k i j) (isLoopPoly_numD3 P _ _ _ _ _) (ddPiece2 P p' p μ i j)
    (fun ε hε ℓ => by
      rw [ddPiece2, integrand_d3_eq P hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsDD2, massesDD2,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)
  refine ⟨v₁, v₂, hv₁, hv₂, ?_⟩
  have ha : Tendsto (fun ε : ℝ => ((P.mγ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) (𝓝[>] 0)
      (𝓝 ((P.mγ ^ 2 : ℝ) : ℂ)) := by
    have h : Tendsto (fun ε : ℝ => ((P.mγ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) (𝓝 0)
        (𝓝 (((P.mγ ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I)) :=
      (continuous_const.sub (continuous_ofReal.mul continuous_const)).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  refine ((hT₁.sub (ha.mul hT₂)).const_mul (ddCoeff P)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  obtain ⟨h1, h2⟩ := efInt_ddPieces P hm hmγ hΛ hp hp' hq μ i j hε
  have e : (fun k => ddIntegrand P p' p μ ε k i j) = fun k => ddCoeff P *
      (ddPiece1 P p' p μ i j ε k - (((P.mγ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) *
        ddPiece2 P p' p μ i j ε k) :=
    funext fun k => ddIntegrand_eq P hε p' p μ i j k
  rw [e, QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul,
    efi_sub_mul ⟨h1.1, h1.2⟩ ⟨h2.1, h2.2⟩]

end Data

/-! ### Covariance -/

theorem lineKind_mom_map' {L : Matrix (Fin 4) (Fin 4) ℝ} (p p' : Fin 4 → ℝ) (k : LineKind) :
    k.mom (L *ᵥ p) (L *ᵥ p') = L *ᵥ k.mom p p' := by
  cases k <;> simp [LineKind.mom]

/-- The class limit as a combination of the two parametric matrices. -/
theorem classLimit_repDD_eq (s₀ s₁ : Fin 2) (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    {Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hY : ∀ μ i j, Tendsto (fun ε => classV (repDD s₀ s₁) { P with ε := ε } p' p μ i j)
      (𝓝[>] 0) (𝓝 (Y μ i j))) :
    ∃ V₁ V₂ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ,
      (∀ μ i j, ∃ v, IsParamValue (dd1Data P hm hmγ hΛ hp hp' hq)
        (fun ℓ => numD3 P p' p μ (ℓ 0) i j) v ∧ V₁ μ i j = v / auxLimit P.m) ∧
      (∀ μ i j, ∃ v, IsParamValue (dd2Data P hm hmγ hΛ hp hp' hq)
        (fun ℓ => numD3 P p' p μ (ℓ 0) i j) v ∧ V₂ μ i j = v / auxLimit P.m) ∧
      ∀ μ, Y μ = ((1 / I) * ddCoeff P) • (V₁ μ - ((P.mγ ^ 2 : ℝ) : ℂ) • V₂ μ) := by
  choose v₁ v₂ hv₁ hv₂ hT using fun μ i j =>
    tendsto_efi_ddIntegrand_param P hm hmγ hΛ hp hp' hq μ i j
  refine ⟨fun μ => Matrix.of fun i j => v₁ μ i j / auxLimit P.m,
    fun μ => Matrix.of fun i j => v₂ μ i j / auxLimit P.m,
    fun μ i j => ⟨v₁ μ i j, hv₁ μ i j, rfl⟩, fun μ i j => ⟨v₂ μ i j, hv₂ μ i j, rfl⟩,
    fun μ => ?_⟩
  ext i j
  have hlim := (hT μ i j).const_mul (1 / I)
  have hY' : Tendsto (fun ε => (1 / I) * QED.OneLoop.energyFirstIntegral fun k =>
      ddIntegrand P p' p μ ε k i j) (𝓝[>] 0) (𝓝 (Y μ i j)) := by
    refine (hY μ i j).congr fun ε => ?_
    rw [classV_repDD_eq]
  rw [tendsto_nhds_unique hY' hlim]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, smul_eq_mul]
  ring

/-- **Covariance of the `δ₃`–`δ₃` class limits under `L`, with the external momenta moved.** -/
theorem conj_classLimit_repDD (s₀ s₁ : Fin 2) {P : Params} (hA : ChainAdmissible P)
    {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ} (h : IsSpinLift L S T)
    {p' p : Fin 4 → ℝ} (hpq : IsPairQ P.m p' p) {Y Z : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hY : ∀ μ i j, Tendsto (fun ε => classV (repDD s₀ s₁) { P with ε := ε } p' p μ i j)
      (𝓝[>] 0) (𝓝 (Y μ i j)))
    (hZ : ∀ μ i j, Tendsto (fun ε => classV (repDD s₀ s₁) { P with ε := ε } (L *ᵥ p') (L *ᵥ p)
      μ i j) (𝓝[>] 0) (𝓝 (Z μ i j))) (μ : Fin 4) :
    S * Z μ * T = vecAct L Y μ := by
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  have hm := hA.hm
  have hmγ := hA.hmγ
  have hΛ := hA.hΛ
  have hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp
  have hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp'
  have hqL : 0 ≤ Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p) := by
    rw [← Matrix.mulVec_sub, h.dot_mulVec]; exact hq.le
  obtain ⟨V₁, V₂, hV₁, hV₂, hYV⟩ := classLimit_repDD_eq s₀ s₁ P hm hmγ hΛ hp hp' hq.le hY
  obtain ⟨W₁, W₂, hW₁, hW₂, hZW⟩ := classLimit_repDD_eq s₀ s₁ P hm hmγ hΛ hpL hpL' hqL hZ
  have hN : ∀ μ k, S * numD3 P (L *ᵥ p') (L *ᵥ p) μ (L *ᵥ k) * T =
      vecAct L (fun ν => numD3 P p' p ν k) μ := fun μ k => numD3_map h P p' p μ k
  have c₁ : ∀ μ, S * W₁ μ * T = vecAct L V₁ μ := fun μ =>
    conj_eq_vecAct_of_paramValue_div (dd1Data P hm hmγ hΛ hp hp' hq.le) h
      (fun i => (kindsDD1 i).mom (L *ᵥ p) (L *ᵥ p')) (funext fun i => lineKind_mom_map' p p' _)
      (fun μ k => numD3 P p' p μ k) (fun μ k => numD3 P (L *ᵥ p') (L *ᵥ p) μ k) hN V₁ W₁
      (auxLimit P.m) hV₁ (fun μ i j => by
        obtain ⟨v, hv, hW⟩ := hW₁ μ i j
        obtain ⟨Q, hQ, hI, rfl⟩ := IsParamValue.exists_integrableOn hv
        exact ⟨Q, hQ, hI, hW⟩) μ
  have c₂ : ∀ μ, S * W₂ μ * T = vecAct L V₂ μ := fun μ =>
    conj_eq_vecAct_of_paramValue_div (dd2Data P hm hmγ hΛ hp hp' hq.le) h
      (fun i => (kindsDD2 i).mom (L *ᵥ p) (L *ᵥ p')) (funext fun i => lineKind_mom_map' p p' _)
      (fun μ k => numD3 P p' p μ k) (fun μ k => numD3 P (L *ᵥ p') (L *ᵥ p) μ k) hN V₂ W₂
      (auxLimit P.m) hV₂ (fun μ i j => by
        obtain ⟨v, hv, hW⟩ := hW₂ μ i j
        obtain ⟨Q, hQ, hI, rfl⟩ := IsParamValue.exists_integrableOn hv
        exact ⟨Q, hQ, hI, hW⟩) μ
  have eY : Y = fun ν => ((1 / I) * ddCoeff P) • (V₁ ν - ((P.mγ ^ 2 : ℝ) : ℂ) • V₂ ν) :=
    funext hYV
  rw [hZW, eY, vecAct_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, c₁, c₂]
  congr 1
  have e2 : vecAct L (fun ν => V₁ ν - ((P.mγ ^ 2 : ℝ) : ℂ) • V₂ ν) μ =
      vecAct L V₁ μ - ((P.mγ ^ 2 : ℝ) : ℂ) • vecAct L V₂ μ := by
    simp only [vecAct, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_comm _
      ((P.mγ ^ 2 : ℝ) : ℂ)]
  rw [e2]

end QED.ChainProof.HCSide

end
