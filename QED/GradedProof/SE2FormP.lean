/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2ParamCont
public import QED.GradedProof.SE2CovTensor
public import QED.GradedProof.SE2LimP
public import QED.GradedProof.SE2FormC

/-!
# One-loop pieces through product data, and the class obligations for `P0`, `P1`

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 2.

* `hasSEForm_kinds`: a one-loop self-energy integrand `F_ε(p, q)` which, multiplied by the
  auxiliary loop `D_aux⁻³`, is a numerator `N_p(q)` over the denominators of product data given by
  line kinds (as in `exists_tendsto_of_kinds_se`), has the covariant form below `-(m_e + μ)²` if
  `N` is spinor covariant (`S N_{Lp}(Lq) S' = N_p(q)`) and polynomial in `p`. The energy-first
  integral of `F_ε` is the joint integral of the product data divided by that of the auxiliary
  loop, which converges to `auxLimit ≠ 0`; the joint integrals form a self-energy piece
  (`SEPiece`).
* `classForm_repP0`, `classForm_repP1`: the classes with the `δ₃` insertion on the internal
  photon line, whose numerator `κ seChain(m - (p + q)̸, photonNum(q))` is covariant by
  `mul_seChain_mul` and `tensorCov_photonNum`.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance

/-- The parametric data of the product data given by line kinds. -/
noncomputable def kindsData {m : ℕ} (hm : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
    (Ms : Fin (m + 1) → ℝ) (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (κ i).dir) :
    SEData where
  m := m
  α := castLoopMatrix fun i => (κ i).dir
  cs := fun i => if κ i = .inn then 1 else 0
  M := Ms
  E := {0, 1, 2, 3}
  hm := by omega
  hcrit := (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit

theorem kindsData_mom {m : ℕ} (hm : 7 ≤ m) (κ : Fin (m + 1) → LineKind) (hκ : ∀ i, κ i ≠ .out)
    (Ms : Fin (m + 1) → ℝ) (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (κ i).dir)
    (p : Fin 4 → ℝ) : (kindsData hm κ Ms hcrit).mom p = fun i => (κ i).mom p p := by
  funext i
  have := hκ i
  simp only [SEData.mom, kindsData]
  rcases h : κ i with _ | _ | _ | _ <;> simp_all [LineKind.mom]

/-- **One-loop self-energy integrands through product data have the covariant form.** -/
theorem hasSEForm_kinds {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
    (hκ : ∀ i, κ i ≠ .out) (Ms : Fin (m + 1) → ℝ) {mass : ℝ} (hmass : 0 < mass) {me μ : ℝ}
    (hme : 0 < me) (hμ : 0 < μ)
    (hMe : ∀ i, κ i ≠ .pho → me ^ 2 ≤ Ms i ^ 2) (hMp : ∀ i, κ i = .pho → μ ^ 2 ≤ Ms i ^ 2)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (κ i).dir)
    (hcard : ({0, 1, 2, 3} : Finset (Fin (m + 1))).card = 4)
    (hE : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))), κ e ≠ .aux)
    (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N p (ℓ 0) i j)
    (hcov : ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S S' : Matrix (Fin 4) (Fin 4) ℂ),
      IsSpinLift L S S' → ∀ p k, S * N (L *ᵥ p) (L *ᵥ k) * S' = N p k)
    {d : ℕ} (hpoly : ∀ k i j, IsLoopPoly 1 d fun y => N (y 0) k i j)
    (F : ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hfac : ∀ ε : ℝ, 0 < ε → ∀ p (ℓ : Fin 2 → Fin 4 → ℝ) i j,
      N p (ℓ 0) i j * ∏ k, (propDenom (Ms k) ε ((κ k).lineMom p p ℓ))⁻¹ =
        F ε p (ℓ 0) i j * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3) :
    HasSEForm (me + μ) fun ε p i j => QED.OneLoop.energyFirstIntegral fun q => F ε p q i j := by
  set D := kindsData hm7 κ Ms hcrit
  have hmom := kindsData_mom hm7 κ hκ Ms hcrit
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
  have hc : ∀ p : Fin 4 → ℝ, -(me + μ) ^ 2 < Minkowski.dot p p →
      0 < min 1 (1 + Minkowski.dot p p / (me + μ) ^ 2) * min (me ^ 2) (μ ^ 2) := fun p hs => by
    refine mul_pos (lt_min one_pos ?_) (lt_min (by positivity) (by positivity))
    have hT2 : 0 < (me + μ) ^ 2 := by positivity
    have h1 : 0 < (me + μ) ^ 2 + Minkowski.dot p p := by linarith
    calc (0 : ℝ) < ((me + μ) ^ 2 + Minkowski.dot p p) / (me + μ) ^ 2 := by positivity
      _ = 1 + Minkowski.dot p p / (me + μ) ^ 2 := by field_simp
  let P : SEPiece (me + μ) :=
    { D := D
      N := fun p ℓ => N p (ℓ 0)
      hQ := fun p i j => by
        obtain ⟨Q, hQ⟩ := (hN p i j).exists_loopQuartic
        refine ⟨Q, ⟨Or.inl hm7, ?_⟩, hQ⟩
        exact refinedBound_of_dependsOnZero _ hcard hα Q fun ℓ => by
          simp only [hQ, Matrix.cons_val_zero]
      hV := fun p hp => ⟨_, hc p hp, fun z hz hz1 hU => by
        rw [hmom p]
        exact symanzikV_kinds_se_ge κ hκ Ms hme hμ hp hMe hMp hz hz1 hU⟩
      hcov := fun L S S' h p ℓ => hcov L S S' h p (ℓ 0) }
  have hH := tendsto_energyFirstIntegral_aux hmass
  have hH0 := auxLimit_ne_zero hmass
  refine P.hasSEForm (by nlinarith [hme, hμ]) (d := d) (fun ℓ i j => hpoly (ℓ 0) i j)
    (h := fun ε => (QED.OneLoop.energyFirstIntegral fun k => ((propDenom mass ε k)⁻¹) ^ 3)⁻¹)
    (hH.inv₀ hH0) fun p _ i j => ?_
  filter_upwards [self_mem_nhdsWithin, hH.eventually_ne hH0] with ε (hε : 0 < ε) hne
  have e : (fun ℓ => P.N p ℓ i j * ∏ k, (lineDenom P.D.α (P.D.mom p) P.D.M ε k ℓ)⁻¹) =
      fun ℓ => F ε p (ℓ 0) i j * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3 := by
    funext ℓ
    show N p (ℓ 0) i j * ∏ k, (lineDenom (castLoopMatrix fun i => (κ i).dir) (D.mom p) Ms ε k
      ℓ)⁻¹ = _
    rw [hmom p, prod_lineDenom_kinds]
    exact hfac ε hε p ℓ i j
  rw [e, jointEnergyFirstIntegral_two_mul (fun q => F ε p q i j)
    (fun k => ((propDenom mass ε k)⁻¹) ^ 3)]
  exact (eq_inv_mul_iff_mul_eq₀ hne).mpr (mul_comm _ _)

/-! ### The classes `P0`, `P1` -/

theorem mulVec_add' (L : Matrix (Fin 4) (Fin 4) ℝ) (p k : Fin 4 → ℝ) :
    L *ᵥ p + L *ᵥ k = L *ᵥ (p + k) := (Matrix.mulVec_add L p k).symm

theorem cov_numSEP (Q : Params) {L : Matrix (Fin 4) (Fin 4) ℝ} {S S' : Matrix (Fin 4) (Fin 4) ℂ}
    (h : IsSpinLift L S S') (p k : Fin 4 → ℝ) :
    S * (kappaSE Q.e • numSEP Q (L *ᵥ p) (L *ᵥ k)) * S' = kappaSE Q.e • numSEP Q p k := by
  rw [Matrix.mul_smul, Matrix.smul_mul, numSEP, numSEP, mulVec_add',
    mul_seChain_mul h _ (tensorCov_photonNum h Q.δ₃ Q.mγ Q.Λ k),
    h.mul_electronNumerator_mul]

theorem isLoopAffine_add_const (k : Fin 4 → ℝ) :
    IsLoopAffine fun y : Fin 1 → Fin 4 → ℝ => y 0 + k :=
  ⟨![1], k, fun y => by simp⟩

theorem isLoopPoly_numSEP_p (Q : Params) (k : Fin 4 → ℝ) (i j : Fin 4) :
    IsLoopPoly 1 1 fun y => (kappaSE Q.e • numSEP Q (y 0) k) i j := by
  simp only [Matrix.smul_apply, smul_eq_mul]
  refine IsLoopPoly.const_mul _ ?_
  have h := isLoopPolyMat_seChain (d := 0)
    ((isLoopAffine_add_const k).isLoopPolyMat_electronNumerator Q.m)
    (fun ν ρ => IsLoopPoly.const (L := 1) (n := 0) (photonNum Q.δ₃ Q.mγ Q.Λ k ν ρ)) i j
  simpa [numSEP] using h

/-- The `δ₃` self-energy integrand has the covariant form below `-(m + ν)²`. -/
theorem hasSEForm_seP (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) :
    HasSEForm (Q.m + ν) fun ε p α β => QED.OneLoop.energyFirstIntegral fun q =>
      kappaSE Q.e * seChain (QED.OneLoop.electronPropagator Q.m ε (p + q))
        (photonInsertion Q.δ₃ Q.mγ Q.Λ ε q) α β := by
  have hmγ : 0 < Q.mγ := hν0.trans_le (hν.trans (min_le_left _ _))
  have hΛ : 0 < Q.Λ := hν0.trans_le (hν.trans (min_le_right _ _))
  obtain ⟨hMe, hMp⟩ := massesSEP_bounds Q hmγ hΛ
  refine hasSEForm_kinds (by norm_num) kindsSEP (by decide) (massesSEP Q) hm hm hν0 hMe
    (fun i hi => (pow_le_pow_left₀ hν0.le hν 2).trans (hMp i hi)) (by decide) (by decide)
    (by decide) (fun p k => kappaSE Q.e • numSEP Q p k)
    (fun p i j => by
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact (isLoopPoly_numSEP Q p i j).const_mul _)
    (fun L S S' h p k => cov_numSEP Q h p k) (isLoopPoly_numSEP_p Q)
    (fun ε p q α β => kappaSE Q.e * seChain (QED.OneLoop.electronPropagator Q.m ε (p + q))
      (photonInsertion Q.δ₃ Q.mγ Q.Λ ε q) α β)
    fun ε hε p ℓ i j => ?_
  rw [integrand_seP_eq Q hε.ne', Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsSEP, massesSEP,
    LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

theorem classForm_repP0 : ClassForm repP0 := by
  intro Q hQ m₀ ν _ _ _ _ hν0 hν _
  refine (hasSEForm_seP Q hQ.hm hν0 hν).congr fun p _ α β => Eventually.of_forall fun ε => ?_
  exact (contractionValue₂_of_one_chord _ p0_isChord_iff (p0Mom p) (p0_isConserved p)
    (fun ℓ => (p0Mom_apply p ℓ).1) ![α] ![β] ![] _ p
    (fun ℓ => p0_integrand { Q with ε := ε } p ℓ α β)).symm

theorem classForm_repP1 : ClassForm repP1 := by
  intro Q hQ m₀ ν _ _ _ _ hν0 hν _
  refine (hasSEForm_seP Q hQ.hm hν0 hν).congr fun p _ α β => Eventually.of_forall fun ε => ?_
  exact (contractionValue₂_of_one_chord _ p1_isChord_iff (p1Mom p) (p1_isConserved p)
    (fun ℓ => (p1Mom_apply p ℓ).1) ![α] ![β] ![] _ p
    (fun ℓ => p1_integrand { Q with ε := ε } p ℓ α β)).symm

end QED.GradedProof.SE2

end
