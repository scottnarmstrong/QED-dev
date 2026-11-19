/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2LimC
public import QED.GradedProof.SE2ClassP
public import QED.GradedProof.SE2Positivity

/-!
# The classes `P0`, `P1`: the `ε → 0⁺` limit

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 2, step L1.

* `exists_tendsto_of_kinds_se`: the self-energy form of
  `QED.TwoLoop.CountertermLimit.exists_tendsto_energyFirstIntegral_of_product`: a one-loop
  integrand `F_ε` that, multiplied by the auxiliary loop, is an `ε`-independent numerator over
  the denominators of product data given by kinds (no outgoing line), has an energy-first limit
  for every `p` below the threshold `-(m_e + μ)²`; the positivity of `V` is
  `symanzikV_kinds_se_ge`.
* `exists_tendsto_contractionValue₂_repP0`, `…_repP1`: the values of the classes with a `δ₃`
  insertion on the internal photon converge below the threshold `-(m + min(m_γ, Λ))²`.
-/

@[expose] public section

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open Complex Filter Topology

/-- **One-loop limits through product data in self-energy kinematics.** -/
theorem exists_tendsto_of_kinds_se {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
    (hκ : ∀ i, κ i ≠ .out) (Ms : Fin (m + 1) → ℝ) {mass : ℝ} (hmass : 0 < mass) {me μ : ℝ}
    (hme : 0 < me) (hμ : 0 < μ) (p : Fin 4 → ℝ) (hs : -(me + μ) ^ 2 < Minkowski.dot p p)
    (hMe : ∀ i, κ i ≠ .pho → me ^ 2 ≤ Ms i ^ 2) (hMp : ∀ i, κ i = .pho → μ ^ 2 ≤ Ms i ^ 2)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (κ i).dir)
    (hcard : ({0, 1, 2, 3} : Finset (Fin (m + 1))).card = 4)
    (hE : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))), κ e ≠ .aux)
    (N : (Fin 4 → ℝ) → ℂ) (hN : IsLoopPoly 2 4 fun ℓ => N (ℓ 0))
    (F : ℝ → (Fin 4 → ℝ) → ℂ)
    (hfac : ∀ ε : ℝ, 0 < ε → ∀ ℓ : Fin 2 → Fin 4 → ℝ,
      N (ℓ 0) * ∏ i, (propDenom (Ms i) ε ((κ i).lineMom p p ℓ))⁻¹ =
        F ε (ℓ 0) * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3) :
    ∃ L : ℂ, Tendsto (fun ε => QED.OneLoop.energyFirstIntegral (F ε)) (𝓝[>] 0) (𝓝 L) := by
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
  have hc : 0 < min 1 (1 + Minkowski.dot p p / (me + μ) ^ 2) * min (me ^ 2) (μ ^ 2) := by
    refine mul_pos (lt_min one_pos ?_) (lt_min (by positivity) (by positivity))
    have hT2 : 0 < (me + μ) ^ 2 := by positivity
    have h1 : 0 < (me + μ) ^ 2 + Minkowski.dot p p := by linarith
    calc (0 : ℝ) < ((me + μ) ^ 2 + Minkowski.dot p p) / (me + μ) ^ 2 := by positivity
      _ = 1 + Minkowski.dot p p / (me + μ) ^ 2 := by field_simp
  refine exists_tendsto_energyFirstIntegral_of_product hm7 (castLoopMatrix fun i => (κ i).dir)
    (fun i => (κ i).mom p p) Ms Q ((noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit)
    hB hc (fun z hz hz1 hU => symanzikV_kinds_se_ge κ hκ Ms hme hμ hs hMe hMp hz hz1 hU) hmass F
    fun ε hε ℓ => ?_
  rw [hQ, prod_lineDenom_kinds]
  exact hfac ε hε ℓ

/-- The masses of the product data for `δ₃` against the self-energy bounds. -/
theorem massesSEP_bounds (Q : Params) (hmγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ) :
    (∀ i, kindsSEP i ≠ .pho → Q.m ^ 2 ≤ massesSEP Q i ^ 2) ∧
      (∀ i, kindsSEP i = .pho → min Q.mγ Q.Λ ^ 2 ≤ massesSEP Q i ^ 2) := by
  obtain ⟨h1, h2⟩ := sq_min_le Q hmγ hΛ
  constructor <;> intro i hi <;> fin_cases i <;> simp_all [kindsSEP, massesSEP]

/-- The `δ₃` self-energy integrand converges below threshold. -/
theorem exists_tendsto_seP {Q : Params} (hm : 0 < Q.m) (hmγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ)
    {p : Fin 4 → ℝ} (hs : -(Q.m + min Q.mγ Q.Λ) ^ 2 < Minkowski.dot p p) (α β : Fin 4) :
    ∃ L : ℂ, Tendsto (fun ε : ℝ => QED.OneLoop.energyFirstIntegral fun q =>
      kappaSE Q.e * seChain (QED.OneLoop.electronPropagator Q.m ε (p + q))
        (photonInsertion Q.δ₃ Q.mγ Q.Λ ε q) α β) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨hMe, hMp⟩ := massesSEP_bounds Q hmγ hΛ
  exact exists_tendsto_of_kinds_se (by norm_num) kindsSEP (by decide) (massesSEP Q) hm hm
    (lt_min hmγ hΛ) p hs hMe hMp (by decide) (by decide) (by decide)
    (fun k => kappaSE Q.e * numSEP Q p k α β) ((isLoopPoly_numSEP Q p α β).const_mul _)
    (fun ε q => kappaSE Q.e * seChain (QED.OneLoop.electronPropagator Q.m ε (p + q))
        (photonInsertion Q.δ₃ Q.mγ Q.Λ ε q) α β)
    fun ε hε ℓ => by
      rw [integrand_seP_eq Q hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsSEP, massesSEP,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring

/-- **The limit of the class `P0`** exists below threshold. -/
theorem exists_tendsto_contractionValue₂_repP0 {Q : Params} (hm : 0 < Q.m) (hmγ : 0 < Q.mγ)
    (hΛ : 0 < Q.Λ) {p : Fin 4 → ℝ} (hs : -(Q.m + min Q.mγ Q.Λ) ^ 2 < Minkowski.dot p p)
    (α β : Fin 4) :
    ∃ L : ℂ, Tendsto (fun ε : ℝ =>
      contractionValue₂ { Q with ε := ε } repP0 ![p] ![p] ![] ![α] ![β] ![]) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨L, hL⟩ := exists_tendsto_seP hm hmγ hΛ hs α β
  refine ⟨L, hL.congr fun ε => ?_⟩
  exact (contractionValue₂_of_one_chord _ p0_isChord_iff (p0Mom p) (p0_isConserved p)
    (fun ℓ => (p0Mom_apply p ℓ).1) ![α] ![β] ![] _ p
    (fun ℓ => p0_integrand { Q with ε := ε } p ℓ α β)).symm

/-- **The limit of the class `P1`** exists below threshold. -/
theorem exists_tendsto_contractionValue₂_repP1 {Q : Params} (hm : 0 < Q.m) (hmγ : 0 < Q.mγ)
    (hΛ : 0 < Q.Λ) {p : Fin 4 → ℝ} (hs : -(Q.m + min Q.mγ Q.Λ) ^ 2 < Minkowski.dot p p)
    (α β : Fin 4) :
    ∃ L : ℂ, Tendsto (fun ε : ℝ =>
      contractionValue₂ { Q with ε := ε } repP1 ![p] ![p] ![] ![α] ![β] ![]) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨L, hL⟩ := exists_tendsto_seP hm hmγ hΛ hs α β
  refine ⟨L, hL.congr fun ε => ?_⟩
  exact (contractionValue₂_of_one_chord _ p1_isChord_iff (p1Mom p) (p1_isConserved p)
    (fun ℓ => (p1Mom_apply p ℓ).1) ![α] ![β] ![] _ p
    (fun ℓ => p1_integrand { Q with ε := ε } p ℓ α β)).symm

end QED.GradedProof.SE2

end
