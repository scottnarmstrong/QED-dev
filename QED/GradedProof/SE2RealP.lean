/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2RealPiece
public import QED.GradedProof.SE2RealDecomp
public import QED.GradedProof.SE2FormP
public import QED.TwoLoop.UnitSCCtAssembly

/-!
# The reality class obligations for `P0`, `P1`

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57), input `SEReal`; the reality counterpart of `QED/GradedProof/SE2FormP.lean`.

The one-loop value is the joint integral of the product data divided by the auxiliary loop,
whose limit `auxLimit M = i π² / (2M²)` is imaginary
(`QED.TwoLoop.UnitSCCt.auxLimit_eq`). The numerator `κ seChain(m - (p + q)̸, photonNum(q))` is
`♯`-fixed: `κ = (ie)²(1/i)²(2π)⁻⁴` is real and the photon tensor
`photonNum = (1/i) g' (-(i/2) δ₃ (k² g - k k)) g'` is real (`conj_photonNum`). So the limit has
phase `-1` (`hasSharpLim_kinds`, `classSharp_repP0`, `classSharp_repP1`).
-/

@[expose] public section

open Complex Filter Topology Matrix
open scoped Real

namespace QED.GradedProof.SE2Real

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.SE2

/-! ### The numerator -/

theorem conj_photonNum (δ₃ mγ Λ : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) :
    starRingEnd ℂ (photonNum δ₃ mγ Λ k ν ρ) = photonNum δ₃ mγ Λ k ν ρ := by
  have e : ∀ x y z : ℝ, (1 / I) * ((x : ℂ) * (-(I / 2) * (y : ℂ)) * (z : ℂ)) =
      ((-(1 / 2) * (x * y * z) : ℝ) : ℂ) := fun x y z => by
    push_cast
    field_simp
  have h : photonNum δ₃ mγ Λ k ν ρ = ∑ a, ∑ b, ((-(1 / 2) *
      ((Minkowski.metric ν a * (Λ ^ 2 - mγ ^ 2)) *
        (δ₃ * (Minkowski.dot k k * Minkowski.metric a b - k a * k b)) *
        (Minkowski.metric ρ b * (Λ ^ 2 - mγ ^ 2))) : ℝ) : ℂ) := by
    simp only [photonNum, pvPhotonNum, photonCtFactor, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => e _ _ _
  rw [h]
  simp only [map_sum, Complex.conj_ofReal]

theorem conj_kappaSE (e : ℝ) : starRingEnd ℂ (kappaSE e) = kappaSE e := by
  simp only [kappaSE, map_mul, map_pow, map_div₀, map_one, map_inv₀, Complex.conj_I,
    Complex.conj_ofReal]
  ring

theorem sharp_kappa_numSEP (Q : Params) (p k : Fin 4 → ℝ) :
    sharp (kappaSE Q.e • numSEP Q p k) = kappaSE Q.e • numSEP Q p k := by
  rw [sharp_smul, conj_kappaSE, numSEP,
    sharp_seChain (sharp_electronNumerator _ _) (conj_photonNum _ _ _ k)]

/-! ### One-loop pieces through product data -/

/-- **One-loop self-energy integrands through product data with a `♯`-fixed numerator have a
limit with phase `-1`.** -/
theorem hasSharpLim_kinds {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
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
    (hsharp : ∀ p k, sharp (N p k) = N p k)
    (F : ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hfac : ∀ ε : ℝ, 0 < ε → ∀ p (ℓ : Fin 2 → Fin 4 → ℝ) i j,
      N p (ℓ 0) i j * ∏ k, (propDenom (Ms k) ε ((κ k).lineMom p p ℓ))⁻¹ =
        F ε p (ℓ 0) i j * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3) :
    HasSharpLim (me + μ) (-1) fun ε p i j =>
      QED.OneLoop.energyFirstIntegral fun q => F ε p q i j := by
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
  have hN1 : ∀ p ℓ, sharp (P.N p ℓ) = (1 : ℂ) • P.N p ℓ := fun p ℓ => by
    rw [one_smul]
    exact hsharp p (ℓ 0)
  have hd : starRingEnd ℂ (auxLimit mass)⁻¹ = -1 * (auxLimit mass)⁻¹ := by
    rw [QED.TwoLoop.UnitSCCt.auxLimit_eq hmass]
    simp only [map_inv₀, map_div₀, map_mul, map_pow, Complex.conj_I, Complex.conj_ofReal,
      map_ofNat]
    ring
  have hfin := SEPiece.hasSharpLim' P hN1
    (h := fun ε => (QED.OneLoop.energyFirstIntegral fun k => ((propDenom mass ε k)⁻¹) ^ 3)⁻¹)
    (hH.inv₀ hH0) hd (G := fun ε p i j => QED.OneLoop.energyFirstIntegral fun q => F ε p q i j)
  rw [mul_one] at hfin
  refine hfin fun p _ i j => ?_
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

/-- The `δ₃` self-energy integrand has the covariant form below `-(m + ν)²`. -/
theorem hasSharpLim_seP (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) :
    HasSharpLim (Q.m + ν) (-1) fun ε p α β => QED.OneLoop.energyFirstIntegral fun q =>
      kappaSE Q.e * seChain (QED.OneLoop.electronPropagator Q.m ε (p + q))
        (photonInsertion Q.δ₃ Q.mγ Q.Λ ε q) α β := by
  have hmγ : 0 < Q.mγ := hν0.trans_le (hν.trans (min_le_left _ _))
  have hΛ : 0 < Q.Λ := hν0.trans_le (hν.trans (min_le_right _ _))
  obtain ⟨hMe, hMp⟩ := massesSEP_bounds Q hmγ hΛ
  refine hasSharpLim_kinds (by norm_num) kindsSEP (by decide) (massesSEP Q) hm hm hν0 hMe
    (fun i hi => (pow_le_pow_left₀ hν0.le hν 2).trans (hMp i hi)) (by decide) (by decide)
    (by decide) (fun p k => kappaSE Q.e • numSEP Q p k)
    (fun p i j => by
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact (isLoopPoly_numSEP Q p i j).const_mul _)
    (fun L S S' h p k => cov_numSEP Q h p k) (sharp_kappa_numSEP Q)
    (fun ε p q α β => kappaSE Q.e * seChain (QED.OneLoop.electronPropagator Q.m ε (p + q))
      (photonInsertion Q.δ₃ Q.mγ Q.Λ ε q) α β)
    fun ε hε p ℓ i j => ?_
  rw [integrand_seP_eq Q hε.ne', Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsSEP, massesSEP,
    LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

theorem classSharp_repP0 : ClassSharp repP0 := by
  intro Q hQ m₀ ν _ _ _ _ hν0 hν _
  refine (hasSharpLim_seP Q hQ.hm hν0 hν).congr fun p _ α β => Eventually.of_forall fun ε => ?_
  exact (contractionValue₂_of_one_chord _ p0_isChord_iff (p0Mom p) (p0_isConserved p)
    (fun ℓ => (p0Mom_apply p ℓ).1) ![α] ![β] ![] _ p
    (fun ℓ => p0_integrand { Q with ε := ε } p ℓ α β)).symm

theorem classSharp_repP1 : ClassSharp repP1 := by
  intro Q hQ m₀ ν _ _ _ _ hν0 hν _
  refine (hasSharpLim_seP Q hQ.hm hν0 hν).congr fun p _ α β => Eventually.of_forall fun ε => ?_
  exact (contractionValue₂_of_one_chord _ p1_isChord_iff (p1Mom p) (p1_isConserved p)
    (fun ℓ => (p1Mom_apply p ℓ).1) ![α] ![β] ![] _ p
    (fun ℓ => p1_integrand { Q with ε := ε } p ℓ α β)).symm

end QED.GradedProof.SE2Real

end
