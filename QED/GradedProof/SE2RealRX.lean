/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2RealPiece
public import QED.GradedProof.SE2RealDecomp
public import QED.GradedProof.SE2FormRX

/-!
# The reality class obligations for `R`, `X`

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57), input `SEReal`; the reality counterpart of `QED/GradedProof/SE2FormRX.lean`.

The numerators are `(ie)⁴ (1/i)³ chain4 w (E₃, E₂, E₁) = ie⁴ chain4 …` with electron numerators
`Eₖ` (`♯`-fixed) and the photon weights `w = pvEta · pvEta`, products of two `(1/i) · real`
factors, hence real (`conj_wR`, `conj_wX`). So `N♯ = -N` (`sharp_numG_repR`, `sharp_numG_repX`),
and `hasSharpLim_gggg` (the piece of `hasSEForm_gggg` with the symmetry) gives
`classSharp_repR`, `classSharp_repX`.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.SE2Real

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.TwoLoop.Relabel QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix RefinedBound
  IntNoSubdivergenceRefined symanzikU symanzikV noSubdivergenceRefined_castLoopMatrix_iff)
open QED.GradedProof.SE2

/-! ### The numerators -/

theorem conj_pvEta (Q : Params) (x y : Fin 4) :
    starRingEnd ℂ (pvEta Q x y) = -pvEta Q x y := by
  simp only [pvEta, map_mul, map_div₀, map_one, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem conj_wR (Q : Params) (x : Fin 4 → Fin 4) : starRingEnd ℂ (wR Q x) = wR Q x := by
  rw [wR, map_mul, conj_pvEta, conj_pvEta, neg_mul_neg]

theorem conj_wX (Q : Params) (x : Fin 4 → Fin 4) : starRingEnd ℂ (wX Q x) = wX Q x := by
  rw [wX, map_mul, conj_pvEta, conj_pvEta, neg_mul_neg]

/-- An open chain with a real weight and `♯`-fixed insertions is `♯`-fixed. -/
theorem sharp_chain4 {w : (Fin 4 → Fin 4) → ℂ} (hw : ∀ x, starRingEnd ℂ (w x) = w x)
    {E₃ E₂ E₁ : Matrix (Fin 4) (Fin 4) ℂ} (h₃ : sharp E₃ = E₃) (h₂ : sharp E₂ = E₂)
    (h₁ : sharp E₁ = E₁) : sharp (chain4 w E₃ E₂ E₁) = chain4 w E₃ E₂ E₁ := by
  simp only [chain4, chainG, sharp_sum, sharp_smul, sharp_mul, sharp_gamma, hw, h₃, h₂, h₁]

theorem conj_coupling (Q : Params) :
    starRingEnd ℂ ((I * Q.e) ^ 4 * (1 / I) ^ 3) = -((I * Q.e) ^ 4 * (1 / I) ^ 3) := by
  simp only [map_mul, map_pow, map_div₀, map_one, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem sharp_numG_repR (Q : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    sharp (numG Q repR p ℓ) = (-1 : ℂ) • numG Q repR p ℓ := by
  rw [numG_repR, sharp_smul, conj_coupling, sharp_chain4 (conj_wR Q)
    (sharp_electronNumerator _ _) (sharp_electronNumerator _ _) (sharp_electronNumerator _ _),
    smul_smul, neg_one_mul]

theorem sharp_numG_repX (Q : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    sharp (numG Q repX p ℓ) = (-1 : ℂ) • numG Q repX p ℓ := by
  rw [numG_repX, sharp_smul, conj_coupling, sharp_chain4 (conj_wX Q)
    (sharp_electronNumerator _ _) (sharp_electronNumerator _ _) (sharp_electronNumerator _ _),
    smul_smul, neg_one_mul]

/-! ### The pieces and the classes -/

/-- **A two-loop contraction of four `gauge` vertices with a `♯`-symmetric numerator has a
`♯`-symmetric limit.** -/
theorem hasSharpLim_gggg (C : Contraction 1 0 k_gggg)
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (hL : loopCount C = 2)
    (hcard : Fintype.card (FermionLine C) = 3) (a : Fin 7 → Fin 2 → ℤ)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2} a) (Q : Params) (cs : Fin 7 → ℝ)
    (e : FermionLine C → Fin 7) (he : Function.Injective e)
    (hE : ∀ f, e f ∈ ({0, 1, 2} : Finset (Fin 7)))
    (hk : ∀ p ℓ f, lineMomentum₂ C ![p] ![p] ![] ℓ (.inl f) =
      lineMomentum (castLoopMatrix a) (fun i => cs i • p) (e f) ℓ)
    (hden : ∀ (ε : ℝ) p ℓ, amplitudeDenominator { Q with ε := ε } C (zeroFlavoring k_gggg)
      (lineMomentum₂ C ![p] ![p] ![] ℓ) =
        ∏ i, (lineDenom (castLoopMatrix a) (fun i => cs i • p) (massesSE Q) ε i ℓ)⁻¹)
    {T : ℝ} (_hT : 0 < T)
    (hV : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → ∃ c : ℝ, 0 < c ∧
      ∀ z : Fin 7 → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU (castLoopMatrix a) z ≠ 0 →
        c ≤ symanzikV (castLoopMatrix a) (fun i => cs i • p) (massesSE Q) z)
    (hcov : ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S S' : Matrix (Fin 4) (Fin 4) ℂ),
      IsSpinLift L S S' → ∀ p ℓ, S * numG Q C (L *ᵥ p) (loopAct L ℓ) * S' = numG Q C p ℓ)
    {c : ℂ} (hsharp : ∀ p ℓ, sharp (numG Q C p ℓ) = c • numG Q C p ℓ) :
    HasSharpLim T c fun ε p α β =>
      contractionValue₂ { Q with ε := ε } C ![p] ![p] ![] ![α] ![β] ![] := by
  set κ : ℂ := (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ with hκ
  let D : SEData :=
    { m := 6
      α := castLoopMatrix a
      cs := cs
      M := massesSE Q
      E := {0, 1, 2}
      hm := le_refl _
      hcrit := (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit }
  have haff : ∀ p (f : FermionLine C),
      IsLoopAffine fun ℓ => lineMomentum₂ C ![p] ![p] ![] ℓ (.inl f) := fun p f => by
    rw [show (fun ℓ => lineMomentum₂ C ![p] ![p] ![] ℓ (.inl f)) =
      lineMomentum (castLoopMatrix a) (fun i => cs i • p) (e f) from funext fun ℓ => hk p ℓ f]
    exact isLoopAffine_lineMomentum _ _ _
  let P : SEPiece T :=
    { D := D
      N := fun p ℓ => κ • numG Q C p ℓ
      hQ := fun p i j => by
        have hpoly := isLoopPoly_amplitudeNumerator_gggg Q C (zeroFlavoring k_gggg) ![p] ![]
          (fun ℓ => lineMomentum₂ C ![p] ![p] ![] ℓ) (haff p) ![i] ![j] ![]
        rw [hcard] at hpoly
        obtain ⟨P', hq, hP⟩ := IsLoopPoly.exists_loopQuartic_cubic (hpoly.const_mul κ)
        refine ⟨P', ⟨Or.inr hq, ?_⟩, ?_⟩
        · rw [hP]
          have h := (refinedBound_amplitudeNumerator_gggg Q C (zeroFlavoring k_gggg) ![p] ![]
            (castLoopMatrix a) (fun i => cs i • p) (fun ℓ => lineMomentum₂ C ![p] ![p] ![] ℓ)
            e he (fun ℓ f => hk p ℓ f) ![i] ![j] ![]).const_mul κ
          rw [hcard] at h
          refine h.mono ?_ (by norm_num)
          intro x hx
          obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hx
          exact hE f
        · rw [hP]
          rfl
      hV := hV
      hcov := fun L S S' h p ℓ => by
        rw [Matrix.mul_smul, Matrix.smul_mul, hcov L S S' h p ℓ] }
  have hN : ∀ p ℓ, sharp (P.N p ℓ) = c • P.N p ℓ := fun p ℓ => by
    show sharp (κ • numG Q C p ℓ) = c • (κ • numG Q C p ℓ)
    rw [sharp_smul, hκ, map_inv₀, Complex.conj_ofReal, hsharp, smul_comm]
  refine SEPiece.hasSharpLim P hN (h := fun _ => 1) (h₀ := 1) (by simp) fun p _ i j => ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  show contractionValue₂ { Q with ε := ε } C ![p] ![p] ![] ![i] ![j] ![] =
    1 * QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ =>
      κ * amplitudeNumerator Q C (zeroFlavoring k_gggg) ![p] ![]
        (lineMomentum₂ C ![p] ![p] ![] ℓ) ![i] ![j] ![] *
      ∏ k, (lineDenom (castLoopMatrix a) (fun i => cs i • p) (massesSE Q) ε k ℓ)⁻¹)
  rw [one_mul]
  unfold contractionValue₂
  rw [hL]
  congr 1
  funext ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring _ hcyc,
    contractionAmplitude₂_eq { Q with ε := ε } hε.ne', hden ε p ℓ, hκ, ← mul_assoc]
  rfl

theorem classSharp_repR : ClassSharp repR := by
  intro Q hQ m₀ ν _ _ _ _ hν0 hν _
  have hm := hQ.hm
  obtain ⟨i1, i2, i3, -, -⟩ := idxR_apply
  refine hasSharpLim_gggg repR (sameCycle_of_pow (n := 5) (by decide +kernel)) loopCount_repR
    (by decide +kernel) aR intCrit_R Q aRc (fun f => idxR (.inl f)) ?_ ?_
    (fun p ℓ f => by rw [lineMomentum₂_repR, rMom, ppR_eq])
    (fun ε p ℓ => by rw [← ppR_eq]; exact r_denominator { Q with ε := ε } p ℓ)
    (by positivity) (fun p hp => ⟨min 1 (1 + Minkowski.dot p p / (Q.m + ν) ^ 2) *
      min (Q.m ^ 2) (ν ^ 2), min_one_mul_pos (by positivity)
      (lt_min (by positivity) (by positivity)) hp, fun z hz hz1 hU => by
        rw [← ppR_eq]; exact symanzikV_R_ge Q hm hν0 hν hp hz hz1 hU⟩)
    (fun L S S' h p ℓ => cov_numG_repR Q h p ℓ) (sharp_numG_repR Q)
  · intro f g h
    rcases r_fermionLine_cases f with rfl | rfl | rfl <;>
      rcases r_fermionLine_cases g with rfl | rfl | rfl <;>
      simp_all
  · intro f
    rcases r_fermionLine_cases f with rfl | rfl | rfl <;> simp [i1, i2, i3]

theorem classSharp_repX : ClassSharp repX := by
  intro Q hQ m₀ ν _ hm₀ _ _ hν0 hν hν2
  have hm := hQ.hm
  have hν2' : ν ≤ 2 * Q.m := hν2.trans (by linarith)
  obtain ⟨i1, i2, i3, -, -⟩ := idxX_apply
  refine hasSharpLim_gggg repX (sameCycle_of_pow (n := 5) (by decide +kernel)) loopCount_repX
    (by decide +kernel) aX intCrit_X Q aXc (fun f => idxX (.inl f)) ?_ ?_
    (fun p ℓ f => by rw [lineMomentum₂_repX, xMom, ppX_eq])
    (fun ε p ℓ => by rw [← ppX_eq]; exact x_denominator { Q with ε := ε } p ℓ)
    (by positivity) (fun p hp => ⟨min 1 (1 + Minkowski.dot p p / (Q.m + ν) ^ 2) *
      min (Q.m ^ 2) (ν ^ 2), min_one_mul_pos (by positivity)
      (lt_min (by positivity) (by positivity)) hp, fun z hz hz1 hU => by
        rw [← ppX_eq]; exact symanzikV_X_ge Q hm hν0 hν hν2' hp hz hz1 hU⟩)
    (fun L S S' h p ℓ => cov_numG_repX Q h p ℓ) (sharp_numG_repX Q)
  · intro f g h
    rcases x_fermionLine_cases f with rfl | rfl | rfl <;>
      rcases x_fermionLine_cases g with rfl | rfl | rfl <;>
      simp_all
  · intro f
    rcases x_fermionLine_cases f with rfl | rfl | rfl <;> simp [i1, i2, i3]

end QED.GradedProof.SE2Real

end
