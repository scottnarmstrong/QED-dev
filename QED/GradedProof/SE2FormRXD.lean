/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2FormRX
public import QED.GradedProof.SE2FormPD

/-!
# Clause 3: the classes `R`, `X`

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 3: `ClassFormD` for the classes `R`, `X`. The proofs are those of
`QED/GradedProof/SE2FormRX.lean` with `SEPiece.hasSEFormD` in place of `SEPiece.hasSEForm`.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.TwoLoop.Relabel QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix RefinedBound
  IntNoSubdivergenceRefined symanzikU symanzikV noSubdivergenceRefined_castLoopMatrix_iff)

/-- **Two-loop self-energy contractions of four `gauge` vertices with covariant numerators have
the covariant form.** -/
theorem hasSEFormD_gggg (C : Contraction 1 0 k_gggg)
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
    {T : ℝ} (hT : 0 < T)
    (hV : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → ∃ c : ℝ, 0 < c ∧
      ∀ z : Fin 7 → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU (castLoopMatrix a) z ≠ 0 →
        c ≤ symanzikV (castLoopMatrix a) (fun i => cs i • p) (massesSE Q) z)
    (hcov : ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S S' : Matrix (Fin 4) (Fin 4) ℂ),
      IsSpinLift L S S' → ∀ p ℓ, S * numG Q C (L *ᵥ p) (loopAct L ℓ) * S' = numG Q C p ℓ) :
    HasSEFormD T fun ε p α β =>
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
  refine P.hasSEFormD (by nlinarith) (d := 3) (fun ℓ i j => ?_) (h := fun _ => 1)
    tendsto_const_nhds fun p _ i j => ?_
  · show IsLoopPoly 1 3 fun y => κ * amplitudeNumerator Q C (zeroFlavoring k_gggg) ![y 0] ![]
      (lineMomentum₂ C ![y 0] ![y 0] ![] ℓ) ![i] ![j] ![]
    have hpoly := isLoopPoly_amplitudeNumerator_gggg Q C (zeroFlavoring k_gggg) ![0] ![]
      (fun y : Fin 1 → Fin 4 → ℝ => lineMomentum₂ C ![y 0] ![y 0] ![] ℓ) (fun f => by
        rw [show (fun y : Fin 1 → Fin 4 → ℝ => lineMomentum₂ C ![y 0] ![y 0] ![] ℓ (.inl f)) =
          fun y => lineMomentum (castLoopMatrix a) (fun i => cs i • y 0) (e f) ℓ from
            funext fun y => hk (y 0) ℓ f]
        exact ⟨![cs (e f)], lineMomentum (castLoopMatrix a) 0 (e f) ℓ,
          lineMomentum_smul_eq _ _ _ ℓ⟩) ![i] ![j] ![]
    rw [hcard] at hpoly
    refine (congrArg (IsLoopPoly 1 3) (funext fun y => ?_)).mp (hpoly.const_mul κ)
    rw [amplitudeNumerator_gggg_pIn Q C _ ![0] ![y 0]]
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
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

theorem classFormD_repR : ClassFormD repR := by
  intro Q hQ m₀ ν _ _ _ _ hν0 hν _
  have hm := hQ.hm
  obtain ⟨i1, i2, i3, -, -⟩ := idxR_apply
  refine hasSEFormD_gggg repR (sameCycle_of_pow (n := 5) (by decide +kernel)) loopCount_repR
    (by decide +kernel) aR intCrit_R Q aRc (fun f => idxR (.inl f)) ?_ ?_
    (fun p ℓ f => by rw [lineMomentum₂_repR, rMom, ppR_eq])
    (fun ε p ℓ => by rw [← ppR_eq]; exact r_denominator { Q with ε := ε } p ℓ)
    (by positivity) (fun p hp => ⟨min 1 (1 + Minkowski.dot p p / (Q.m + ν) ^ 2) *
      min (Q.m ^ 2) (ν ^ 2), min_one_mul_pos (by positivity)
      (lt_min (by positivity) (by positivity)) hp, fun z hz hz1 hU => by
        rw [← ppR_eq]; exact symanzikV_R_ge Q hm hν0 hν hp hz hz1 hU⟩)
    fun L S S' h p ℓ => cov_numG_repR Q h p ℓ
  · intro f g h
    rcases r_fermionLine_cases f with rfl | rfl | rfl <;>
      rcases r_fermionLine_cases g with rfl | rfl | rfl <;>
      simp_all
  · intro f
    rcases r_fermionLine_cases f with rfl | rfl | rfl <;> simp [i1, i2, i3]

theorem classFormD_repX : ClassFormD repX := by
  intro Q hQ m₀ ν _ hm₀ _ _ hν0 hν hν2
  have hm := hQ.hm
  have hν2' : ν ≤ 2 * Q.m := hν2.trans (by linarith)
  obtain ⟨i1, i2, i3, -, -⟩ := idxX_apply
  refine hasSEFormD_gggg repX (sameCycle_of_pow (n := 5) (by decide +kernel)) loopCount_repX
    (by decide +kernel) aX intCrit_X Q aXc (fun f => idxX (.inl f)) ?_ ?_
    (fun p ℓ f => by rw [lineMomentum₂_repX, xMom, ppX_eq])
    (fun ε p ℓ => by rw [← ppX_eq]; exact x_denominator { Q with ε := ε } p ℓ)
    (by positivity) (fun p hp => ⟨min 1 (1 + Minkowski.dot p p / (Q.m + ν) ^ 2) *
      min (Q.m ^ 2) (ν ^ 2), min_one_mul_pos (by positivity)
      (lt_min (by positivity) (by positivity)) hp, fun z hz hz1 hU => by
        rw [← ppX_eq]; exact symanzikV_X_ge Q hm hν0 hν hν2' hp hz hz1 hU⟩)
    fun L S S' h p ℓ => cov_numG_repX Q h p ℓ
  · intro f g h
    rcases x_fermionLine_cases f with rfl | rfl | rfl <;>
      rcases x_fermionLine_cases g with rfl | rfl | rfl <;>
      simp_all
  · intro f
    rcases x_fermionLine_cases f with rfl | rfl | rfl <;> simp [i1, i2, i3]

end QED.GradedProof.SE2

end
