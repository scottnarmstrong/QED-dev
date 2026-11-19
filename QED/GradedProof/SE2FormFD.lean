/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2FormF
public import QED.GradedProof.SE2FormPD

/-!
# Clause 3: the class `F`

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 3: `ClassFormD` for the class `F`. The one-loop pieces have limits
`i(A(p²) p̸ ± B(p²) m)` with `A`, `B` differentiable on the region (`hasSEFormD_selfEnergy`,
`hasSEFormD_selfEnergy_twist`), the `ε`-suppressed pieces have limit `0`, and the `n₀` piece is a
self-energy piece (`SEPiece.hasSEFormD`). The assembly is that of
`QED/GradedProof/SE2FormF.lean`.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance

/-- The limit of the one-loop self-energy integrand below `-(m + ν)²`. -/
theorem tendsto_selfEnergy_seMat (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) {p : Fin 4 → ℝ} (hp : -(Q.m + ν) ^ 2 < Minkowski.dot p p)
    (α β : Fin 4) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun q => selfEnergyIntegrand Q ε p q α β)
      (𝓝[>] 0) (𝓝 (seMat (I * selfEnergyLoopA Q (Minkowski.dot p p))
        (I * (selfEnergyLoopB Q (Minkowski.dot p p) * Q.m)) p α β)) := by
  have hmγ : 0 < Q.mγ := hν0.trans_le (hν.trans (min_le_left _ _))
  have hΛ : 0 < Q.Λ := hν0.trans_le (hν.trans (min_le_right _ _))
  have h := tendsto_energyFirstIntegral_selfEnergyIntegrand hm hmγ hΛ
    (lt_of_threshold_le hm.le hν0.le (hν.trans (min_le_left _ _)) hp)
    (lt_of_threshold_le hm.le hν0.le (hν.trans (min_le_right _ _)) hp) α β
  convert h using 2
  simp only [seMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The one-loop self-energy integrand: limit differentiable along lines. -/
theorem hasSEFormD_selfEnergy (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) :
    HasSEFormD (Q.m + ν) fun ε p α β =>
      QED.OneLoop.energyFirstIntegral fun q => selfEnergyIntegrand Q ε p q α β :=
  HasSEFormD.of_seMat (fun s => I * selfEnergyLoopA Q s) (fun s => I * (selfEnergyLoopB Q s * Q.m))
    (fun _ hs => (differentiableAt_loopAB Q hm hν0 hν I hs).1)
    (fun _ hs => (differentiableAt_loopAB Q hm hν0 hν I hs).2)
    fun _ hp α β => tendsto_selfEnergy_seMat Q hm hν0 hν hp α β

/-- The twisted one-loop self-energy: limit differentiable along lines. -/
theorem hasSEFormD_selfEnergy_twist (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) :
    HasSEFormD (Q.m + ν) fun ε p α β => -(g5 α * g5 β) *
      QED.OneLoop.energyFirstIntegral fun q => selfEnergyIntegrand Q ε p q α β := by
  refine HasSEFormD.of_seMat (fun s => I * selfEnergyLoopA Q s)
    (fun s => -(I * (selfEnergyLoopB Q s * Q.m)))
    (fun s hs => (differentiableAt_loopAB Q hm hν0 hν I hs).1)
    (fun s hs => (differentiableAt_loopAB Q hm hν0 hν I hs).2.neg) fun p hp α β => ?_
  rw [← neg_g5_mul_seMat]
  exact (tendsto_selfEnergy_seMat Q hm hν0 hν hp α β).const_mul _

/-- A piece multiplied by a positive power of `ε` converges to `0`. -/
theorem hasSEFormD_eps_piece {T : ℝ} (c : ℂ) (n : ℕ) (hn : 0 < n)
    {H : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hH : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
      ∃ L, Tendsto (fun ε => H ε p α β) (𝓝[>] 0) (𝓝 L)) :
    HasSEFormD T fun ε p α β => (c * (ε : ℂ) ^ n) * H ε p α β := by
  refine HasSEFormD.of_seMat 0 0 (fun _ _ => differentiableAt_const _)
    (fun _ _ => differentiableAt_const _) fun p hp α β => ?_
  obtain ⟨L, hL⟩ := hH p hp α β
  have h := (tendsto_ofReal_mul_nhdsWithin c n).mul hL
  simp only [ofReal_zero, zero_pow hn.ne', mul_zero, zero_mul] at h
  simpa [seMat] using h

theorem hasSEFormD_F0 (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) :
    HasSEFormD (Q.m + ν) fun ε p α β => QED.OneLoop.energyFirstIntegral fun q =>
      prefF Q ε p q * numF0 Q p q α β := by
  have hmγ : 0 < Q.mγ := hν0.trans_le (hν.trans (min_le_left _ _))
  have hΛ : 0 < Q.Λ := hν0.trans_le (hν.trans (min_le_right _ _))
  obtain ⟨hMe, hMp⟩ := massesSEF_bounds Q hmγ hΛ
  exact hasSEFormD_kinds (by norm_num) kindsSEF (by decide) (massesSEF Q) hm hm hν0 hMe
    (fun i hi => (pow_le_pow_left₀ hν0.le hν 2).trans (hMp i hi)) (by decide) (by decide)
    (by decide) (numF0 Q) (fun p i j => (isLoopPoly_numF Q p i j).1)
    (fun L S S' h p k => cov_numF0 Q h p k) (isLoopPoly_numF0_p Q)
    (fun ε p q α β => prefF Q ε p q * numF0 Q p q α β)
    fun ε _ p ℓ i j => hfac_F Q p (fun q => numF0 Q p q i j) ε ℓ

theorem classFormD_repF : ClassFormD repF := by
  intro Q hQ m₀ ν _ _ _ _ hν0 hν _
  have hm := hQ.hm
  have hmγ : 0 < Q.mγ := hν0.trans_le (hν.trans (min_le_left _ _))
  have hΛ : 0 < Q.Λ := hν0.trans_le (hν.trans (min_le_right _ _))
  have hs : ∀ p : Fin 4 → ℝ, -(Q.m + ν) ^ 2 < Minkowski.dot p p →
      -(Q.m + min Q.mγ Q.Λ) ^ 2 < Minkowski.dot p p := fun p hp =>
    lt_of_threshold_le hm.le hν0.le hν hp
  set c₀ : ℂ := -(Q.δ₂ : ℂ) - (((Q.δ₂ - Q.δm) / 2 : ℝ) : ℂ)
  set c₃ : ℂ := (((Q.δ₂ - Q.δm) / 2 : ℝ) : ℂ)
  set κ := kappaSE Q.e
  have h1 := (((hasSEFormD_selfEnergy Q hm hν0 hν).const_mul c₀).add
    ((hasSEFormD_selfEnergy_twist Q hm hν0 hν).const_mul c₃)).add
    (((hasSEFormD_F0 Q hm hν0 hν).const_mul (-κ)).add
      ((hasSEFormD_eps_piece (-κ) 1 one_pos fun p hp α β =>
        (piece_F Q hm hmγ hΛ (hs p hp) (fun q => numF1 Q p q α β)
          (isLoopPoly_numF Q p α β).2.1).2).add
      (hasSEFormD_eps_piece (-κ) 2 two_pos fun p hp α β =>
        (piece_F Q hm hmγ hΛ (hs p hp) (fun q => numF2 Q p q α β)
          (isLoopPoly_numF Q p α β).2.2).2)))
  refine h1.congr fun p hp α β => ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  obtain ⟨i0, -⟩ := piece_F Q hm hmγ hΛ (hs p hp) (fun q => numF0 Q p q α β)
    (isLoopPoly_numF Q p α β).1
  obtain ⟨i1, -⟩ := piece_F Q hm hmγ hΛ (hs p hp) (fun q => numF1 Q p q α β)
    (isLoopPoly_numF Q p α β).2.1
  obtain ⟨i2, -⟩ := piece_F Q hm hmγ hΛ (hs p hp) (fun q => numF2 Q p q α β)
    (isLoopPoly_numF Q p α β).2.2
  rw [contractionValue₂_of_one_chord _ f_isChord_iff (fMom p) (f_isConserved p)
    (fun ℓ => (fMom_apply p ℓ).1) ![α] ![β] ![]
    (fun q => kappaSE Q.e * seChain (electronInsertion Q.m ε Q.δ₂ Q.δm (p + q))
      (QED.OneLoop.photonPropagator Q.mγ Q.Λ ε q) α β) p
    (fun ℓ => f_integrand { Q with ε := ε } p ℓ α β)]
  have hfun : (fun q => kappaSE Q.e * seChain (electronInsertion Q.m ε Q.δ₂ Q.δm (p + q))
        (QED.OneLoop.photonPropagator Q.mγ Q.Λ ε q) α β) =
      fun q => (c₀ + c₃ * (-(g5 α * g5 β))) * selfEnergyIntegrand Q ε p q α β +
        (-κ) * (prefF Q ε p q * numF0 Q p q α β) +
        (-κ * ε) * (prefF Q ε p q * numF1 Q p q α β) +
        (-κ * ε ^ 2) * (prefF Q ε p q * numF2 Q p q α β) := by
    funext q
    exact integrand_F_eq Q hε p q α β
  rw [hfun, energyFirstIntegral_lin4 (integrableEnergyFirst_selfEnergyIntegrand Q hε p α β)
    (i0 ε hε) (i1 ε hε) (i2 ε hε)]
  ring

end QED.GradedProof.SE2

end
