/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2RealP
public import QED.GradedProof.SE2RealC
public import QED.GradedProof.SE2FormF

/-!
# The reality class obligation for `F`

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57), input `SEReal`; the reality counterpart of `QED/GradedProof/SE2FormF.lean`.

The integrand of `repF` is `(c₀ + c₃ (-(γ⁵)_{αα} (γ⁵)_{ββ})) Σ_m + (-κ) D⁻³ D_γ⁻¹ D_Λ⁻¹
(n₀ + ε n₁ + ε² n₂)` with real `c₀, c₃, κ`:

* `Σ_m` converges to `i (A p̸ + B m)` with real `A, B`, phase `-1` (`hasSharpLim_selfEnergy`),
  and so does its `γ⁵`-twist `i (A p̸ - B m)` (`hasSharpLim_selfEnergy_twist`);
* the `n₀` numerator `seChain(D_m(p+q) R(p+q), g')` has real coefficients, so is `♯`-fixed
  (`sharp_numF0`), and `hasSharpLim_kinds` gives phase `-1` (`hasSharpLim_F0`);
* the `ε`, `ε²` pieces converge to `0` (`hasSharpLim_eps_piece`).
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.SE2Real

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.SE2

/-- A covariant matrix with imaginary coefficients is `♯`-odd. -/
theorem sharp_seMat_of_conj {a b : ℂ} (ha : starRingEnd ℂ a = -a) (hb : starRingEnd ℂ b = -b)
    (p : Fin 4 → ℝ) : sharp (seMat a b p) = (-1 : ℂ) • seMat a b p := by
  rw [seMat, sharp_seForm, ha, hb, neg_one_smul, neg_add, neg_smul, neg_smul]

theorem conj_I_mul_ofReal (x : ℂ) (hx : starRingEnd ℂ x = x) :
    starRingEnd ℂ (I * x) = -(I * x) := by
  rw [map_mul, Complex.conj_I, hx, neg_mul]

/-- The one-loop self-energy integrand has a limit with phase `-1`. -/
theorem hasSharpLim_selfEnergy (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) :
    HasSharpLim (Q.m + ν) (-1) fun ε p α β =>
      QED.OneLoop.energyFirstIntegral fun q => selfEnergyIntegrand Q ε p q α β := by
  have hmγ : 0 < Q.mγ := hν0.trans_le (hν.trans (min_le_left _ _))
  have hΛ : 0 < Q.Λ := hν0.trans_le (hν.trans (min_le_right _ _))
  refine ⟨fun p => seMat (I * selfEnergyLoopA Q (Minkowski.dot p p))
    (I * (selfEnergyLoopB Q (Minkowski.dot p p) * Q.m)) p, fun p hp => ⟨fun α β => ?_, ?_⟩⟩
  · have h := tendsto_energyFirstIntegral_selfEnergyIntegrand hm hmγ hΛ
      (lt_of_threshold_le hm.le hν0.le (hν.trans (min_le_left _ _)) hp)
      (lt_of_threshold_le hm.le hν0.le (hν.trans (min_le_right _ _)) hp) α β
    convert h using 2
    simp only [seMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · exact sharp_seMat_of_conj (conj_I_mul_ofReal _ (conj_selfEnergyLoopA _ _))
      (conj_I_mul_ofReal _ (by rw [map_mul, conj_selfEnergyLoopB, Complex.conj_ofReal])) p

/-- The twisted one-loop self-energy has a limit with phase `-1`. -/
theorem hasSharpLim_selfEnergy_twist (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) :
    HasSharpLim (Q.m + ν) (-1) fun ε p α β => -(g5 α * g5 β) *
      QED.OneLoop.energyFirstIntegral fun q => selfEnergyIntegrand Q ε p q α β := by
  have hmγ : 0 < Q.mγ := hν0.trans_le (hν.trans (min_le_left _ _))
  have hΛ : 0 < Q.Λ := hν0.trans_le (hν.trans (min_le_right _ _))
  refine ⟨fun p => seMat (I * selfEnergyLoopA Q (Minkowski.dot p p))
    (-(I * (selfEnergyLoopB Q (Minkowski.dot p p) * Q.m))) p, fun p hp => ⟨fun α β => ?_, ?_⟩⟩
  · beta_reduce
    rw [← neg_g5_mul_seMat]
    refine Tendsto.const_mul _ ?_
    have h := tendsto_energyFirstIntegral_selfEnergyIntegrand hm hmγ hΛ
      (lt_of_threshold_le hm.le hν0.le (hν.trans (min_le_left _ _)) hp)
      (lt_of_threshold_le hm.le hν0.le (hν.trans (min_le_right _ _)) hp) α β
    convert h using 2
    simp only [seMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · refine sharp_seMat_of_conj (conj_I_mul_ofReal _ (conj_selfEnergyLoopA _ _)) ?_ p
    rw [map_neg, conj_I_mul_ofReal _ (by rw [map_mul, conj_selfEnergyLoopB, Complex.conj_ofReal])]

/-- A piece multiplied by a positive power of `ε` converges to `0`. -/
theorem hasSharpLim_eps_piece {T : ℝ} {c' : ℂ} (c : ℂ) (n : ℕ) (hn : 0 < n)
    {H : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hH : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
      ∃ L, Tendsto (fun ε => H ε p α β) (𝓝[>] 0) (𝓝 L)) :
    HasSharpLim T c' fun ε p α β => (c * (ε : ℂ) ^ n) * H ε p α β := by
  refine ⟨fun _ => 0, fun p hp => ⟨fun α β => ?_, by rw [sharp_zero, smul_zero]⟩⟩
  obtain ⟨L, hL⟩ := hH p hp α β
  have h := (tendsto_ofReal_mul_nhdsWithin c n).mul hL
  simp only [ofReal_zero, zero_pow hn.ne', mul_zero, zero_mul] at h
  simpa using h

/-! ### The `n₀` piece -/

theorem sharp_numF0 (Q : Params) (p k : Fin 4 → ℝ) : sharp (numF0 Q p k) = numF0 Q p k := by
  have hR : sharp (propDenom Q.m 0 (p + k) • insR Q.m 0 Q.δ₂ Q.δm (p + k)) =
      propDenom Q.m 0 (p + k) • insR Q.m 0 Q.δ₂ Q.δm (p + k) := by
    simp only [propDenom, insR, sharp_smul, sharp_add, sharp_one, sharp_electronNumerator,
      map_sub, map_mul, Complex.conj_ofReal, map_ofNat, map_pow,
      Complex.ofReal_zero, zero_mul, sub_zero, map_zero, zero_add]
  rw [numF0, sharp_seChain hR fun ν ρ => by rw [pvPhotonNum, Complex.conj_ofReal]]

theorem hasSharpLim_F0 (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) :
    HasSharpLim (Q.m + ν) (-1) fun ε p α β => QED.OneLoop.energyFirstIntegral fun q =>
      prefF Q ε p q * numF0 Q p q α β := by
  have hmγ : 0 < Q.mγ := hν0.trans_le (hν.trans (min_le_left _ _))
  have hΛ : 0 < Q.Λ := hν0.trans_le (hν.trans (min_le_right _ _))
  obtain ⟨hMe, hMp⟩ := massesSEF_bounds Q hmγ hΛ
  exact hasSharpLim_kinds (by norm_num) kindsSEF (by decide) (massesSEF Q) hm hm hν0 hMe
    (fun i hi => (pow_le_pow_left₀ hν0.le hν 2).trans (hMp i hi)) (by decide) (by decide)
    (by decide) (numF0 Q) (fun p i j => (isLoopPoly_numF Q p i j).1)
    (fun L S S' h p k => cov_numF0 Q h p k) (sharp_numF0 Q)
    (fun ε p q α β => prefF Q ε p q * numF0 Q p q α β)
    fun ε _ p ℓ i j => hfac_F Q p (fun q => numF0 Q p q i j) ε ℓ

/-! ### The class `F` -/

theorem classSharp_repF : ClassSharp repF := by
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
  have hc₀ : starRingEnd ℂ c₀ = c₀ := by simp only [c₀, map_sub, map_neg, Complex.conj_ofReal]
  have hc₃ : starRingEnd ℂ c₃ = c₃ := Complex.conj_ofReal _
  have hκ : starRingEnd ℂ (-κ) = -κ := by rw [map_neg, conj_kappaSE]
  have h1 := (((hasSharpLim_selfEnergy Q hm hν0 hν).const_mul_conj c₀ hc₀).add
    ((hasSharpLim_selfEnergy_twist Q hm hν0 hν).const_mul_conj c₃ hc₃)).add
    (((hasSharpLim_F0 Q hm hν0 hν).const_mul_conj (-κ) hκ).add
      ((hasSharpLim_eps_piece (-κ) 1 one_pos fun p hp α β =>
        (piece_F Q hm hmγ hΛ (hs p hp) (fun q => numF1 Q p q α β)
          (isLoopPoly_numF Q p α β).2.1).2).add
      (hasSharpLim_eps_piece (-κ) 2 two_pos fun p hp α β =>
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

end QED.GradedProof.SE2Real

end
