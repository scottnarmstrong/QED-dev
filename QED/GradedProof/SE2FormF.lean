/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2FormP
public import QED.GradedProof.SE2LimF

/-!
# The class obligation of clause 2 for `F`

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 2. By `integrand_F_eq` the integrand of `repF` at `ε > 0` is

`(c₀ + c₃ (-(γ⁵)_{αα} (γ⁵)_{ββ})) Σ_m + (-κ) D⁻³ D_γ⁻¹ D_Λ⁻¹ (n₀ + ε n₁ + ε² n₂)`,

and each term has the covariant form:

* `Σ_m` converges to `i (A(p²) p̸ + B(p²) m)` (`hasSEForm_selfEnergy`), and the entrywise
  `γ⁵`-twist maps `a p̸ + b` to `a p̸ - b` (`neg_g5_mul_seMat`);
* the `n₀` piece is a one-loop piece through product data (`hasSEForm_kinds`) whose numerator
  `seChain(D_m(p+q) R(p+q), g (Λ² - m_γ²))` is spinor covariant (`cov_numF0`);
* the `ε n₁`, `ε² n₂` pieces converge to `0` (`hasSEForm_eps_piece`).
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance

/-- The one-loop self-energy integrand has the covariant form below `-(m + ν)²`. -/
theorem hasSEForm_selfEnergy (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) :
    HasSEForm (Q.m + ν) fun ε p α β =>
      QED.OneLoop.energyFirstIntegral fun q => selfEnergyIntegrand Q ε p q α β := by
  have hmγ : 0 < Q.mγ := hν0.trans_le (hν.trans (min_le_left _ _))
  have hΛ : 0 < Q.Λ := hν0.trans_le (hν.trans (min_le_right _ _))
  refine ⟨fun s => I * selfEnergyLoopA Q s, fun s => I * (selfEnergyLoopB Q s * Q.m),
    fun p hp α β => ?_⟩
  have h := tendsto_energyFirstIntegral_selfEnergyIntegrand hm hmγ hΛ
    (lt_of_threshold_le hm.le hν0.le (hν.trans (min_le_left _ _)) hp)
    (lt_of_threshold_le hm.le hν0.le (hν.trans (min_le_right _ _)) hp) α β
  convert h using 2
  simp only [seMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The entrywise `γ⁵`-twist of `a p̸ + b` is `a p̸ - b`. -/
theorem neg_g5_mul_seMat (a b : ℂ) (p : Fin 4 → ℝ) (α β : Fin 4) :
    -(g5 α * g5 β) * seMat a b p α β = seMat a (-b) p α β := by
  have h : gamma5 * seMat a b p * gamma5 = seMat (-a) b p := by
    simp only [seMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, gamma5_conj_slash, gamma5_mul_gamma5]
    rw [smul_neg, neg_smul]
  have h' := congrFun (congrFun h α) β
  rw [gamma5_conj_apply] at h'
  rw [neg_mul, h']
  simp only [seMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The twisted one-loop self-energy has the covariant form. -/
theorem hasSEForm_selfEnergy_twist (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) :
    HasSEForm (Q.m + ν) fun ε p α β => -(g5 α * g5 β) *
      QED.OneLoop.energyFirstIntegral fun q => selfEnergyIntegrand Q ε p q α β := by
  obtain ⟨a, b, h⟩ := hasSEForm_selfEnergy Q hm hν0 hν
  refine ⟨a, fun s => -b s, fun p hp α β => ?_⟩
  rw [← neg_g5_mul_seMat]
  exact (h p hp α β).const_mul _

/-- A piece multiplied by a positive power of `ε` converges to `0`. -/
theorem hasSEForm_eps_piece {T : ℝ} (c : ℂ) (n : ℕ) (hn : 0 < n)
    {H : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hH : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
      ∃ L, Tendsto (fun ε => H ε p α β) (𝓝[>] 0) (𝓝 L)) :
    HasSEForm T fun ε p α β => (c * (ε : ℂ) ^ n) * H ε p α β := by
  refine ⟨0, 0, fun p hp α β => ?_⟩
  obtain ⟨L, hL⟩ := hH p hp α β
  have h := (tendsto_ofReal_mul_nhdsWithin c n).mul hL
  simp only [ofReal_zero, zero_pow hn.ne', mul_zero, zero_mul] at h
  simpa [seMat] using h

/-! ### The `n₀` piece -/

theorem propDenom_mulVec {L : Matrix (Fin 4) (Fin 4) ℝ} {S S' : Matrix (Fin 4) (Fin 4) ℂ}
    (h : IsSpinLift L S S') (M ε : ℝ) (u : Fin 4 → ℝ) :
    propDenom M ε (L *ᵥ u) = propDenom M ε u := by
  simp only [propDenom, h.dot_mulVec]

theorem cov_insR {L : Matrix (Fin 4) (Fin 4) ℝ} {S S' : Matrix (Fin 4) (Fin 4) ℂ}
    (h : IsSpinLift L S S') (m ε δ₂ δm : ℝ) (u : Fin 4 → ℝ) :
    S * insR m ε δ₂ δm (L *ᵥ u) * S' = insR m ε δ₂ δm u := by
  simp only [insR, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, h.mul_electronNumerator_mul, h.mul_eq_one]

theorem cov_numF0 (Q : Params) {L : Matrix (Fin 4) (Fin 4) ℝ} {S S' : Matrix (Fin 4) (Fin 4) ℂ}
    (h : IsSpinLift L S S') (p k : Fin 4 → ℝ) :
    S * numF0 Q (L *ᵥ p) (L *ᵥ k) * S' = numF0 Q p k := by
  rw [numF0, numF0, mulVec_add', mul_seChain_mul h _ (tensorCov_pvPhotonNum h Q.mγ Q.Λ),
    Matrix.mul_smul, Matrix.smul_mul, cov_insR h, propDenom_mulVec h]

theorem isLoopPoly_numF0_p (Q : Params) (k : Fin 4 → ℝ) (i j : Fin 4) :
    IsLoopPoly 1 3 fun y => numF0 Q (y 0) k i j := by
  have ha := isLoopAffine_add_const k
  have hR : IsLoopPolyMat 1 1 fun y => insR Q.m 0 Q.δ₂ Q.δm (y 0 + k) :=
    isLoopPolyMat_add (isLoopPolyMat_smul _ (ha.isLoopPolyMat_electronNumerator Q.m))
      (isLoopPolyMat_mono (isLoopPolyMat_smul _
        (IsLoopPolyMat.const (1 : Matrix (Fin 4) (Fin 4) ℂ))) (Nat.zero_le _))
  have hA : IsLoopPolyMat 1 3 fun y =>
      propDenom Q.m 0 (y 0 + k) • insR Q.m 0 Q.δ₂ Q.δm (y 0 + k) := fun a b => by
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact (ha.isLoopPoly_propDenom Q.m 0).mul (hR a b)
  have h := isLoopPolyMat_seChain (d := 0) hA
    (fun ν ρ => IsLoopPoly.const (L := 1) (n := 0) (pvPhotonNum Q.mγ Q.Λ ν ρ)) i j
  simpa [numF0] using h

theorem hasSEForm_F0 (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) :
    HasSEForm (Q.m + ν) fun ε p α β => QED.OneLoop.energyFirstIntegral fun q =>
      prefF Q ε p q * numF0 Q p q α β := by
  have hmγ : 0 < Q.mγ := hν0.trans_le (hν.trans (min_le_left _ _))
  have hΛ : 0 < Q.Λ := hν0.trans_le (hν.trans (min_le_right _ _))
  obtain ⟨hMe, hMp⟩ := massesSEF_bounds Q hmγ hΛ
  exact hasSEForm_kinds (by norm_num) kindsSEF (by decide) (massesSEF Q) hm hm hν0 hMe
    (fun i hi => (pow_le_pow_left₀ hν0.le hν 2).trans (hMp i hi)) (by decide) (by decide)
    (by decide) (numF0 Q) (fun p i j => (isLoopPoly_numF Q p i j).1)
    (fun L S S' h p k => cov_numF0 Q h p k) (isLoopPoly_numF0_p Q)
    (fun ε p q α β => prefF Q ε p q * numF0 Q p q α β)
    fun ε _ p ℓ i j => hfac_F Q p (fun q => numF0 Q p q i j) ε ℓ

/-! ### The class `F` -/

theorem classForm_repF : ClassForm repF := by
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
  have h1 := (((hasSEForm_selfEnergy Q hm hν0 hν).const_mul c₀).add
    ((hasSEForm_selfEnergy_twist Q hm hν0 hν).const_mul c₃)).add
    (((hasSEForm_F0 Q hm hν0 hν).const_mul (-κ)).add
      ((hasSEForm_eps_piece (-κ) 1 one_pos fun p hp α β =>
        (piece_F Q hm hmγ hΛ (hs p hp) (fun q => numF1 Q p q α β)
          (isLoopPoly_numF Q p α β).2.1).2).add
      (hasSEForm_eps_piece (-κ) 2 two_pos fun p hp α β =>
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
