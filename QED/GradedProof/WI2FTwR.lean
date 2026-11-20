/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2F
public import QED.GradedProof.WI2VtxF
public import QED.WickModel.ThreePointClassification
public import QED.OneLoop.VertexOffShellIntegrable

/-!
# The counterterm-vertex term of the Ward derivative of `F`

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57). The
Ward derivative of the class `F` (`hasDerivAt_dF_wt`) carries, besides the doubled-line terms,
the term `pvF[twR (δ₂ r̸)]` from differentiating the counterterm vertex `δ₂ k̸ + δ_m m`. On shell
it is `-δ₂` times the contracted one-loop vertex limit (`e_mul_twR_dF`):

`e κ auxLimit⁻¹ pvF[twR (δ₂ r̸)] = -δ₂ ∑_μ r_μ V₁^μ`, `V₁ = lim_ε vertexValue = ∫ spatialG`.

Pointwise at `ε ≠ 0` the integrand over the data `dF` is `-δ₂ r_μ` times the one-loop vertex
integrand at `q = 0` times the auxiliary loop (`integrand_twR_dF`); the joint integral factorizes
(`jointEnergyFirstIntegral_two_mul`), and the factors converge.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 QED.Integration.TwoLoop QED.WickModel QED.TwoLoop.Bridge
open QED.TwoLoop.CountertermLimit QED.TwoLoop.Insertion QED.TwoLoop.ClassIntegrable

theorem twR_dF (Q : Params) (p : Fin 4 → ℝ) (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    (dF Q).twR eF Q.m aSlotF bSlotF (cSlotF Q) p Y ℓ =
      seChain (-(electronNumerator Q.m (p + ℓ 0) * Y * electronNumerator Q.m (p + ℓ 0)))
        (pvPhotonNum Q.mγ Q.Λ) := by
  have h0 := lineMomentum_dF Q p 0 ℓ
  have h1 := lineMomentum_dF Q p 1 ℓ
  simp only [kindsF, LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  simp only [SEData.twR, SEData.tw, SEData.twE, seChain, Fintype.sum_prod_type, aSlotF, bSlotF,
    cSlotF, eF, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h0, h1]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => ?_
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_smul, smul_neg, Matrix.mul_assoc]

/-- The contracted vertex chain at `q = 0` is a self-energy chain with `r̸` inserted. -/
theorem sum_lower_vertexChain (e : ℝ) (r : Fin 4 → ℝ) (S : Matrix (Fin 4) (Fin 4) ℂ)
    (D : Fin 4 → Fin 4 → ℂ) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) • vertexChain e μ S S D =
      ((I * e) ^ 3 * (1 / I) ^ 3 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹) •
        seChain (S * Dirac.slash r * S) D := by
  simp only [vertexChain, seChain, Dirac.slash, Matrix.mul_sum, Matrix.sum_mul, Matrix.smul_mul,
    Matrix.mul_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  · ring
  · simp only [Matrix.mul_assoc]

/-- **The integrand of `twR (δ₂ r̸)` over `dF` at `ε ≠ 0`** is `-δ₂` times the contracted
one-loop vertex integrand at `q = 0` times the auxiliary loop. -/
theorem integrand_twR_dF (Q : Params) {ε : ℝ} (hε : ε ≠ 0) (p r : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (α β : Fin 4) :
    Q.e * kappaSE Q.e * ((dF Q).twR eF Q.m aSlotF bSlotF (cSlotF Q) p
        ((Q.δ₂ : ℂ) • Dirac.slash r) ℓ α β *
        ∏ i, (lineDenom (dF Q).α ((dF Q).mom p) (dF Q).M ε i ℓ)⁻¹) =
      (-(Q.δ₂ : ℂ) * ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) *
        vertexEntry { Q with ε := ε } p p μ α β (ℓ 0)) * ((propDenom Q.m ε (ℓ 1))⁻¹) ^ 3 := by
  have hv : ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * vertexEntry { Q with ε := ε } p p μ α β (ℓ 0) =
      (∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) • vertexChain Q.e μ
        (QED.OneLoop.electronPropagator Q.m ε (p + ℓ 0))
        (QED.OneLoop.electronPropagator Q.m ε (p + ℓ 0))
        (QED.OneLoop.photonPropagator Q.mγ Q.Λ ε (ℓ 0))) α β := by
    simp only [vertexEntry, vertexIntegrand_eq_vertexChain, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul]
  rw [hv, sum_lower_vertexChain, twR_dF, prod_lineDenom_dF, photonPropagator_eq_scalar _ _ hε,
    seChain_smul_photon, QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← neg_smul, seChain_smul_in,
    Matrix.smul_apply, smul_eq_mul, Fin.prod_univ_succ, Fin.prod_univ_zero, kindsF, massesF,
    LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ, kappaSE]
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp

/-- **The counterterm-vertex term of the Ward derivative of `F`**, on shell: `e κ / auxLimit`
times `pvF[twR (δ₂ r̸)]` is `-δ₂` times the contracted one-loop vertex limit at `q = 0`. -/
theorem e_mul_twR_dF (Q : Params) (hm : 0 < Q.m) (hmγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -Q.m ^ 2) (hp0 : 0 < p 0) (r : Fin 4 → ℝ)
    (α β : Fin 4) :
    Q.e * kappaSE Q.e * (auxLimit Q.m)⁻¹ * (dF Q).pvF (fun ℓ => (dF Q).twR eF Q.m aSlotF bSlotF
        (cSlotF Q) p ((Q.δ₂ : ℂ) • Dirac.slash r) ℓ α β) ((dF Q).mom p) =
      -(Q.δ₂ : ℂ) * ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) *
        ∫ v, QED.OneLoop.VertexLimit.spatialG Q.e Q.m Q.mγ Q.Λ 0 p p μ α β v := by
  set Y : Matrix (Fin 4) (Fin 4) ℂ := (Q.δ₂ : ℂ) • Dirac.slash r
  obtain ⟨QR, hRq, hRe⟩ := IsLoopPoly.exists_loopQuartic_cubic
    ((dF Q).isLoopPoly_twR eF Q.m aSlotF bSlotF (cSlotF Q) p Y α β)
  have hRg : (dF Q).Good QR := ⟨Or.inr hRq, by
    rw [hRe]; exact (dF Q).refinedBound_twR eF Q.m aSlotF bSlotF (cSlotF Q) eF_ne eF_mem p Y α β⟩
  have hV := vpos_dF_onShell Q hm hmγ hΛ hp
  rw [SEData.pvF_eq hRg hRe hV]
  have hH := tendsto_energyFirstIntegral_aux hm
  have hH0 := auxLimit_ne_zero hm
  have hW : ∀ μ, Tendsto (fun ε => vertexValue { Q with ε := ε } p p μ α β) (𝓝[>] 0)
      (𝓝 (∫ v, QED.OneLoop.VertexLimit.spatialG Q.e Q.m Q.mγ Q.Λ 0 p p μ α β v)) := fun μ =>
    tendsto_vertexValue Q hm hmγ hΛ (pOut := fun _ => p) (pIn := fun _ => p) hp hp hp0 hp0
      (fun _ => α) (fun _ => β) (fun _ => μ)
  have hS := tendsto_finsetSum Finset.univ fun μ _ =>
    (hW μ).const_mul ((Minkowski.lower r μ : ℝ) : ℂ)
  have hL := ((hS.const_mul (-(Q.δ₂ : ℂ))).mul hH).mul_const (auxLimit Q.m)⁻¹
  rw [mul_assoc, mul_inv_cancel₀ hH0, mul_one] at hL
  rw [mul_right_comm ((Q.e : ℂ) * kappaSE Q.e)]
  refine tendsto_nhds_unique (((SEData.tendsto_pv hRg hV).const_mul
    (Q.e * kappaSE Q.e)).mul_const (auxLimit Q.m)⁻¹) (hL.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  congr 1
  rw [← QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul]
  have e : (fun ℓ => (Q.e : ℂ) * kappaSE Q.e * (QR.eval ℓ *
      ∏ i, (lineDenom (dF Q).α ((dF Q).mom p) (dF Q).M ε i ℓ)⁻¹)) = fun ℓ =>
      (fun q => -(Q.δ₂ : ℂ) * ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) *
        vertexEntry { Q with ε := ε } p p μ α β q) (ℓ 0) *
      (fun k => ((propDenom Q.m ε k)⁻¹) ^ 3) (ℓ 1) := funext fun ℓ => by
    rw [hRe]
    exact integrand_twR_dF Q hε.ne' p r ℓ α β
  rw [e, jointEnergyFirstIntegral_two_mul (fun q => -(Q.δ₂ : ℂ) * ∑ μ,
      ((Minkowski.lower r μ : ℝ) : ℂ) * vertexEntry { Q with ε := ε } p p μ α β q)
    (fun k => ((propDenom Q.m ε k)⁻¹) ^ 3)]
  congr 1
  rw [QED.OneLoop.energyFirstIntegral_const_mul, QED.WickModel.energyFirstIntegral_sum_mul_left]
  · rfl
  · intro μ
    exact QED.OneLoop.VertexOffShell.integrable_energyFirst_of_pos hε _ _ _ _ _ _ _ _ _

end QED.GradedProof.WI2

end
