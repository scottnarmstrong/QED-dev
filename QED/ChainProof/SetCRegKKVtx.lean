/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegKKSplit
public import QED.TwoLoop.PauliZeroLimitCt

/-!
# Set (c): the vertex factor of `Q(5, 1, 0)` is the one-loop vertex

Helper level for `QED.ChainProof.SetCRegDisp.IsKKSumGe` (`QED/ChainProof/SetCRegKKGe.lean`).

* **`kkVtx_eq`**: for `ε > 0`, the vertex factor `kkVtx` of
  `QED/ChainProof/SetCRegKKSplit.lean` is `(2π)⁴/(Λ² - m_γ²)` times the frozen one-loop vertex
  integrand `QED.OneLoop.vertexIntegrand` at charge `1` (the Pauli–Villars difference
  `1/D_{m_γ} - 1/D_Λ = (Λ² - m_γ²)/(D_{m_γ} D_Λ)`);
* **`tendsto_kkVtx`**: its energy-first integral tends to `(2π)⁴/(Λ² - m_γ²) · i V`, `V` the
  frozen one-loop vertex `QED.OneLoop.vertexOneLoop` at charge `1`.
-/

@[expose] public section

open Complex Filter Topology Set
open QED.WickModel (Params)
open QED.Dirac (gamma)

namespace QED.ChainProof.SetCRegDisp

open QED.TwoLoop.Bridge (electronNumerator)

variable (R : Params) (p p' : Fin 4 → ℝ) (μ a b : Fin 4)

/-- The constant `(2π)⁴/(Λ² - m_γ²)` relating `kkVtx` to the frozen vertex integrand. -/
noncomputable def kkVtxC (R : Params) : ℂ :=
  ((((2 * Real.pi) ^ 4 / (R.Λ ^ 2 - R.mγ ^ 2) : ℝ)) : ℂ)

theorem kkDn_fold (M ε : ℝ) (k : Fin 4 → ℝ) :
    ((Minkowski.dot k k + M ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I = kkDn M ε k := rfl

theorem kkDn_ne_zero {M ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) : kkDn M ε k ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [kkDn, Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, mul_zero, mul_one, add_zero, zero_sub, Complex.zero_im,
    neg_eq_zero] at this
  exact hε.ne' this

/-- **The vertex factor is the frozen one-loop vertex integrand** at charge `1`, up to
`(2π)⁴/(Λ² - m_γ²)`. -/
theorem kkVtx_eq (hΛ : R.mγ ^ 2 ≠ R.Λ ^ 2) {ε : ℝ} (hε : 0 < ε) (ℓ : Fin 4 → ℝ) :
    kkVtx R p p' ε μ a b ℓ =
      kkVtxC R * QED.OneLoop.vertexIntegrand 1 R.m R.mγ R.Λ ε p' p μ ℓ a b := by
  have h1 := kkDn_ne_zero (M := R.mγ) hε ℓ
  have h2 := kkDn_ne_zero (M := R.Λ) hε ℓ
  have h3 := kkDn_ne_zero (M := R.m) hε (ℓ + p')
  have h4 := kkDn_ne_zero (M := R.m) hε (ℓ + p)
  have hπ : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.pi).ne'
  have hd : ((R.Λ ^ 2 - R.mγ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.2 (Ne.symm hΛ)
  have hD : (kkDn R.mγ ε ℓ)⁻¹ - (kkDn R.Λ ε ℓ)⁻¹ =
      ((R.Λ ^ 2 - R.mγ ^ 2 : ℝ) : ℂ) * ((kkDn R.mγ ε ℓ)⁻¹ * (kkDn R.Λ ε ℓ)⁻¹) := by
    field_simp
    simp only [kkDn]
    push_cast
    ring
  simp only [kkVtx, kkVtxN, kkVtxC, QED.OneLoop.vertexIntegrand, QED.OneLoop.photonPropagator,
    QED.OneLoop.electronPropagator, electronNumerator, Fin.sum_univ_four, Minkowski.metric,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, kkDn_fold, add_comm p' ℓ, add_comm p ℓ]
  simp (config := { decide := true }) only [ite_true, ite_false, Complex.ofReal_zero,
    Complex.ofReal_one, Complex.ofReal_neg, zero_mul, zero_smul, add_zero, zero_add,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hD]
  have hI : (I * 1) ^ 3 * (1 / I) ^ 3 = 1 := by
    rw [mul_one, ← mul_pow, mul_one_div_cancel I_ne_zero, one_pow]
  rw [hI]
  push_cast at hπ hd ⊢
  field_simp

/-- The energy-first integral commutes with a constant factor (no integrability needed). -/
theorem energyFirstIntegral_const_mul (c : ℂ) (F : (Fin 4 → ℝ) → ℂ) :
    QED.OneLoop.energyFirstIntegral (fun ℓ => c * F ℓ) = c * QED.OneLoop.energyFirstIntegral F := by
  simp only [QED.OneLoop.energyFirstIntegral, MeasureTheory.integral_const_mul]

/-- **The limit of the vertex factor**: `(2π)⁴/(Λ² - m_γ²) · i V^μ_{ab}`, `V` the frozen
one-loop vertex at charge `1`. -/
theorem tendsto_kkVtx (hm : 0 < R.m) (hmγ : 0 < R.mγ) (hΛ : R.mγ < R.Λ)
    (hp : Minkowski.dot p p = -R.m ^ 2) (hp' : Minkowski.dot p' p' = -R.m ^ 2)
    (hp0 : 0 < p 0) (hp0' : 0 < p' 0) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral (kkVtx R p p' ε μ a b)) (𝓝[>] 0)
      (𝓝 (kkVtxC R * (I * QED.OneLoop.vertexOneLoop 1 R.m R.mγ R.Λ hm hmγ (hmγ.trans hΛ) p' p
        hp' hp hp0' hp0 μ a b))) := by
  have hΛ2 : R.mγ ^ 2 ≠ R.Λ ^ 2 := by nlinarith
  have h := (QED.OneLoop.vertexLimit_existsUnique 1 R.m R.mγ R.Λ hm hmγ (hmγ.trans hΛ) p' p hp'
    hp hp0' hp0 μ a b).2.exists.choose_spec
  have hV : I * QED.OneLoop.vertexOneLoop 1 R.m R.mγ R.Λ hm hmγ (hmγ.trans hΛ) p' p hp' hp hp0'
      hp0 μ a b = (QED.OneLoop.vertexLimit_existsUnique 1 R.m R.mγ R.Λ hm hmγ (hmγ.trans hΛ) p' p
        hp' hp hp0' hp0 μ a b).2.exists.choose := by
    rw [QED.OneLoop.vertexOneLoop, Matrix.of_apply, ← mul_assoc, mul_one_div_cancel I_ne_zero,
      one_mul]
  rw [hV]
  refine (h.const_mul (kkVtxC R)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [← energyFirstIntegral_const_mul]
  congr 1
  funext ℓ
  exact (kkVtx_eq R p p' μ a b hΛ2 hε ℓ).symm

/-- **The value of `Q(5, 1, 0)`** from the limit `L` of the scalar factor: the vertex limit
times `L`. -/
theorem kkQ_five_eq (hm : 0 < R.m) (hmγ : 0 < R.mγ) (hΛ : R.mγ < R.Λ)
    (hp : Minkowski.dot p p = -R.m ^ 2) (hp' : Minkowski.dot p' p' = -R.m ^ 2)
    (hp0 : 0 < p 0) (hp0' : 0 < p' 0) {t : ℝ} {L : ℂ}
    (hL : Tendsto (fun ε => QED.OneLoop.energyFirstIntegral (kkScl R.mγ R.Λ t ε)) (𝓝[>] 0)
      (𝓝 L)) :
    kkQ 5 R p p' t 1 0 μ a b (1 / 2) = kkVtxC R * (I * QED.OneLoop.vertexOneLoop 1 R.m R.mγ R.Λ
      hm hmγ (hmγ.trans hΛ) p' p hp' hp hp0' hp0 μ a b) * L := by
  refine Tendsto.limUnder_eq (((tendsto_kkVtx R p p' μ a b hm hmγ hΛ hp hp' hp0 hp0').mul
    hL).congr fun ε => ?_)
  exact (jointEnergyFirstIntegral_kkT_five R p p' t ε μ a b).symm

end QED.ChainProof.SetCRegDisp

end
