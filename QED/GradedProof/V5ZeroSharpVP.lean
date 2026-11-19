/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.V5ZeroSharpAlg
public import QED.GradedProof.V5ZeroLimCovVP

/-!
# `♯` of the limit of the vacuum-polarization class

Helper level for the reality of the order-`e⁵` vertex limit (V5Zero, part D). The piece
numerators of `VP` are `(ie)⁵ (1/i)⁶ = -i e⁵` times `♯`-fixed chains with real loop tensors,
with real coefficients (`vpCoeff0`, `vpCoeff2`, the latter built from line denominators at
`ε = 0`), so `N♯ = -N` (`sharp_vpPieceM`). The limit is a sum of five parametric values of these
numerators (`QED.GradedProof.V5Zero.Lim.exists_quartic_classLimitV_VP`, for
`0 < m₀ ≤ m, M₁, M₂`), hence `W♯ = -W` (`sharp_classLimitV_VP`).
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.GradedProof.V5Zero.Sharp

open QED.Dirac QED.GradedProof.SE2Real QED.TwoLoop.LimitCovariance QED.TwoLoop.Bridge
open QED.TwoLoop.Enumeration QED.TwoLoop.ClassLimit QED.WickModel
open QED.Integration.TwoLoop (lineDenom castLoopMatrix)

theorem conj_vpCoeff (e : ℝ) : starRingEnd ℂ ((I * e) ^ 5 * (1 / I) ^ 6) =
    -((I * e) ^ 5 * (1 / I) ^ 6) := by
  have h : (I * e) ^ 5 * (1 / I) ^ 6 = -I * (e : ℂ) ^ 5 := by
    have h4 : I ^ 4 = 1 := Complex.I_pow_four
    rw [mul_pow, one_div, inv_pow, show (6 : ℕ) = 4 + 2 from rfl, pow_add, h4, one_mul,
      pow_succ I 4, h4, one_mul, Complex.I_sq, inv_neg, inv_one]
    ring
  rw [h, map_mul, map_neg, map_pow, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem sharp_vpE0M (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    sharp (vpE0M P p p' μ ℓ) = -vpE0M P p p' μ ℓ := by
  rw [vpE0M_eq, sharp_smul, conj_vpCoeff, sharp_vpChainM _ _ _ _
    (conj_traceT (sharp_electronNumerator _ _) (sharp_electronNumerator _ _)), neg_smul]

theorem sharp_vpE2M (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    sharp (vpE2M P p p' μ ℓ) = -vpE2M P p p' μ ℓ := by
  rw [vpE2M_eq, sharp_smul, conj_vpCoeff, sharp_vpChainM _ _ _ _
    (conj_traceT sharp_one sharp_one), neg_smul]

theorem conj_vpBubbleCoeff (P : Params) : starRingEnd ℂ (vpBubbleCoeff P) = vpBubbleCoeff P := by
  simp only [vpBubbleCoeff, Complex.conj_ofReal]

theorem conj_lineDenom_zero {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (q : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    starRingEnd ℂ (lineDenom α q M 0 i ℓ) = lineDenom α q M 0 i ℓ := by
  simp only [lineDenom, map_sub, Complex.conj_ofReal, Complex.ofReal_zero, zero_mul, map_zero]

theorem conj_vpCoeff0 (P : Params) (j : Fin 5) :
    starRingEnd ℂ (vpCoeff0 P j) = vpCoeff0 P j := by
  have hn : starRingEnd ℂ twoLoopNorm = twoLoopNorm := by
    simp only [twoLoopNorm, map_inv₀, Complex.conj_ofReal]
  unfold vpCoeff0
  split_ifs
  · simp
  · rw [map_mul, hn, conj_vpBubbleCoeff]

theorem conj_vpCoeff2 (P : Params) (p p' : Fin 4 → ℝ) (j : Fin 5) (ℓ : Fin 2 → Fin 4 → ℝ) :
    starRingEnd ℂ (vpCoeff2 P p p' j ℓ) = vpCoeff2 P p p' j ℓ := by
  have hn : starRingEnd ℂ twoLoopNorm = twoLoopNorm := by
    simp only [twoLoopNorm, map_inv₀, Complex.conj_ofReal]
  unfold vpCoeff2
  split_ifs <;>
    simp only [map_neg, map_mul, hn, conj_vpBubbleCoeff, conj_lineDenom_zero, Complex.conj_ofReal]

/-- **`N♯ = -N` for the piece numerators of `VP`.** -/
theorem sharp_vpPieceM (P : Params) (p p' : Fin 4 → ℝ) (j : Fin 5) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    sharp (vpPieceM P p p' j μ ℓ) = (-1 : ℂ) • vpPieceM P p p' j μ ℓ := by
  rw [vpPieceM_eq, sharp_add, sharp_smul, sharp_smul, conj_vpCoeff0, conj_vpCoeff2, sharp_vpE0M,
    sharp_vpE2M, neg_one_smul, neg_add, smul_neg, smul_neg]

/-- **`W♯ = -W` for a sum of parametric values of the `VP` piece numerators.** -/
theorem sharp_classLimitV_VP_of (P : Params) {p p' : Fin 4 → ℝ} (D : Fin 5 → ParamData)
    (W : Fin 5 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hW : ∀ k μ i j, IsParamValue (D k) (fun ℓ => vpPieceM P p p' k μ ℓ i j) (W k μ i j))
    (hlim : classLimitV .VP P p p' = fun μ => ∑ k ∈ Finset.univ, (1 : ℂ) • W k μ) (μ : Fin 4) :
    sharp (classLimitV .VP P p p' μ) = -classLimitV .VP P p p' μ := by
  rw [hlim]
  simp only [sharp_sum, one_smul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sharp_eq_smul_of_isParamValue_vertex (D := D k) (fun μ ℓ => vpPieceM P p p' k μ ℓ)
    (W k) (-1) (fun μ ℓ => sharp_vpPieceM P p p' k μ ℓ) (hW k) μ, neg_one_smul]

/-- **`W♯ = -W` for the limit of `VP`**, for `0 < m₀ ≤ m, M₁, M₂` with the Pauli–Villars
conditions. -/
theorem sharp_classLimitV_VP (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀) (hm : m₀ ≤ P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : m₀ ≤ P.M₁) (hM₂ : m₀ ≤ P.M₂)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (μ : Fin 4) :
    sharp (classLimitV .VP P p p' μ) = -classLimitV .VP P p p' μ := by
  obtain ⟨Q, hQ, -, hW⟩ :=
    QED.GradedProof.V5Zero.Lim.exists_quartic_classLimitV_VP P hm₀ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp
      hp' hq
  refine sharp_classLimitV_VP_of P
    (fun k => QED.GradedProof.V5Zero.Lim.vpData P hm₀ hm hmγ hΛ hM₁ hM₂ hp hp' hq k) _
    (fun k μ i j => ⟨Q μ i j k, hQ μ i j k, ?_, rfl⟩) hW μ
  have hF : (fun ℓ => vpPieceM P p p' k μ ℓ i j) = vpPieceNumer P (fun _ => p') (fun _ => p)
      (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) k := by
    funext ℓ
    simp only [vpPieceM, Matrix.of_apply]
  rw [hF]
  exact refinedBound_vpPieceNumer P _ _ _ _ _ _ k

end QED.GradedProof.V5Zero.Sharp

end
