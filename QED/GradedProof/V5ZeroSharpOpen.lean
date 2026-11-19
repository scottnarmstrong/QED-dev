/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.V5ZeroSharpAlg

/-!
# `♯` of the limits of the open-line classes

Helper level for the reality of the order-`e⁵` vertex limit (V5Zero, part D). The numerator of
an open-line class is `(ie)⁵ (1/i)⁴` times a `♯`-fixed chain
(`QED.GradedProof.V5Zero.Sharp.sharp_chainNum`), and `(ie)⁵ (1/i)⁴ = i e⁵` is imaginary, so
`N♯ = -N` (`sharp_classNumM`). The limit is the parametric value of `twoLoopNorm • N` (real
normalization), hence `W♯ = -W` (`sharp_classLimitV`). Only `m, m_γ, Λ > 0` and the on-shell
data are used.
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.GradedProof.V5Zero.Sharp

open QED.Dirac QED.GradedProof.SE2Real QED.TwoLoop.LimitCovariance QED.TwoLoop.Bridge
open QED.TwoLoop.Enumeration QED.TwoLoop.ClassLimit QED.WickModel
open QED.TwoLoop.ReflCovariance (exists_quartic_classLimitV)

theorem conj_openCoeff (e : ℝ) :
    starRingEnd ℂ ((I * e) ^ 5 * (1 / I) ^ 4) = -((I * e) ^ 5 * (1 / I) ^ 4) := by
  have h : (I * e) ^ 5 * (1 / I) ^ 4 = I * (e : ℂ) ^ 5 := by
    have h4 : I ^ 4 = 1 := Complex.I_pow_four
    rw [mul_pow, one_div, inv_pow, h4, inv_one, mul_one, pow_succ I 4, h4, one_mul]
  rw [h, map_mul, map_pow, Complex.conj_I, Complex.conj_ofReal, neg_mul]

theorem sharp_classNumM_of_chain {c : Class5} (σ : Equiv.Perm (Fin 5))
    (line : Fin 4 → FermionLine c.rep)
    (heq : ∀ (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)
      (ℓ : Fin 2 → Fin 4 → ℝ),
      classNumeratorE c P pOut pIn kIn αOut βIn μ ℓ = (I * P.e) ^ 5 * (1 / I) ^ 4 *
        chainNum P σ (fun i => electronNumerator P.m
          (classMomE c (pIn 0) (pOut 0) ℓ (.inl (line i)))) (μ 0) (αOut 0) (βIn 0))
    (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    sharp (classNumM c P p p' μ ℓ) = (-1 : ℂ) • classNumM c P p p' μ ℓ := by
  have hM : classNumM c P p p' μ ℓ = ((I * P.e) ^ 5 * (1 / I) ^ 4) •
      chainNum P σ (fun i => electronNumerator P.m (classMomE c p p' ℓ (.inl (line i)))) μ := by
    ext i j
    simp only [classNumM, Matrix.of_apply, heq, Matrix.smul_apply, smul_eq_mul]
  rw [hM, sharp_smul, conj_openCoeff, sharp_chainNum P σ (fun i => sharp_electronNumerator _ _),
    smul_smul, neg_one_mul, neg_smul]

/-- **`N♯ = -N` for the open-class numerators.** -/
theorem sharp_classNumM {c : Class5} (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses)
    (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    sharp (classNumM c P p p' μ ℓ) = (-1 : ℂ) • classNumM c P p p' μ ℓ := by
  simp only [QED.TwoLoop.ClassIntegrable.openClasses, Finset.mem_insert,
    Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact sharp_classNumM_of_chain permL lineL chain_L P p p' μ ℓ
  · exact sharp_classNumM_of_chain permX lineX chain_X P p p' μ ℓ
  · exact sharp_classNumM_of_chain permCp lineCp chain_Cp P p p' μ ℓ
  · exact sharp_classNumM_of_chain permCm lineCm chain_Cm P p p' μ ℓ
  · exact sharp_classNumM_of_chain permSp lineSp chain_Sp P p p' μ ℓ
  · exact sharp_classNumM_of_chain permSm lineSm chain_Sm P p p' μ ℓ

theorem conj_twoLoopNorm : starRingEnd ℂ twoLoopNorm = twoLoopNorm := by
  simp only [twoLoopNorm, map_inv₀, Complex.conj_ofReal]

/-- **`W♯ = -W` for the limits of the open-line classes.** -/
theorem sharp_classLimitV {c : Class5} (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses)
    (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (μ : Fin 4) :
    sharp (classLimitV c P p p' μ) = -classLimitV c P p p' μ := by
  rw [← neg_one_smul ℂ (classLimitV c P p p' μ)]
  refine sharp_eq_smul_of_isParamValue_vertex (D := openData hc P hm hmγ hΛ hp hp' hq)
    (fun μ ℓ => twoLoopNorm • classNumM c P p p' μ ℓ) _ (-1) (fun μ ℓ => ?_)
    (fun μ i j => ?_) μ
  · rw [sharp_smul, conj_twoLoopNorm, sharp_classNumM hc, smul_comm]
  · obtain ⟨Q, hQ, -, hv⟩ := exists_quartic_classLimitV hc P hm hmγ hΛ hp hp' hq μ i j
    refine ⟨Q, hQ, ?_, hv⟩
    have hF : (fun ℓ => (twoLoopNorm • classNumM c P p p' μ ℓ) i j) =
        fun ℓ => twoLoopNorm * classNumeratorE c P (fun _ => p') (fun _ => p)
          (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) ℓ := by
      funext ℓ
      simp only [Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul]
    rw [hF]
    exact (QED.TwoLoop.ClassIntegrable.refinedBound_classNumeratorE hc P (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ)).const_mul _

end QED.GradedProof.V5Zero.Sharp

end
