/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2RealParam
public import QED.TwoLoop.LimitCovarianceQuartic

/-!
# The antilinear map `♯` and parametric values

Helper level for the reality of the order-`e⁵` vertex limit (V5Zero, part D). The map
`X♯ = -(C X̄ C)` of `QED.GradedProof.SE2Real.sharp` moves single entries: `C` is a signed
anti-diagonal permutation matrix, so `X♯ i j = sᵢⱼ conj (X (rev i) (rev j))` with `sᵢⱼ = ±1`
(`sharp_apply`). Parametric values (`QED.TwoLoop.LimitCovariance.IsParamValue`) commute with
complex conjugation (`isParamValue_conj`, from `QED.GradedProof.SE2Real.paramIntegrand_qconj`).
Hence, if the numerators satisfy `N(ℓ)♯ = λ N(ℓ)` for real `ℓ`, the parametric values satisfy
`W♯ = λ W` (`sharp_eq_smul_of_isParamValue`).
-/

@[expose] public section

open Complex Matrix MeasureTheory
open scoped Real

namespace QED.GradedProof.V5Zero.Sharp

open QED.GradedProof.SE2Real QED.TwoLoop.LimitCovariance
open QED.Integration.Feynman (simplexSet)

/-- The sign of the single entry of row `i` of `C`, paired with column `j`. -/
def sgn (i j : Fin 4) : ℂ := -(cMat i i.rev * cMat j.rev j)

theorem conj_sgn (i j : Fin 4) : starRingEnd ℂ (sgn i j) = sgn i j := by
  fin_cases i <;> fin_cases j <;> simp [sgn, cMat]

/-- **`X♯` entrywise**: `X♯ i j = sᵢⱼ conj (X (rev i) (rev j))`. -/
theorem sharp_apply (X : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    sharp X i j = sgn i j * starRingEnd ℂ (X i.rev j.rev) := by
  simp only [sharp, sgn, Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> simp [cMat]

theorem refinedBound_conj {m : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ} {E : Finset (Fin (m + 1))}
    {k : ℕ} {F : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (h : QED.Integration.TwoLoop.RefinedBound α E k F) :
    QED.Integration.TwoLoop.RefinedBound α E k fun ℓ => starRingEnd ℂ (F ℓ) := by
  obtain ⟨C, hC, hF⟩ := h
  exact ⟨C, hC, fun A hA ℓ => by rw [Complex.norm_conj]; exact hF A hA ℓ⟩

variable {D : ParamData}

/-- **Parametric values commute with complex conjugation.** -/
theorem isParamValue_conj {F : (Fin 2 → Fin 4 → ℝ) → ℂ} {v : ℂ} (h : IsParamValue D F v) :
    IsParamValue D (fun ℓ => starRingEnd ℂ (F ℓ)) (starRingEnd ℂ v) := by
  obtain ⟨Q, rfl, hB, rfl⟩ := h
  refine ⟨qconj Q, funext fun ℓ => eval_qconj Q ℓ, refinedBound_conj hB, ?_⟩
  simp only [paramIntegrand_qconj, integral_conj, map_mul, map_neg, map_pow, Complex.conj_ofReal]

theorem isParamValue_const_mul (c : ℂ) {F : (Fin 2 → Fin 4 → ℝ) → ℂ} {v : ℂ}
    (h : IsParamValue D F v) : IsParamValue D (fun ℓ => c * F ℓ) (c * v) := by
  have := IsParamValue.sum (Finset.univ : Finset Unit) (fun _ => c) (F := fun _ => F)
    (v := fun _ => v) fun _ _ => h
  simpa using this

theorem isParamValue_congr {F G : (Fin 2 → Fin 4 → ℝ) → ℂ} {v : ℂ} (h : IsParamValue D F v)
    (hFG : ∀ ℓ, F ℓ = G ℓ) : IsParamValue D G v := by
  rwa [← funext hFG]

/-- **The parametric value matrix inherits the `♯`-law of the numerator.** -/
theorem sharp_eq_smul_of_isParamValue (N : (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (W : Matrix (Fin 4) (Fin 4) ℂ) (c : ℂ) (hN : ∀ ℓ, sharp (N ℓ) = c • N ℓ)
    (hW : ∀ i j, IsParamValue D (fun ℓ => N ℓ i j) (W i j)) : sharp W = c • W := by
  ext i j
  have h1 := isParamValue_const_mul (sgn i j) (isParamValue_conj (hW i.rev j.rev))
  have h2 := isParamValue_const_mul c (hW i j)
  have h1' : IsParamValue D (fun ℓ => c * N ℓ i j) (sgn i j * starRingEnd ℂ (W i.rev j.rev)) :=
    isParamValue_congr h1 fun ℓ => by
      have := congrFun (congrFun (hN ℓ) i) j
      rw [sharp_apply, Matrix.smul_apply, smul_eq_mul] at this
      exact this
  rw [sharp_apply, Matrix.smul_apply, smul_eq_mul]
  exact IsParamValue.unique h1' h2

/-- The same for a vertex `W^μ` of parametric values. -/
theorem sharp_eq_smul_of_isParamValue_vertex
    (N : Fin 4 → (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (c : ℂ) (hN : ∀ μ ℓ, sharp (N μ ℓ) = c • N μ ℓ)
    (hW : ∀ μ i j, IsParamValue D (fun ℓ => N μ ℓ i j) (W μ i j)) (μ : Fin 4) :
    sharp (W μ) = c • W μ :=
  sharp_eq_smul_of_isParamValue (N μ) (W μ) c (hN μ) (hW μ)

end QED.GradedProof.V5Zero.Sharp

end
