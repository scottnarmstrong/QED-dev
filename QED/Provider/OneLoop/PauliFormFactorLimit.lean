/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.VertexOneLoop
public import QED.Frozen.OneLoop.IsFormFactorPair
public import Mathlib.Analysis.Complex.Basic
import QED.OneLoop.FormFactorPair

/-!
# Provider for `QED.OneLoop.isFormFactorPair_vertexOneLoop_pauli_limit`

Proves packet 2's headline goal (I) (decision D-14) as
`QED.Provider.OneLoop.isFormFactorPair_vertexOneLoop_pauli_limit`, with the binder convention of
decision D-13. The unique form-factor pair is `(A, B)` with
`B = (e²/8π²) ∫ dF₃ (x₃ - x₃²) m² (1/D_{m_γ} - 1/D_Λ)`, and the normalized integral tends to `1`
jointly in the regulators and `q²` (`QED.OneLoop.VertexLimit.tendsto_integral_pauliIntegrand`).
Until the frozen anchor is sealed, this module is quarantined; it must never import the frozen
anchor.
-/

@[expose] public section

open Matrix Complex
open QED.OneLoop QED.OneLoop.VertexLimit
open scoped Real

namespace QED.Provider.OneLoop

/-- Packet 2's (I), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem isFormFactorPair_vertexOneLoop_pauli_limit {e m : ℝ} (he : e ≠ 0 := by assumption)
    (hm : 0 < m := by assumption) {η : ℝ} (hη : 0 < η := by assumption) :
    ∃ δ > 0, ∃ R : ℝ, ∀ (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ) (p' p : Fin 4 → ℝ)
      (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
      (hp0' : 0 < p' 0) (hp0 : 0 < p 0),
      0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < δ →
      mγ < δ → R < Λ →
      (∃ F : ℂ × ℂ,
        IsFormFactorPair e m p' p (vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0) F) ∧
      ∀ F : ℂ × ℂ,
        IsFormFactorPair e m p' p (vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0) F →
        ‖F.2 - ((e ^ 2 / (8 * Real.pi ^ 2) : ℝ) : ℂ)‖ < η := by
  have he2 : 0 < e ^ 2 := by positivity
  have hc : 0 < 8 * π ^ 2 / e ^ 2 * η := by positivity
  obtain ⟨δ, hδ, R, hR⟩ := exists_abs_integral_pauliIntegrand_sub_one_lt hm hc
  refine ⟨δ, hδ, R, fun mγ Λ hmγ hΛ p' p hp' hp hp0' hp0 hq0 hqδ hmγδ hRΛ =>
    ⟨⟨_, isFormFactorPair_vertexOneLoop hm hmγ hΛ hp' hp hp0' hp0⟩, fun F hF => ?_⟩⟩
  rw [eq_of_isFormFactorPair_vertexOneLoop he hm hmγ hΛ hp' hp hp0' hp0 hq0 hF]
  have hb := hR mγ Λ (Minkowski.dot (p' - p) (p' - p)) hmγ hmγδ hRΛ hq0 hqδ
  simp only
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, formFactorB_eq hp' hp]
  calc |e ^ 2 / (8 * π ^ 2) * ∫ z, pauliIntegrand m (mγ, Λ, Minkowski.dot (p' - p) (p' - p)) z
          ∂QED.Integration.feynmanMeasure - e ^ 2 / (8 * π ^ 2)|
        = e ^ 2 / (8 * π ^ 2) * |∫ z, pauliIntegrand m (mγ, Λ, Minkowski.dot (p' - p) (p' - p)) z
          ∂QED.Integration.feynmanMeasure - 1| := by
          rw [← mul_sub_one, abs_mul, abs_of_pos (by positivity)]
      _ < e ^ 2 / (8 * π ^ 2) * (8 * π ^ 2 / e ^ 2 * η) := by gcongr
      _ = η := by field_simp

end QED.Provider.OneLoop

end
