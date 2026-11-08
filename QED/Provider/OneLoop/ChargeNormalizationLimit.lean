/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.Frozen.OneLoop.IsFormFactorPair
public import Mathlib.Analysis.Complex.Basic
import QED.OneLoop.ChargeCondition

/-!
# Provider for `QED.OneLoop.isFormFactorPair_vertexFunction_dirac_limit`

Proves packet 3's theorem goal (M) (decision D-15) as
`QED.Provider.OneLoop.isFormFactorPair_vertexFunction_dirac_limit`, with the binder convention of
decision D-13. Until the frozen anchor is sealed, this module is quarantined; it must never import
the frozen anchor.
-/

@[expose] public section

open Matrix Complex
open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration
open scoped Real

namespace QED.Provider.OneLoop

/-- Packet 3's (M), with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem isFormFactorPair_vertexFunction_dirac_limit {e Z₁ m mγ Λ : ℝ} (he : e ≠ 0 := by assumption)
    (hm : 0 < m := by assumption) (hmγ : 0 < mγ := by assumption) (hΛ : 0 < Λ := by assumption)
    (hZ : IsChargeNormalized e Z₁ m mγ Λ hm hmγ hΛ := by assumption) {η : ℝ}
    (hη : 0 < η := by assumption) :
    ∃ δ > 0, ∀ (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -m ^ 2)
      (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0),
      0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < δ →
      (∃ F : ℂ × ℂ, IsFormFactorPair e m p' p
        (vertexFunction e Z₁ m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0) F) ∧
      ∀ F : ℂ × ℂ, IsFormFactorPair e m p' p
          (vertexFunction e Z₁ m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0) F →
        ‖F.1 - 1‖ < η := by
  have hZ1 := eq_chargeZ_of_isChargeNormalized he hm hmγ hΛ hZ
  have he2 : 0 < e ^ 2 := by positivity
  have hc : 0 < 16 * π ^ 2 / e ^ 2 * η := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := exists_abs_integral_formIntegrandAq_sub_lt hm hmγ hΛ hc
  refine ⟨δ, hδ, fun p' p hp' hp hp0' hp0 hq0 hqδ => ⟨⟨_,
    (isFormFactorPair_vertexOneLoop_iff_vertexFunction_aux (Z₁ := Z₁) hm hmγ hΛ hp' hp hp0'
      hp0 _).mp
      (isFormFactorPair_vertexOneLoop hm hmγ hΛ hp' hp hp0' hp0)⟩, fun F hF => ?_⟩⟩
  have hF' : IsFormFactorPair e m p' p (vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0)
      (F.1 - Z₁, F.2) :=
    (isFormFactorPair_vertexOneLoop_iff_vertexFunction_aux (Z₁ := Z₁) hm hmγ hΛ hp' hp hp0'
      hp0 _).mpr
      (by simpa using hF)
  have hEq := eq_of_isFormFactorPair_vertexOneLoop he hm hmγ hΛ hp' hp hp0' hp0 hq0 hF'
  have h1 : F.1 = (Z₁ : ℂ) + (formFactorA e m mγ Λ p' p : ℂ) := by
    have := congrArg Prod.fst hEq; simp only at this; rw [← this]; ring
  rw [h1, hZ1, formFactorA_eq_q hp' hp]
  have hb := hδ' _ hq0 hqδ
  have : ((chargeZ e m mγ Λ : ℝ) : ℂ) + ((e ^ 2 / (16 * π ^ 2) * ∫ z, formIntegrandAq m mγ Λ
      (Minkowski.dot (p' - p) (p' - p)) z ∂feynmanMeasure : ℝ) : ℂ) - 1
      = ((e ^ 2 / (16 * π ^ 2) * (∫ z, formIntegrandAq m mγ Λ
        (Minkowski.dot (p' - p) (p' - p)) z ∂feynmanMeasure
          - ∫ z, formIntegrandAq m mγ Λ 0 z ∂feynmanMeasure) : ℝ) : ℂ) := by
    simp only [chargeZ, chargeA0]; push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
  calc e ^ 2 / (16 * π ^ 2) * |∫ z, formIntegrandAq m mγ Λ (Minkowski.dot (p' - p) (p' - p)) z
          ∂feynmanMeasure - ∫ z, formIntegrandAq m mγ Λ 0 z ∂feynmanMeasure|
      < e ^ 2 / (16 * π ^ 2) * (16 * π ^ 2 / e ^ 2 * η) := by gcongr
    _ = η := by field_simp

end QED.Provider.OneLoop

end
