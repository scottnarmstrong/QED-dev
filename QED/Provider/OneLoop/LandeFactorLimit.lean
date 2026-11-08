/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.IsResponseMagneticMoment
public import QED.Frozen.OneLoop.IsChargeNormalized
import QED.OneLoop.MagneticResponse

/-!
# Provider for `QED.OneLoop.landeFactor_isResponseMagneticMoment_limit`

Proves packet 4a's headline goal (R′) (decision D-16) as
`QED.Provider.OneLoop.landeFactor_isResponseMagneticMoment_limit`, with the binder convention of
decision D-13. Under the charge condition `Z₁ = 1 - A(0)`, the response magnetic moment is
`μ = e (1 + B(0)) / (2m)`, so `g = 4 m μ / e = 2 (1 + B(0))`, and `B(0) → e²/(8π²)` jointly in the
regulators. Until the frozen anchor is sealed, this module is quarantined; it must never import
the frozen anchor.
-/

@[expose] public section

open Matrix Complex
open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration
open scoped Real

namespace QED.Provider.OneLoop

/-- Packet 4a's (R′), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem landeFactor_isResponseMagneticMoment_limit {e m : ℝ} (he : e ≠ 0 := by assumption)
    (hm : 0 < m := by assumption) {η : ℝ} (hη : 0 < η := by assumption) :
    ∃ δ > 0, ∃ R : ℝ, ∀ (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ), mγ < δ → R < Λ →
      (∃ Z₁ μ : ℝ, IsChargeNormalized e Z₁ m mγ Λ hm hmγ hΛ ∧
        IsResponseMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ μ) ∧
      ∀ Z₁ μ : ℝ, IsChargeNormalized e Z₁ m mγ Λ hm hmγ hΛ →
        IsResponseMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ μ →
        |4 * m * μ / e - 2 * (1 + e ^ 2 / (8 * Real.pi ^ 2))| < η := by
  have he2 : 0 < e ^ 2 := by positivity
  have hc : 0 < 4 * π ^ 2 / e ^ 2 * η := by positivity
  obtain ⟨δ, hδ, R, hR⟩ := exists_abs_integral_pauliIntegrand_zero_sub_one_lt hm hc
  refine ⟨δ, hδ, R, fun mγ Λ hmγ hΛ hmγδ hRΛ =>
    ⟨⟨chargeZ e m mγ Λ, magneticMu e (chargeZ e m mγ Λ) m mγ Λ,
      isChargeNormalized_chargeZ hm hmγ hΛ, magneticMu_spec hm hmγ hΛ⟩, fun Z₁ μ hZ hμ => ?_⟩⟩
  have hZ1 := eq_chargeZ_of_isChargeNormalized he hm hmγ hΛ hZ
  subst hZ1
  have hμ' := eq_of_magnetic_spec hm hmγ hΛ hμ (magneticMu_spec hm hmγ hΛ)
  subst hμ'
  have hb := hR mγ Λ hmγ hmγδ hRΛ
  have key : 4 * m * magneticMu e (chargeZ e m mγ Λ) m mγ Λ / e - 2 * (1 + e ^ 2 / (8 * π ^ 2))
      = 2 * (e ^ 2 / (8 * π ^ 2)) * (∫ z, pauliIntegrand m (mγ, Λ, 0) z ∂feynmanMeasure - 1) := by
    simp only [magneticMu, chargeZ, pauliB0]
    field_simp
    ring
  rw [key, abs_mul, abs_of_pos (by positivity)]
  calc 2 * (e ^ 2 / (8 * π ^ 2)) * |∫ z, pauliIntegrand m (mγ, Λ, 0) z ∂feynmanMeasure - 1|
      < 2 * (e ^ 2 / (8 * π ^ 2)) * (4 * π ^ 2 / e ^ 2 * η) := by gcongr
    _ = η := by field_simp; ring

end QED.Provider.OneLoop

end
