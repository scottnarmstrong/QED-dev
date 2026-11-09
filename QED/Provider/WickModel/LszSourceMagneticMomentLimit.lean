/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.LszSourceMagneticMoment
public import QED.Frozen.WickModel.IsLSZResponseMagneticMoment
public import QED.Frozen.WickModel.LszAmplitudeExistsUnique
public import QED.Frozen.WickModel.VacuumPolarization
public import QED.Frozen.OneLoop.VertexFunction
public import QED.Frozen.OneLoop.IsResponseMagneticMoment
public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.Frozen.OneLoop.PacketNormSq
public import QED.OneLoop.OneParticle
public import QED.Algebra.OnShell
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Support
import QED.WickModel.LszPacketMoment
import QED.WickModel.LszResponse

/-!
# Provider for `QED.WickModel.integrable_and_tendsto_lszSourceMagneticMoment`

Proves packet 6c-2's theorem goal (L₇′) (decision D-31) as
`QED.Provider.WickModel.integrable_and_tendsto_lszSourceMagneticMoment`, with the binder
convention of decision D-13. This module must never import the frozen anchor.

Integrability is `QED.WickModel.LszPacket.integrable_mul_lszPacketCurrentDensity`. For the limit,
`QED.WickModel.LszPacket.lszSourceMagneticMoment_eq` shows that the LSZ source magnetic moment
equals packet 4b's (W₃) at `Z₁ = 1 + δ₁` for every packet width (the photon-leg term carries a
factor `q²`, whose gradient vanishes on the diagonal `k' = k`), and the LSZ response magnetic
moment is a response magnetic moment of packet 4a
(`QED.WickModel.LszResponse.isResponseMagneticMoment_of_isLSZ`), so the sealed (W₄) applies
(`QED.WickModel.LszPacket.tendsto_lszSourceMagneticMoment`).
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open scoped ContDiff

namespace QED.Provider.WickModel

open QED.WickModel in
/-- Packet 6c-2's (L₇′), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem integrable_and_tendsto_lszSourceMagneticMoment {P : Params}
    (hm : 0 < P.m := by assumption) (hmγ : 0 < P.mγ := by assumption)
    (hΛ : 0 < P.Λ := by assumption) (hM₁ : P.m < P.M₁ := by assumption)
    (hM₂ : P.m < P.M₂ := by assumption) (hPV₁ : 1 + P.c₁ + P.c₂ = 0 := by assumption)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0 := by assumption)
    (hon : IsElectronOnShell P hm hmγ hΛ := by assumption) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ := by assumption) (hφc : HasCompactSupport φ := by assumption)
    (hφ0 : ∃ t, 0 ≤ t ∧ φ t ≠ 0 := by assumption) :
    (∀ lam > 0, Integrable fun x : Fin 3 → ℝ =>
      (x 0 : ℂ) * lszPacketCurrentDensity P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon φ lam x) ∧
    ∀ μ : ℝ, IsLSZResponseMagneticMoment P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon μ →
      Tendsto (fun lam => lszSourceMagneticMoment P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon φ lam)
        (𝓝[>] 0) (𝓝 (μ : ℂ)) :=
  ⟨LszPacket.integrable_mul_lszPacketCurrentDensity P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon hφ hφc,
    fun μ hμ => LszPacket.tendsto_lszSourceMagneticMoment P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon hφ
      hφc hφ0 μ (LszResponse.isResponseMagneticMoment_of_isLSZ P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂
        hon μ hμ)⟩

end QED.Provider.WickModel

end
