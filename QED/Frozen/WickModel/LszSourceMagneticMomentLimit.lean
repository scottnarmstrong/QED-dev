-- FROZEN_ANCHOR_PREFIX_BEGIN
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
public import QED.Provider.WickModel.LszSourceMagneticMomentLimit

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open scoped ContDiff

namespace QED.WickModel

/-- (L₇′) **The two LSZ magnetic moments agree (packet 6c theorem goal; as (W₄)).** For a real
smooth compactly supported profile `φ` that is not identically zero on `[0, ∞)` (ruling D-17):
for every packet width `λ > 0` the position integral of (L₇) converges absolutely, and as
`λ → 0⁺` the LSZ source magnetic moment tends to the LSZ response magnetic moment (L₅). -/
theorem integrable_and_tendsto_lszSourceMagneticMoment (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∃ t, 0 ≤ t ∧ φ t ≠ 0) :
    (∀ lam > 0, Integrable fun x : Fin 3 → ℝ =>
      (x 0 : ℂ) * lszPacketCurrentDensity P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon φ lam x) ∧
    ∀ μ : ℝ, IsLSZResponseMagneticMoment P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon μ →
      Tendsto (fun lam => lszSourceMagneticMoment P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon φ lam) (𝓝[>] 0)
        (𝓝 (μ : ℂ)) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.WickModel.integrable_and_tendsto_lszSourceMagneticMoment
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.WickModel

end
-- FROZEN_ANCHOR_SUFFIX_END
