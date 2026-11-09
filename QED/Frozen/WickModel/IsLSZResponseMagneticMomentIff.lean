-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

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
public import QED.Provider.WickModel.IsLSZResponseMagneticMomentIff

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open scoped ContDiff

namespace QED.WickModel

/-- (L₅′) **The LSZ response magnetic moment is packet 4a's (packet 6c theorem goal).** A real
`μ` satisfies (L₅) if and only if it satisfies (R₀) for the vertex function with
`Z₁ = 1 + δ₁`: in the Breit frame the photon-leg term of (L₃) is `i e q³ D(q²) Π(q²) = O(q³)`,
since `q_B² = q²` and `ū₊(p') γ² u₊(p) = i q`; this uses `m_γ > 0` and holds for every `δ₃`. -/
theorem isLSZResponseMagneticMoment_iff_isResponseMagneticMoment (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) (μ : ℝ) :
    IsLSZResponseMagneticMoment P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon μ ↔
      QED.OneLoop.IsResponseMagneticMoment P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ μ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.WickModel

end
-- FROZEN_ANCHOR_SUFFIX_END
