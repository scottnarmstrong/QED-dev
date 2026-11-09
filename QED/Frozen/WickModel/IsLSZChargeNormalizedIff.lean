-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.IsLSZChargeNormalized
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
public import QED.Provider.WickModel.IsLSZChargeNormalizedIff

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open scoped ContDiff

namespace QED.WickModel

/-- (L₄′) **The LSZ charge condition is packet 3's (packet 6c theorem goal).** (L₄) holds if
and only if the vertex counterterm `Z₁ = 1 + δ₁` satisfies the charge condition (K₀). -/
theorem isLSZChargeNormalized_iff_isChargeNormalized (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) :
    IsLSZChargeNormalized P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon ↔
      QED.OneLoop.IsChargeNormalized P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.WickModel.isLSZChargeNormalized_iff_isChargeNormalized
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.WickModel

end
-- FROZEN_ANCHOR_SUFFIX_END
