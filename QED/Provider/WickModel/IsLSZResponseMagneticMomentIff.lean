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
import QED.WickModel.LszResponse

/-!
# Provider for `QED.WickModel.isLSZResponseMagneticMoment_iff_isResponseMagneticMoment`

Proves packet 6c-2's theorem goal (L₅′) (decision D-31) as
`QED.Provider.WickModel.isLSZResponseMagneticMoment_iff_isResponseMagneticMoment`, with the binder
convention of decision D-13. In the Breit frame the LSZ amplitude and the vertex sandwich at
`Z₁ = 1 + δ₁` differ by the photon-leg term `i e q³ D(q²) Π(q²)`, which is at most `C q³` for
`0 < q ≤ 1`, so the two little-o conditions are equivalent
(`QED.WickModel.LszResponse.isLSZResponseMagneticMoment_iff`). This module must never import the
frozen anchor.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open scoped ContDiff

namespace QED.Provider.WickModel

open QED.WickModel in
/-- Packet 6c-2's (L₅′), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem isLSZResponseMagneticMoment_iff_isResponseMagneticMoment {P : Params}
    (hm : 0 < P.m := by assumption) (hmγ : 0 < P.mγ := by assumption)
    (hΛ : 0 < P.Λ := by assumption) (hM₁ : P.m < P.M₁ := by assumption)
    (hM₂ : P.m < P.M₂ := by assumption) (hPV₁ : 1 + P.c₁ + P.c₂ = 0 := by assumption)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0 := by assumption)
    (hon : IsElectronOnShell P hm hmγ hΛ := by assumption) {μ : ℝ} :
    IsLSZResponseMagneticMoment P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon μ ↔
      QED.OneLoop.IsResponseMagneticMoment P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ μ :=
  LszResponse.isLSZResponseMagneticMoment_iff P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon μ

end QED.Provider.WickModel

end
