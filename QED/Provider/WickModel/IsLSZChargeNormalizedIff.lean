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
import QED.WickModel.LszCharge

/-!
# Provider for `QED.WickModel.isLSZChargeNormalized_iff_isChargeNormalized`

Proves packet 6c-2's theorem goal (L₄′) (decision D-31) as
`QED.Provider.WickModel.isLSZChargeNormalized_iff_isChargeNormalized`, with the binder convention of
decision D-13. At `p' = p` the photon-leg term of the closed form vanishes, so the LSZ amplitude is
the sandwich of the vertex function at `Z₁ = 1 + δ₁`, which is `e (Z₁ + A₀) ū γ^μ u` on all Dirac
solutions; since `ū_0(p) γ⁰ u_0(p) = 2p⁰ ≠ 0`, both conditions say `e (Z₁ + A₀) = e`
(`QED.WickModel.LszCharge.isLSZChargeNormalized_iff`). This module must never import the frozen
anchor.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open scoped ContDiff

namespace QED.Provider.WickModel

open QED.WickModel in
/-- Packet 6c-2's (L₄′), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem isLSZChargeNormalized_iff_isChargeNormalized {P : Params}
    (hm : 0 < P.m := by assumption) (hmγ : 0 < P.mγ := by assumption)
    (hΛ : 0 < P.Λ := by assumption) (hM₁ : P.m < P.M₁ := by assumption)
    (hM₂ : P.m < P.M₂ := by assumption) (hPV₁ : 1 + P.c₁ + P.c₂ = 0 := by assumption)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0 := by assumption)
    (hon : IsElectronOnShell P hm hmγ hΛ := by assumption) :
    IsLSZChargeNormalized P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon ↔
      QED.OneLoop.IsChargeNormalized P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ :=
  LszCharge.isLSZChargeNormalized_iff P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon

end QED.Provider.WickModel

end
