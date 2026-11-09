/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.LszPacketCurrentDensity
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

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open scoped ContDiff

namespace QED.WickModel

/-- (L₇) **The magnetic moment, source definition, LSZ form** (64.4)–(64.7) (rulings D-9,
D-29): (W₃) with the current density (L₆), `μ = ∫ d³x x¹ ⟨e|J²(x)|e⟩ / ⟨e|e⟩`. The position
integral is the undamped one; theorem (L₇′) asserts that it converges absolutely. -/
noncomputable def lszSourceMagneticMoment (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ)
    (φ : ℝ → ℝ) (lam : ℝ) : ℂ :=
  (∫ x : Fin 3 → ℝ, (x 0 : ℂ) * lszPacketCurrentDensity P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon φ lam x)
    / (QED.OneLoop.packetNormSq P.m φ lam : ℂ)

end QED.WickModel

end
