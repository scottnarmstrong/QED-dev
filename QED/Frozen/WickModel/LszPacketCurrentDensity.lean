/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.LszAmplitude
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

/-- (L₆) The current density `⟨e|J²(x)|e⟩` at time `0` of the wave packet of (W₁), LSZ form:
(W₁) with the one-electron matrix elements `⟨k'|J²(0)|k⟩` given by the LSZ amplitude
`M²_{++}(k', k)` (L₂) instead of the sandwich of the amputated vertex (decision D-29). -/
noncomputable def lszPacketCurrentDensity (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ)
    (φ : ℝ → ℝ) (lam : ℝ) (x : Fin 3 → ℝ) : ℂ :=
  ∫ k : Fin 3 → ℝ, ∫ k' : Fin 3 → ℝ,
    ((φ ((∑ j, k' j ^ 2) / lam ^ 2) * φ ((∑ j, k j ^ 2) / lam ^ 2)
      / ((2 * Real.pi) ^ 3 * (2 * QED.OneLoop.oneParticleMomentum P.m k 0)
        * ((2 * Real.pi) ^ 3 * (2 * QED.OneLoop.oneParticleMomentum P.m k' 0))) : ℝ) : ℂ)
    * Complex.exp (I * ((∑ j, (k j - k' j) * x j : ℝ) : ℂ))
    * lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon (QED.OneLoop.oneParticleMomentum P.m k')
        (QED.OneLoop.oneParticleMomentum P.m k) (QED.OneLoop.dot_oneParticleMomentum P.m k')
        (QED.OneLoop.dot_oneParticleMomentum P.m k) (QED.OneLoop.oneParticleMomentum_pos hm k')
        (QED.OneLoop.oneParticleMomentum_pos hm k) 0 0 2

end QED.WickModel

end
