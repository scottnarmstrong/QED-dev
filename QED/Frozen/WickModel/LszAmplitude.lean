/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

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

/-- (L₂) **The LSZ amplitude of the electron current** `M^μ_{s's}(p', p)` (decisions D-23, D-29):
for on-shell positive-energy momenta `p'`, `p`, spins `s'`, `s` and index `μ`, the unique number
that is the iterated limit of (L₁) of the sandwiched connected three-point function
`(1/i) ū_{s'}(p') G^μ_ε(r', r) u_s(p)`. It is chosen from the sealed existence-and-uniqueness
theorem (L₁); its characterization is (L₂′). -/
noncomputable def lszAmplitude (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ)
    (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (s' s : Fin 2)
    (μ : Fin 4) : ℂ :=
  ((lszAmplitude_existsUnique P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon).2 p' p hp' hp hp0' hp0 s' s
    μ).exists.choose

end QED.WickModel

end
