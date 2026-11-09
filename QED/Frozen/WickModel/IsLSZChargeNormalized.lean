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

/-- (L₄) **The charge condition, LSZ form** ((63.1)–(63.2); decision D-29): at `p' = p`, the LSZ
amplitude (L₂) is `e ū_{s'}(p) γ^μ u_s(p)` for every on-shell positive-energy `p`, all spins
`s'`, `s` and every `μ`. This is (K₀) with the LSZ amplitude as the current matrix element, stated
on the spinor bases `u_s(p)`, `ū_{s'}(p)` rather than on all solutions; (L₄′) shows the two
agree. -/
def IsLSZChargeNormalized (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) : Prop :=
  ∀ (p : Fin 4 → ℝ) (hp : Minkowski.dot p p = -P.m ^ 2) (hp0 : 0 < p 0) (s' s : Fin 2)
    (μ : Fin 4), lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p p hp hp hp0 hp0 s' s μ
      = (P.e : ℂ) * (Dirac.bar (Dirac.spinor P.m p s') ⬝ᵥ (Dirac.gamma μ *ᵥ Dirac.spinor P.m p s))

end QED.WickModel

end
