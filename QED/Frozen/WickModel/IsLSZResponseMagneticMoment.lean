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

/-- (L₅) **The magnetic moment, response definition, LSZ form** (rulings D-9, D-29): (R₀) with
the LSZ amplitude `M²_{++}(p', p)` (L₂), spins up along `z`, as the static-field matrix element
in place of `ū₊(p') V²(p', p) u₊(p)`: for Breit-frame on-shell momenta
`p = (E, -q/2, 0, 0)`, `p' = (E, q/2, 0, 0)`, it equals `2 i m μ q + o(q)` as `q → 0⁺`. -/
def IsLSZResponseMagneticMoment (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) (μ : ℝ) : Prop :=
  ∀ η > 0, ∃ δ > 0, ∀ (q : ℝ) (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0),
    0 < q → q < δ → p' 1 = q / 2 → p 1 = -(q / 2) → p' 2 = 0 → p 2 = 0 → p' 3 = 0 →
    p 3 = 0 →
    ‖lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 0 0 2
      - 2 * I * P.m * μ * q‖ ≤ η * q

end QED.WickModel

end
