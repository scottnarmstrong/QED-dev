/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.LszAmplitude
public import QED.Frozen.WickModel.IsLSZChargeNormalized
public import QED.Frozen.WickModel.IsLSZResponseMagneticMoment
public import QED.Frozen.WickModel.LszSourceMagneticMoment
public import QED.Frozen.Algebra.LorentzGen
public import QED.Frozen.Algebra.Lower
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Support

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open scoped ContDiff

namespace QED.WickModel

/-- (H₀) **The on-shell form-factor decomposition (63.18) of the LSZ amplitude** (decisions D-29,
D-32): the pair `F = (A, B)` decomposes the LSZ amplitude (L₂) at the on-shell positive-energy
momenta `(p', p)` if `M^μ_{s's}(p', p) = e ū_{s'}(p') [A γ^μ - (i/m) B S^{μν} q_ν] u_s(p)` for all
spins `s'`, `s` and every `μ`, with `q = p' - p` and `S^{μν} = (i/4)[γ^μ, γ^ν]`. This is (G₀) with
the LSZ amplitude as the current matrix element, stated on the spinor bases `u_s(p)`,
`ū_{s'}(p')` rather than on all solutions; the two forms agree, since these spinors span the
solution spaces ((38.1), (38.16), (38.23)). The photon-leg term of (L₃) is a multiple of
`ū_{s'}(p') γ^μ u_s(p)`, so it shifts only `A`. For `e ≠ 0` and `q² > 0` there is exactly one
such pair (H₀′), and `B` is the Pauli form factor of the model's own amplitude at `(p', p)`. -/
def IsLSZFormFactorPair (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ)
    (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (F : ℂ × ℂ) : Prop :=
  ∀ (s' s : Fin 2) (μ : Fin 4),
    lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 s' s μ =
      (P.e : ℂ) * (Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ
        ((F.1 • Dirac.gamma μ - (I / (P.m : ℂ) * F.2) •
          ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • Dirac.lorentzGen μ ν) *ᵥ
            Dirac.spinor P.m p s))

end QED.WickModel

end
