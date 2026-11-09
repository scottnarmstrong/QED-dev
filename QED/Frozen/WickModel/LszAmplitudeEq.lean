-- FROZEN_ANCHOR_PREFIX_BEGIN
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
public import QED.Provider.WickModel.LszAmplitudeEq

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open scoped ContDiff

namespace QED.WickModel

/-- (L₃) **The LSZ amplitude is the vertex plus the photon-leg term (packet 6c theorem goal;
obligation O-3; decisions D-21, D-23, D-29).** With the electron on shell (Z₅) the corrections
on the electron legs drop out (unit residues, (62.27), (62.36)–(62.38)), and
`M^μ_{s's}(p', p) = ū_{s'}(p') V^μ(p', p) u_s(p) + e q² D(q²) Π(q²) ū_{s'}(p') γ^μ u_s(p)`.
Here `V` is the vertex function (J) at `Z₁ = 1 + δ₁`, `q = p' - p` (so `q² ≥ 0`),
`D(q²) = 1/(q² + m_γ²) - 1/(q² + Λ²)` is the scalar part of the photon propagator (B) at `ε = 0`,
and `Π` is the vacuum polarization function (Z₇). The second term is the photon leg
`e γ^ν Δ̃_{νρ}(q) Π^{ρμ}(q)` between on-shell spinors, where the `q̸ q^μ` part of `Π^{ρμ}`
drops out. As `m_γ → 0` and `Λ → ∞` at fixed `q² > 0` the factor `q² D(q²)` tends to `1`. No
photon on-shell condition (Z₈) is assumed: the formula holds for every `δ₃`. -/
theorem lszAmplitude_eq (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ)
    (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (s' s : Fin 2)
    (μ : Fin 4) :
    lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 s' s μ =
      Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ
          (QED.OneLoop.vertexFunction P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ p' p hp' hp hp0'
            hp0 μ *ᵥ Dirac.spinor P.m p s)
        + (P.e : ℂ) * ((Minkowski.dot (p' - p) (p' - p) *
            ((Minkowski.dot (p' - p) (p' - p) + P.mγ ^ 2)⁻¹
              - (Minkowski.dot (p' - p) (p' - p) + P.Λ ^ 2)⁻¹) : ℝ) : ℂ)
          * vacuumPolarization P hm hM₁ hM₂ hPV₁ hPV₂ ⟨Minkowski.dot (p' - p) (p' - p),
              lt_of_lt_of_le (neg_lt_zero.mpr (mul_pos four_pos (pow_pos hm 2)))
                (Minkowski.dot_sub_self_nonneg_of_onShell hp' hp hp0' hp0)⟩
          * (Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ (Dirac.gamma μ *ᵥ Dirac.spinor P.m p s)) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.WickModel.lszAmplitude_eq
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.WickModel

end
-- FROZEN_ANCHOR_SUFFIX_END
