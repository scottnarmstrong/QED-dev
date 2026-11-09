/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.LszAmplitudeSpec
public import QED.WickModel.LszLimit

/-!
# The LSZ amplitude in closed form

The sealed LSZ amplitude `lszAmplitude` (L₂) is the only number with the iterated-limit property
of its characterization (L₂′), and `LszLimit.closedForm` has that property
(`QED.WickModel.lszLimit_closedForm`). So the two are equal: the LSZ amplitude is
`ū_{s'}(p') V^μ(p', p) u_s(p)`, with `V^μ` the vertex function (J) at `Z₁ = 1 + δ₁`, plus the
photon-leg term `e q² [1/(q² + m_γ²) - 1/(q² + Λ²)] Π(q²) ū_{s'}(p') γ^μ u_s(p)`, `q = p' - p`.

## Main statements

* `QED.WickModel.LszClosedForm.lszAmplitude_eq_closedForm`: `lszAmplitude = LszLimit.closedForm`.
* `QED.WickModel.LszClosedForm.lszAmplitude_eq_vertex_add_photonLeg`: the same, written out.

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Matrix Complex

namespace QED.WickModel

/-- **The LSZ amplitude is the closed form.** By the uniqueness half of the characterization
(L₂′), applied to the limit property `QED.WickModel.lszLimit_closedForm` of
`LszLimit.closedForm`. -/
theorem LszClosedForm.lszAmplitude_eq_closedForm (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) (p' p : Fin 4 → ℝ)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (s' s : Fin 2) (μ : Fin 4) :
    lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 s' s μ =
      LszLimit.closedForm P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ p' p hp' hp hp0' hp0 s' s μ :=
  ((lszAmplitude_spec P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 s' s μ).2 _
    (lszLimit_closedForm P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 s' s μ)).symm

/-- **The LSZ amplitude, written out.** `lszAmplitude` is `ū_{s'}(p') V^μ(p', p) u_s(p)`, with
`V^μ` the vertex function (J) at `Z₁ = 1 + δ₁`, plus
`e q² [1/(q² + m_γ²) - 1/(q² + Λ²)] Π(q²) ū_{s'}(p') γ^μ u_s(p)`, `q = p' - p`. -/
theorem LszClosedForm.lszAmplitude_eq_vertex_add_photonLeg (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) (p' p : Fin 4 → ℝ)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (s' s : Fin 2) (μ : Fin 4) :
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
  LszClosedForm.lszAmplitude_eq_closedForm P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0
    s' s μ

end QED.WickModel

end
