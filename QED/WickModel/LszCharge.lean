/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.IsLSZChargeNormalized
public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.OneLoop.ChargeCondition
import QED.Algebra.Spinor
import QED.WickModel.LszClosedForm
import Mathlib.Tactic.LinearCombination

/-!
# The LSZ charge condition is the charge condition (K₀)

At `p' = p` the momentum transfer vanishes, so the photon-leg term of the closed form
(`QED.WickModel.LszClosedForm.lszAmplitude_eq_closedForm`) vanishes through its factor `q² = 0`,
and the LSZ amplitude is the sandwich `ū_{s'}(p) V^μ(p, p) u_s(p)` of the vertex function at
`Z₁ = 1 + δ₁`. That sandwich is `e (Z₁ + A₀) ū γ^μ u` for all Dirac solutions, and
`ū_0(p) γ⁰ u_0(p) = 2p⁰ ≠ 0`. So the LSZ charge condition (L₄), stated on the spinor bases, holds
if and only if `e (Z₁ + A₀) = e`, which is the charge condition (K₀) on all solutions.

## Main statements

* `QED.WickModel.LszCharge.lszAmplitude_self`: at `p' = p` the LSZ amplitude is
  `ū_{s'}(p) V^μ(p, p) u_s(p)`.
* `QED.WickModel.LszCharge.bar_spinor_gamma_spinor_self`: `ū_s(p) γ^μ u_s(p) = 2p^μ`.
* `QED.WickModel.LszCharge.isLSZChargeNormalized_iff`: (L₄) holds if and only if (K₀) holds at
  `Z₁ = 1 + δ₁`.

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Matrix Complex

namespace QED.WickModel

/-- **The LSZ amplitude at zero momentum transfer** is the sandwich of the vertex function at
`Z₁ = 1 + δ₁`: the photon-leg term carries the factor `q² = 0`. -/
theorem LszCharge.lszAmplitude_self (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) (p : Fin 4 → ℝ) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp0 : 0 < p 0) (s' s : Fin 2) (μ : Fin 4) :
    lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p p hp hp hp0 hp0 s' s μ =
      Dirac.bar (Dirac.spinor P.m p s') ⬝ᵥ
        (QED.OneLoop.vertexFunction P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ p p hp hp hp0 hp0 μ
          *ᵥ Dirac.spinor P.m p s) := by
  have hd : Minkowski.dot (p - p) (p - p) = 0 := by simp [Minkowski.dot]
  have h0 : (Minkowski.dot (p - p) (p - p) *
      ((Minkowski.dot (p - p) (p - p) + P.mγ ^ 2)⁻¹
        - (Minkowski.dot (p - p) (p - p) + P.Λ ^ 2)⁻¹) : ℝ) = 0 := by
    rw [hd, zero_mul]
  rw [LszClosedForm.lszAmplitude_eq_vertex_add_photonLeg, h0, ofReal_zero, mul_zero, zero_mul,
    zero_mul, add_zero]

/-- **The current of a spinor with itself**: `ū_s(p) γ^μ u_s(p) = 2p^μ` on shell with positive
energy, by the Gordon identity at `p' = p` and the normalization `ū_s(p) u_s(p) = 2m`. -/
theorem LszCharge.bar_spinor_gamma_spinor_self {m : ℝ} (hm : 0 < m) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -m ^ 2) (hp0 : 0 < p 0) (s : Fin 2) (μ : Fin 4) :
    Dirac.bar (Dirac.spinor m p s) ⬝ᵥ (Dirac.gamma μ *ᵥ Dirac.spinor m p s) = 2 * (p μ : ℂ) := by
  have hg := Dirac.gordon_spinor m p p hp hp s s μ
  have hn : Dirac.bar (Dirac.spinor m p s) ⬝ᵥ Dirac.spinor m p s = (2 * m : ℂ) := by
    simpa using Dirac.bar_spinor_dotProduct_spinor m hm p hp hp0 s s
  simp only [sub_self, ofReal_zero, zero_smul, Finset.sum_const_zero, smul_zero, sub_zero,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, hn] at hg
  have hm' : (2 * m : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 * m := by positivity
    exact_mod_cast this.ne'
  refine mul_left_cancel₀ hm' ?_
  rw [hg]
  push_cast
  ring

/-- **(L₄) is (K₀).** The LSZ charge condition, stated on the spinor bases, holds if and only if
the vertex function at `Z₁ = 1 + δ₁` satisfies the charge condition (K₀) on all Dirac
solutions. -/
theorem LszCharge.isLSZChargeNormalized_iff (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) :
    IsLSZChargeNormalized P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon ↔
      QED.OneLoop.IsChargeNormalized P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ := by
  constructor
  · intro h p hp hp0 μ u w hu hw
    -- On the spin-up spinor at `p` and `μ = 0`, (L₄) gives `e (Z₁ + A₀) · 2p⁰ = e · 2p⁰`.
    have h1 := h p hp hp0 0 0 0
    rw [LszCharge.lszAmplitude_self,
      QED.OneLoop.VertexLimit.sandwich_vertexFunction_self hm hmγ hΛ hp hp0 0
        (Dirac.slash_mulVec_spinor P.m p hp 0)
        (Dirac.bar_vecMul_slash P.m p _ (Dirac.slash_mulVec_spinor P.m p hp 0)),
      LszCharge.bar_spinor_gamma_spinor_self hm hp hp0 0 0] at h1
    have hne : 2 * (p 0 : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 2 * p 0 := by positivity
      exact_mod_cast this.ne'
    have hc := mul_right_cancel₀ hne h1
    rw [QED.OneLoop.VertexLimit.sandwich_vertexFunction_self hm hmγ hΛ hp hp0 μ hu hw, hc]
  · intro h p hp hp0 s' s μ
    rw [LszCharge.lszAmplitude_self]
    exact h p hp hp0 μ _ _ (Dirac.slash_mulVec_spinor P.m p hp s)
      (Dirac.bar_vecMul_slash P.m p _ (Dirac.slash_mulVec_spinor P.m p hp s'))

end QED.WickModel

end
