/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2ParamPiece
public import QED.TwoLoop.JointIntegralInvariance

/-!
# Parametric values under a change of routing

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A6. The Ward–Takahashi derivative (`SEData.hasDerivAt_pv_ray_ward`) is applied in a routing
where the external momentum flows only through the open electron line; the self-energy classes
are given in their frozen routings. Two parametric values agree when the joint integrands at every
`ε > 0` are related by an integer unimodular affine change of loop momenta `ℓ ↦ R ℓ + a`
(`SEData.pv_eq_of_comp`): the joint integrals agree
(`QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add`, which allows any
real shift `a`, in particular multiples of the external momentum), and the parametric values are
their limits (`SEData.tendsto_pv`).
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.SE2.SEData

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit

/-- **Equal joint integrals give equal parametric values.** -/
theorem pv_eq_of_joint_eq {D₁ D₂ : SEData} {Q₁ Q₂ : LoopQuartic} (h₁ : D₁.Good Q₁)
    (h₂ : D₂.Good Q₂) {q₁ : Fin (D₁.m + 1) → Fin 4 → ℝ} {q₂ : Fin (D₂.m + 1) → Fin 4 → ℝ}
    (hV₁ : D₁.VPos q₁) (hV₂ : D₂.VPos q₂)
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      QED.TwoLoop.jointEnergyFirstIntegral 2
          (fun ℓ => Q₁.eval ℓ * ∏ i, (lineDenom D₁.α q₁ D₁.M ε i ℓ)⁻¹) =
        QED.TwoLoop.jointEnergyFirstIntegral 2
          (fun ℓ => Q₂.eval ℓ * ∏ i, (lineDenom D₂.α q₂ D₂.M ε i ℓ)⁻¹)) :
    D₁.pv Q₁ q₁ = D₂.pv Q₂ q₂ :=
  tendsto_nhds_unique ((tendsto_pv h₁ hV₁).congr' h) (tendsto_pv h₂ hV₂)

/-- **Parametric values under an integer unimodular affine change of loop momenta.** -/
theorem pv_eq_of_comp {D₁ D₂ : SEData} {Q₁ Q₂ : LoopQuartic} (h₁ : D₁.Good Q₁)
    (h₂ : D₂.Good Q₂) {q₁ : Fin (D₁.m + 1) → Fin 4 → ℝ} {q₂ : Fin (D₂.m + 1) → Fin 4 → ℝ}
    (hV₁ : D₁.VPos q₁) (hV₂ : D₂.VPos q₂) (R : Matrix (Fin 2) (Fin 2) ℤ) (hR : IsUnit R.det)
    (a : Fin 2 → Fin 4 → ℝ)
    (h : ∀ ε, 0 < ε → ∀ ℓ, Q₁.eval ℓ * ∏ i, (lineDenom D₁.α q₁ D₁.M ε i ℓ)⁻¹ =
      Q₂.eval ((fun s => ∑ r, R s r • ℓ r) + a) *
        ∏ i, (lineDenom D₂.α q₂ D₂.M ε i ((fun s => ∑ r, R s r • ℓ r) + a))⁻¹) :
    D₁.pv Q₁ q₁ = D₂.pv Q₂ q₂ := by
  refine pv_eq_of_joint_eq h₁ h₂ hV₁ hV₂ ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [← QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2
    (fun ℓ => Q₂.eval ℓ * ∏ i, (lineDenom D₂.α q₂ D₂.M ε i ℓ)⁻¹) R hR a]
  exact congrArg _ (funext (h ε hε))

end QED.GradedProof.SE2.SEData

end
