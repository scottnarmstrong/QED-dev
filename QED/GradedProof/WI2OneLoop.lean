/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2LimC
public import QED.GradedProof.SE2ParamCont
public import QED.OneLoop.FormFactorPair
public import QED.OneLoop.ChargeCondition
public import QED.TwoLoop.WardIdentityParametric

/-!
# The one-loop Ward identity between on-shell spinors

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57). The
`δ₁` classes of the self-energy (`C1`, `C2`: `δ₁` times the one-loop self-energy limit
`seOneLoopLimit`) and of the vertex (`δ₁` times the one-loop vertex limit `vOne`) pair through
the one-loop Ward identity, which we need only between on-shell spinors (`(p̸ + m) u = 0`,
`w (p̸ + m) = 0`):

* `hasDerivAt_sandwich_seOneLoopLimit`: `d/dt|₁ w Σ₁(t p) u = -i m δ₂^{os} (w u)`, from the on-shell
  form `w Σ₁(t p) u = i Σ(-t m) (w u)`;
* `sum_lower_sandwich_vOne`: `∑_μ p_μ w V₁^μ u = -i e m A₀ (w u)`;
* `hasDerivAt_sandwich_seOneLoopLimit_eq`: with `A₀ = -δ₂^{os}` (`chargeA0_eq_neg_onShellδ₂`),
  `d/dt|₁ w Σ₁(t p) u = -(1/e) ∑_μ p_μ w V₁^μ u`.
-/

@[expose] public section

open Complex Matrix Filter Topology

namespace QED.GradedProof.WI2

open QED.WickModel (Params selfEnergyLoopA selfEnergyLoopB onShellδ₂ onShellδm)

/-- The one-loop vertex limit at `(p, p)`, `V₁^μ_{ij} = lim_ε vertexValue = ∫ spatialG`. -/
noncomputable def vOne (Q : Params) (p : Fin 4 → ℝ) (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => ∫ v, QED.OneLoop.VertexLimit.spatialG Q.e Q.m Q.mγ Q.Λ 0 p p μ i j v

/-- A contracted sandwich of `γ^μ` is the sandwich of the slash. -/
theorem sum_lower_sandwich_gamma (r : Fin 4 → ℝ) (u w : Fin 4 → ℂ) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)) =
      w ⬝ᵥ (Dirac.slash r *ᵥ u) := by
  simp only [Dirac.slash, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul,
    smul_eq_mul]

theorem sandwich_vOne (Q : Params) (hm : 0 < Q.m) (hmγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -Q.m ^ 2) (hp0 : 0 < p 0) (μ : Fin 4)
    {u w : Fin 4 → ℂ} (hu : Dirac.slash p *ᵥ u = -((Q.m : ℂ) • u))
    (hw : w ᵥ* Dirac.slash p = -((Q.m : ℂ) • w)) :
    w ⬝ᵥ (vOne Q p μ *ᵥ u) =
      I * Q.e * QED.OneLoop.VertexLimit.chargeA0 Q.e Q.m Q.mγ Q.Λ *
        (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)) := by
  have h := QED.OneLoop.VertexLimit.sandwich_vertexOneLoop_self (e := Q.e) hm hmγ hΛ hp hp0 μ hu hw
  rw [QED.OneLoop.VertexLimit.vertexOneLoop_eq_limit hm hmγ hΛ hp hp hp0 hp0] at h
  have e : vOne Q p μ = I • Matrix.of (fun i j => (1 / I) *
      ∫ v, QED.OneLoop.VertexLimit.spatialG Q.e Q.m Q.mγ Q.Λ 0 p p μ i j v) := by
    ext i j
    simp only [vOne, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
  rw [e, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, h, QED.OneLoop.VertexLimit.chargeA0]
  push_cast
  ring

/-- **The contracted one-loop vertex between on-shell spinors.** -/
theorem sum_lower_sandwich_vOne (Q : Params) (hm : 0 < Q.m) (hmγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -Q.m ^ 2) (hp0 : 0 < p 0)
    {u w : Fin 4 → ℂ} (hu : Dirac.slash p *ᵥ u = -((Q.m : ℂ) • u))
    (hw : w ᵥ* Dirac.slash p = -((Q.m : ℂ) • w)) :
    ∑ μ, ((Minkowski.lower p μ : ℝ) : ℂ) * (w ⬝ᵥ (vOne Q p μ *ᵥ u)) =
      -(I * Q.e * QED.OneLoop.VertexLimit.chargeA0 Q.e Q.m Q.mγ Q.Λ * Q.m) * (w ⬝ᵥ u) := by
  simp only [sandwich_vOne Q hm hmγ hΛ hp hp0 _ hu hw, mul_left_comm _ (I * _ * _ : ℂ),
    ← Finset.mul_sum, sum_lower_sandwich_gamma, hu, dotProduct_neg, dotProduct_smul,
    smul_eq_mul]
  ring

/-- The on-shell function `Σ(z) = A(-z²) z + B(-z²) m` of the one-loop self-energy has derivative
`δ₂^{os}` at `z = -m`. -/
theorem hasDerivAt_shell_one (Q : Params) (hm : 0 < Q.m) (hmγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ) :
    HasDerivAt (fun z : ℝ => selfEnergyLoopA Q (-z ^ 2) * z + selfEnergyLoopB Q (-z ^ 2) * Q.m)
      (onShellδ₂ Q : ℂ) (-Q.m) := by
  have h := ((QED.WickModel.selfEnergyLoop_onShell_iff Q hm hmγ hΛ (onShellδ₂ Q)
    (onShellδm Q)).2 ⟨rfl, rfl⟩).2
  have hl : HasDerivAt (fun z : ℝ => (onShellδ₂ Q : ℂ) * z + (onShellδm Q : ℂ) * Q.m)
      (onShellδ₂ Q : ℂ) (-Q.m) := by
    simpa using ((hasDerivAt_id (-Q.m)).ofReal_comp.const_mul (onShellδ₂ Q : ℂ)).add_const
      ((onShellδm Q : ℂ) * Q.m)
  have h2 := h.add hl
  rw [zero_add] at h2
  exact h2.congr_of_eventuallyEq (Eventually.of_forall fun z => by
    simp only [Pi.add_apply]
    ring)

/-- **The one-loop self-energy between on-shell spinors along the ray**: its derivative at
`t = 1` is `-i m δ₂^{os} (w u)`. -/
theorem hasDerivAt_sandwich_seOneLoopLimit (Q : Params) (hm : 0 < Q.m) (hmγ : 0 < Q.mγ)
    (hΛ : 0 < Q.Λ) {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -Q.m ^ 2) {u w : Fin 4 → ℂ}
    (hu : Dirac.slash p *ᵥ u = -((Q.m : ℂ) • u)) :
    HasDerivAt (fun t : ℝ => w ⬝ᵥ (QED.GradedProof.SE2.seOneLoopLimit Q (t • p) *ᵥ u))
      (I * (-(Q.m : ℂ)) * (onShellδ₂ Q : ℂ) * (w ⬝ᵥ u)) 1 := by
  set S : ℝ → ℂ := fun z => selfEnergyLoopA Q (-z ^ 2) * z + selfEnergyLoopB Q (-z ^ 2) * Q.m
  have hf : (fun t : ℝ => w ⬝ᵥ (QED.GradedProof.SE2.seOneLoopLimit Q (t • p) *ᵥ u)) =
      fun t => I * S (-(t * Q.m)) * (w ⬝ᵥ u) := by
    funext t
    have hd : Minkowski.dot (t • p) (t • p) = -(-(t * Q.m)) ^ 2 := by
      rw [QED.GradedProof.SE2.dot_smul_smul, hp]
      ring
    simp only [QED.GradedProof.SE2.seOneLoopLimit, hd, QED.Dirac.slash_smul, Matrix.smul_mulVec,
      Matrix.add_mulVec, Matrix.one_mulVec, hu, dotProduct_smul, dotProduct_add, dotProduct_neg,
      smul_eq_mul, S]
    push_cast
    ring
  rw [hf]
  have hc : HasDerivAt (fun t : ℝ => -(t * Q.m)) (-Q.m) 1 := by
    have := ((hasDerivAt_id (1 : ℝ)).mul_const Q.m).neg
    simp only [id, one_mul] at this
    exact this
  have hS : HasDerivAt S (onShellδ₂ Q : ℂ) (-(1 * Q.m)) := by
    rw [one_mul]
    exact hasDerivAt_shell_one Q hm hmγ hΛ
  have h := ((hS.scomp 1 hc).const_mul I).mul_const (w ⬝ᵥ u)
  convert h using 1
  · funext t
    simp only [Function.comp_apply]
  · rw [Complex.real_smul]
    push_cast
    ring

/-- **The one-loop Ward identity between on-shell spinors**: `d/dt|₁ w Σ₁(t p) u` equals
`-(1/e) ∑_μ p_μ w V₁^μ(p, p) u`. -/
theorem hasDerivAt_sandwich_seOneLoopLimit_eq (Q : Params) (he : Q.e ≠ 0) (hm : 0 < Q.m)
    (hmγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ) {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -Q.m ^ 2)
    (hp0 : 0 < p 0) {u w : Fin 4 → ℂ} (hu : Dirac.slash p *ᵥ u = -((Q.m : ℂ) • u))
    (hw : w ᵥ* Dirac.slash p = -((Q.m : ℂ) • w)) :
    HasDerivAt (fun t : ℝ => w ⬝ᵥ (QED.GradedProof.SE2.seOneLoopLimit Q (t • p) *ᵥ u))
      (-(1 / (Q.e : ℂ)) * ∑ μ, ((Minkowski.lower p μ : ℝ) : ℂ) * (w ⬝ᵥ (vOne Q p μ *ᵥ u))) 1 := by
  convert hasDerivAt_sandwich_seOneLoopLimit Q hm hmγ hΛ hp hu (w := w) using 1
  rw [sum_lower_sandwich_vOne Q hm hmγ hΛ hp hp0 hu hw,
    QED.TwoLoop.Ward.chargeA0_eq_neg_onShellδ₂ Q hm hmγ hΛ]
  have he' : (Q.e : ℂ) ≠ 0 := by exact_mod_cast he
  push_cast
  field_simp

end QED.GradedProof.WI2

end
