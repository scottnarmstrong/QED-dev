/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.OneLoop.ChargeRenormalization
import Mathlib.Tactic.LinearCombination

/-!
# The charge condition for the frozen vertex function

Facts about the frozen vertex function `QED.OneLoop.vertexFunction` and the frozen charge
condition `QED.OneLoop.IsChargeNormalized` (packet 3, decision D-15), used by the providers of
packet 3's theorems:

* `sandwich_vertexFunction_self`: at `p' = p` the sandwich is `e (Z₁ + A₀) ū γ^μ u`;
* `isChargeNormalized_chargeZ`: `Z₁ = 1 - A₀` satisfies the charge condition;
* `eq_chargeZ_of_isChargeNormalized`: for `e ≠ 0` it is the only solution;
* `isFormFactorPair_vertexOneLoop_iff_vertexFunction_aux`: the counterterm shifts only `F₁`.

These are internal helpers.
-/

@[expose] public section

open Matrix Complex
open QED.OneLoop QED.Integration
open scoped Real

namespace QED.OneLoop.VertexLimit

/-- The value of the loop's `γ^μ` coefficient at `q² = 0`. -/
noncomputable def chargeA0 (e m mγ Λ : ℝ) : ℝ :=
  e ^ 2 / (16 * π ^ 2) * ∫ z, formIntegrandAq m mγ Λ 0 z ∂feynmanMeasure

/-- The counterterm fixed by the charge condition. -/
noncomputable def chargeZ (e m mγ Λ : ℝ) : ℝ := 1 - chargeA0 e m mγ Λ

theorem sandwich_vertexFunction_self {e Z₁ m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -m ^ 2) (hp0 : 0 < p 0) (μ : Fin 4)
    {u w : Fin 4 → ℂ} (hu : Dirac.slash p *ᵥ u = -((m : ℂ) • u))
    (hw : w ᵥ* Dirac.slash p = -((m : ℂ) • w)) :
    w ⬝ᵥ (vertexFunction e Z₁ m mγ Λ hm hmγ hΛ p p hp hp hp0 hp0 μ *ᵥ u)
      = (e : ℂ) * ((Z₁ + chargeA0 e m mγ Λ : ℝ) : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)) := by
  simp only [vertexFunction, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  rw [sandwich_vertexOneLoop_self hm hmγ hΛ hp hp0 μ hu hw]
  simp only [chargeA0]; push_cast; ring

theorem isChargeNormalized_chargeZ {e m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    IsChargeNormalized e (chargeZ e m mγ Λ) m mγ Λ hm hmγ hΛ := by
  intro p hp hp0 μ u w hu hw
  rw [sandwich_vertexFunction_self hm hmγ hΛ hp hp0 μ hu hw]
  simp only [chargeZ]; push_cast; ring

theorem eq_chargeZ_of_isChargeNormalized {e Z₁ m mγ Λ : ℝ} (he : e ≠ 0) (hm : 0 < m)
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hZ : IsChargeNormalized e Z₁ m mγ Λ hm hmγ hΛ) :
    Z₁ = chargeZ e m mγ Λ := by
  set pr : Fin 4 → ℝ := Pi.single 0 m
  have hpr : Minkowski.dot pr pr = -m ^ 2 := by simp [pr, Minkowski.dot_eq]; ring
  have hpr0 : 0 < pr 0 := by simp [pr, hm]
  obtain ⟨u, w, hu, hw, hne⟩ := exists_sandwich_gamma_zero_ne_zero hm hpr hpr0
  have h := hZ pr hpr hpr0 0 u w hu hw
  rw [sandwich_vertexFunction_self hm hmγ hΛ hpr hpr0 0 hu hw] at h
  have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he
  have h2 : ((Z₁ + chargeA0 e m mγ Λ : ℝ) : ℂ) = 1 := by
    have h3 : (e : ℂ) * (((Z₁ + chargeA0 e m mγ Λ : ℝ) : ℂ) - 1) * (w ⬝ᵥ (Dirac.gamma 0 *ᵥ u))
        = 0 := by linear_combination h
    rcases mul_eq_zero.mp h3 with h4 | h4
    · rcases mul_eq_zero.mp h4 with h5 | h5
      · exact absurd h5 he'
      · exact sub_eq_zero.mp h5
    · exact absurd h4 hne
  have h3 : Z₁ + chargeA0 e m mγ Λ = 1 := by exact_mod_cast h2
  simp only [chargeZ]; linarith

theorem isFormFactorPair_vertexOneLoop_iff_vertexFunction_aux {e Z₁ m mγ Λ : ℝ} (hm : 0 < m)
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (F : ℂ × ℂ) :
    IsFormFactorPair e m p' p (vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0) F ↔
      IsFormFactorPair e m p' p (vertexFunction e Z₁ m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0)
        ((Z₁ : ℂ) + F.1, F.2) := by
  unfold IsFormFactorPair
  constructor
  · intro h μ u w hu hw
    have h1 := h μ u w hu hw
    simp only [vertexFunction, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec,
      dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h1 ⊢
    rw [h1]; push_cast; ring
  · intro h μ u w hu hw
    have h1 := h μ u w hu hw
    simp only [vertexFunction, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec,
      dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h1 ⊢
    push_cast at h1
    linear_combination h1

end QED.OneLoop.VertexLimit

end
