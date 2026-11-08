/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.VertexOneLoopSpec
public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.OneLoop.PauliLimit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The form-factor pair of the frozen one-loop vertex

Facts about the frozen one-loop vertex `QED.OneLoop.vertexOneLoop` (packet 2, decision D-14)
and the frozen predicate `QED.OneLoop.IsFormFactorPair`, used by the providers of packet 2's
theorems (G) and (I):

* `vertexOneLoop_eq_limit`: the vertex is `1/i` times the closed-form limit;
* `isFormFactorPair_vertexOneLoop`: `(A, B) = (formFactorA, formFactorB)` is a form-factor pair;
* `eq_of_isFormFactorPair_vertexOneLoop`: for `e ≠ 0` and `q² > 0` it is the only one.

These are internal helpers.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open QED.OneLoop QED.Integration
open scoped Real

namespace QED.OneLoop.VertexLimit

theorem vertexOneLoop_eq_limit {e m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ : Fin 4) :
    vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 μ
      = Matrix.of (fun i j => (1 / I) * ∫ v, spatialG e m mγ Λ 0 p' p μ i j v) := by
  ext i j
  have h := (tendsto_energyFirstIntegral_iff_vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0'
    hp0 μ i j _).mp (tendsto_energyFirstIntegral_vertexIntegrand hm hmγ hΛ hp' hp hp0' hp0 μ i j)
  simp only [Matrix.of_apply]
  rw [h]
  field_simp

theorem isFormFactorPair_vertexOneLoop {e m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) :
    IsFormFactorPair e m p' p (vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0)
      ((formFactorA e m mγ Λ p' p : ℂ), (formFactorB e m mγ Λ p' p : ℂ)) := fun μ u w hu hw => by
  rw [vertexOneLoop_eq_limit hm hmγ hΛ hp' hp hp0' hp0 μ]
  exact sandwich_vertexLimit hm hmγ hΛ hp' hp hp0' hp0 μ hu hw

theorem eq_of_isFormFactorPair_vertexOneLoop {e m mγ Λ : ℝ} (he : e ≠ 0) (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) {F : ℂ × ℂ}
    (hF : IsFormFactorPair e m p' p (vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0) F) :
    F = ((formFactorA e m mγ Λ p' p : ℂ), (formFactorB e m mγ Λ p' p : ℂ)) := by
  have hex := isFormFactorPair_vertexOneLoop hm hmγ hΛ hp' hp hp0' hp0 (e := e)
  have hdiff : ∀ (μ : Fin 4) (u w : Fin 4 → ℂ), Dirac.slash p *ᵥ u = -((m : ℂ) • u) →
      w ᵥ* Dirac.slash p' = -((m : ℂ) • w) →
      w ⬝ᵥ (((F.1 - formFactorA e m mγ Λ p' p) • Dirac.gamma μ
        - (I / (m : ℂ) * (F.2 - formFactorB e m mγ Λ p' p)) •
          ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • Dirac.lorentzGen μ ν) *ᵥ u) = 0 := by
    intro μ u w hu hw
    have h1 := hF μ u w hu hw
    have h2 := hex μ u w hu hw
    rw [h1] at h2
    have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he
    have h3 := mul_left_cancel₀ he' h2
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul] at h3 ⊢
    linear_combination h3
  obtain ⟨h1, h2⟩ := Dirac.eq_zero_of_sandwich_formFactor_eq_zero hm hp' hp hq hdiff
  exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)

end QED.OneLoop.VertexLimit

end
