/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.WickVertex
public import QED.Frozen.OneLoop.VertexFunction
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.Basic
import QED.Frozen.Wick.WickVertexEq
import QED.Frozen.OneLoop.VertexOneLoopSpec
import Mathlib.Analysis.Complex.Basic

/-!
# Provider for `QED.Wick.tendsto_wickVertex`

Proves packet 5's headline goal (W₂) (decision D-20) as `QED.Provider.Wick.tendsto_wickVertex`,
with the binder convention of decision D-13. This module must never import the frozen anchor
(W₂). It consumes the sealed theorem (W₁) `QED.Wick.wickVertex_eq` and the frozen
characterization `QED.OneLoop.tendsto_energyFirstIntegral_iff_vertexOneLoop` of the one-loop
vertex (F′).
-/

@[expose] public section

open Complex Filter Topology

namespace QED.Provider.Wick

/-- Packet 5's (W₂), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem tendsto_wickVertex {e δ₁ δ₂ δm δ₃ m mγ Λ : ℝ} (hm : 0 < m := by assumption)
    (hmγ : 0 < mγ := by assumption) (hΛ : 0 < Λ := by assumption) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2 := by assumption)
    (hp : Minkowski.dot p p = -m ^ 2 := by assumption) (hp0' : 0 < p' 0 := by assumption)
    (hp0 : 0 < p 0 := by assumption) {μ i j : Fin 4} :
    Tendsto (fun ε => (1 / I) * QED.Wick.wickVertex e δ₁ δ₂ δm δ₃ m mγ Λ ε p' p μ i j) (𝓝[>] 0)
      (𝓝 (QED.OneLoop.vertexFunction e (1 + δ₁) m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 μ i j)) := by
  have hlim := (QED.OneLoop.tendsto_energyFirstIntegral_iff_vertexOneLoop e m mγ Λ hm hmγ hΛ p' p
    hp' hp hp0' hp0 μ i j _).2 rfl
  have hW : ∀ ε, (1 / I) * QED.Wick.wickVertex e δ₁ δ₂ δm δ₃ m mγ Λ ε p' p μ i j =
      (1 / I) * ((I * (((1 + δ₁) * e : ℝ) : ℂ)) * Dirac.gamma μ i j +
        QED.OneLoop.energyFirstIntegral fun ℓ =>
          QED.OneLoop.vertexIntegrand e m mγ Λ ε p' p μ ℓ i j) := fun ε => by
    rw [QED.Wick.wickVertex_eq]
    simp
  simp_rw [hW]
  have hfin : QED.OneLoop.vertexFunction e (1 + δ₁) m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 μ i j =
      (1 / I) * ((I * (((1 + δ₁) * e : ℝ) : ℂ)) * Dirac.gamma μ i j +
        I * QED.OneLoop.vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 μ i j) := by
    simp only [QED.OneLoop.vertexFunction, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
  rw [hfin]
  exact (tendsto_const_nhds.add hlim).const_mul (1 / I)

end QED.Provider.Wick

end
