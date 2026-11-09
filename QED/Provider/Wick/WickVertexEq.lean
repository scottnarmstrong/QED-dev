/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.WickVertex
public import QED.Frozen.OneLoop.VertexIntegrand
import QED.Wick.Classification
import QED.Wick.ChainValue

/-!
# Provider for `QED.Wick.wickVertex_eq`

Proves packet 5's theorem goal (W₁) (obligations O-1, O-2; decision D-20) as
`QED.Provider.Wick.wickVertex_eq`, with the binder convention of decision D-13. This module must
never import the frozen anchor.

`QED.Wick.wickVertex_eq_chains` reduces the Wick vertex to the two tree contractions, which give
`i (1 + δ₁) e γ^μ`, plus `1/6` times the sum over the vertex-correction contractions of three
gauge vertices. There are six of these (`QED.Wick.card_isChain`). Each has the value of the
frozen one-loop integral (`QED.Wick.contractionValue_of_isChain`).
-/

@[expose] public section

open Complex

namespace QED.Provider.Wick

open scoped Classical in
/-- Packet 5's (W₁), with implicit data binders (decision D-13). -/
theorem wickVertex_eq {e δ₁ δ₂ δm δ₃ m mγ Λ ε : ℝ} {p' p : Fin 4 → ℝ} {μ : Fin 4} :
    QED.Wick.wickVertex e δ₁ δ₂ δm δ₃ m mγ Λ ε p' p μ =
      (I * (((1 + δ₁) * e : ℝ) : ℂ)) • Dirac.gamma μ +
        Matrix.of fun i j => QED.OneLoop.energyFirstIntegral fun ℓ =>
          QED.OneLoop.vertexIntegrand e m mγ Λ ε p' p μ ℓ i j := by
  rw [QED.Wick.wickVertex_eq_chains]
  congr 1
  rw [Finset.sum_congr rfl fun C hC => by
      obtain ⟨a, b, c, h⟩ := (Finset.mem_filter.mp hC).2
      exact QED.Wick.contractionValue_of_isChain e δ₁ δ₂ δm δ₃ m mγ Λ ε p' p μ h,
    Finset.sum_const, QED.Wick.card_isChain, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num

end QED.Provider.Wick

end
