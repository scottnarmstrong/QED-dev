/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.RepsIntDBInt
public import QED.Frozen.VPChain.IsVPChain

/-!
# (HC₀) from the remaining representatives

Helper for obligation O3-5 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53). Eight of the nine
representatives are integrable at `ε > 0` under the Pauli–Villars conditions:
* `repDD s₀ s₁` (one loop): `QED.ChainProof.RepsInt.chainValueIntegrable_repDD`;
* `repBD s`, `repDB s` (two loops): `QED.ChainProof.RepsInt.chainValueIntegrable_repBD`,
  `QED.ChainProof.RepsInt.chainValueIntegrable_repDB`.

So `QED.ChainProof.RepsIntegrable` reduces to the three-loop bubble–bubble representative
(`RepsRemaining`), and (HC₀) follows from it with exactly its frozen statement and binders
(`jointEnergyFirstIntegrable_vertexChain_two'_of_remaining`).
-/

@[expose] public section

namespace QED.ChainProof

open QED.WickModel QED.ChainProof.Enum

/-- **What remains of (HC₀)**: (T₉′) for the value integrand of the three-loop bubble–bubble
representative `repBB`, at `ε > 0` under the Pauli–Villars conditions and momentum
conservation. -/
def RepsRemaining : Prop :=
  ∀ P : Params, 0 < P.ε → 1 + P.c₁ + P.c₂ = 0 → P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0 →
    ∀ pOut pIn kIn : Fin 1 → Fin 4 → ℝ, pOut 0 = pIn 0 + kIn 0 → ∀ αOut βIn μ : Fin 1 → Fin 4,
      ChainValueIntegrable P repBB pOut pIn kIn αOut βIn μ

/-- `RepsIntegrable` from the bubble–bubble representative and the eight proved ones. -/
theorem repsIntegrable_of_remaining (hrem : RepsRemaining) (P : Params) (hε : 0 < P.ε)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) : RepsIntegrable P pOut pIn kIn αOut βIn μ := by
  exact ⟨hrem P hε hc₁ hc₂ pOut pIn kIn hmom αOut βIn μ,
    RepsInt.chainValueIntegrable_repBD P αOut βIn μ hε hc₁ hc₂ hmom,
    RepsInt.chainValueIntegrable_repDB P αOut βIn μ hε hc₁ hc₂ hmom,
    RepsInt.chainValueIntegrable_repDD P hε hmom αOut βIn μ⟩

/-- **(HC₀) from the bubble–bubble representative**: the conclusion and binders are those of the
frozen `QED.VPChain.jointEnergyFirstIntegrable_vertexChain_two`, with the extra hypothesis
`RepsRemaining` ((T₉′) for `repBB`). -/
theorem jointEnergyFirstIntegrable_vertexChain_two'_of_remaining (hrem : RepsRemaining)
    (P : Params) (hε : 0 < P.ε)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) (hC : QED.VPChain.IsVPChain 2 C)
    {pOut pIn : Fin 1 → Fin 4 → ℝ} {kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ :=
  jointEnergyFirstIntegrable_vertexChain_two_of_reps P hε hc₁ hc₂ C hC hmom αOut βIn μ
    (repsIntegrable_of_remaining hrem P hε hc₁ hc₂ hmom αOut βIn μ)

end QED.ChainProof

end
