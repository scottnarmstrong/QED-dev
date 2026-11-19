/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.ConnectedPart
public import QED.Frozen.WickModel.ConnectedFunction
import QED.GradedProof.EmbedOrder

/-!
# Provider for `QED.Graded.connectedPart_eq_connectedFunction_sub`

Proves the frozen theorem goal `QED.Graded.connectedPart_eq_connectedFunction_sub` (Phase 5 Stage 2
packet, decision D-57) as `QED.Provider.Graded.connectedPart_eq_connectedFunction_sub`, with the
binder convention of decision D-13, from the helper in `QED.GradedProof.EmbedOrder`. The anchor is
sealed (D-57 seal note).
-/

public section

open QED.WickModel (Params)
open QED.Graded

namespace QED.Provider.Graded

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem connectedPart_eq_connectedFunction_sub {P : Params} {D : Counterterms (Fin 3)}
    (h₁ : P.δ₁ = P.e ^ 2 * D.d₁ 0 0 := by assumption)
    (h₂ : P.δ₂ = P.e ^ 2 * D.d₂ 0 0 := by assumption)
    (hm : P.δm = P.e ^ 2 * D.dm 0 0 := by assumption)
    (h₃ : P.δ₃ = P.e ^ 2 * D.d₃ 0 := by assumption)
    (hD : ∀ f k, 1 ≤ k → D.d₁ f k = 0 ∧ D.d₂ f k = 0 ∧ D.dm f k = 0 := by assumption)
    (hD₃ : ∀ k, 1 ≤ k → D.d₃ k = 0 := by assumption) {nf nA K : ℕ}
    (hK : K + 1 ≤ 2 * nf + nA + 1 := by assumption) {pOut pIn : Fin nf → Fin 4 → ℝ}
    {kIn : Fin nA → Fin 4 → ℝ} {αOut βIn : Fin nf → Fin 4} {μ : Fin nA → Fin 4} :
    connectedPart P ⟨P.mass, P.loopCoeff, 0⟩ D nf nA (K + 1) pOut pIn kIn αOut βIn μ =
      WickModel.connectedFunction P nf nA (K + 1) pOut pIn kIn αOut βIn μ -
        WickModel.connectedFunction P nf nA K pOut pIn kIn αOut βIn μ :=
  QED.GradedProof.connectedPart_eq_connectedFunction_sub' P D h₁ h₂ hm h₃ hD hD₃ nf nA K hK
    pOut pIn kIn αOut βIn μ

end QED.Provider.Graded

end
