/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.VertexPart
public import QED.Frozen.Lepton.VertexOrderFive
import QED.GradedProof.VertexTwo

/-!
# Provider for `QED.Graded.vertexPart_two_eq`

Proves the frozen theorem goal `QED.Graded.vertexPart_two_eq` (Phase 5 Stage 2 packet, decision
D-57) as `QED.Provider.Graded.vertexPart_two_eq`, with the binder convention of decision D-13, from
the helper in `QED.GradedProof.VertexTwo`. The anchor is sealed (D-57 seal note).
-/

public section

open QED.WickModel (Params)
open QED.Graded

namespace QED.Provider.Graded

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem vertexPart_two_eq {P : Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : Lepton.Flavors F} {D : Counterterms F}
    (hmass : Φ.mass Φ.openLine = P.m := by assumption)
    (h₁ : P.δ₁ = P.e ^ 2 * D.d₁ Φ.openLine 0 := by assumption)
    (h₂ : P.δ₂ = P.e ^ 2 * D.d₂ Φ.openLine 0 := by assumption)
    (hm : P.δm = P.e ^ 2 * D.dm Φ.openLine 0 := by assumption)
    (h₃ : P.δ₃ = P.e ^ 2 * D.d₃ 0 := by assumption) {p' p : Fin 4 → ℝ} {μ : Fin 4} :
    vertexPart P Φ D Φ.openLine 2 p' p μ =
      Lepton.vertexOrderFive P Φ p' p μ +
        ((P.e ^ 4 * D.d₁ Φ.openLine 1 * P.e : ℝ) : ℂ) • Dirac.gamma μ :=
  QED.GradedProof.vertexPart_two_eq' P Φ D hmass h₁ h₂ hm h₃ p' p μ

end QED.Provider.Graded

end
