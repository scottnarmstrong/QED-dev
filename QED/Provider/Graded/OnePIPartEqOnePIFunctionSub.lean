/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.OnePIPart
public import QED.Frozen.Lepton.OnePIFunction
import QED.GradedProof.EmbedOrder

/-!
# Provider for `QED.Graded.onePIPart_eq_onePIFunction₂_sub`

Proves the frozen theorem goal `QED.Graded.onePIPart_eq_onePIFunction₂_sub` (Phase 5 Stage 2 packet,
decision D-57) as `QED.Provider.Graded.onePIPart_eq_onePIFunction₂_sub`, with the binder convention
of decision D-13, from the helper in `QED.GradedProof.EmbedOrder`. The anchor is sealed (D-57 seal
note).
-/

public section

open QED.WickModel (Params)
open QED.Graded

namespace QED.Provider.Graded

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem onePIPart_eq_onePIFunction₂_sub {P : Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : Lepton.Flavors F} {D : Counterterms F}
    (hmass : Φ.mass Φ.openLine = P.m := by assumption)
    (h₁ : P.δ₁ = P.e ^ 2 * D.d₁ Φ.openLine 0 := by assumption)
    (h₂ : P.δ₂ = P.e ^ 2 * D.d₂ Φ.openLine 0 := by assumption)
    (hm : P.δm = P.e ^ 2 * D.dm Φ.openLine 0 := by assumption)
    (h₃ : P.δ₃ = P.e ^ 2 * D.d₃ 0 := by assumption)
    (hD : ∀ f k, 1 ≤ k → D.d₁ f k = 0 ∧ D.d₂ f k = 0 ∧ D.dm f k = 0 := by assumption)
    (hD₃ : ∀ k, 1 ≤ k → D.d₃ k = 0 := by assumption) {nf nA K : ℕ}
    (hnf : 1 ≤ nf := by assumption) (hK : K + 1 ≤ 2 * nf + nA + 3 := by assumption)
    {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ} {αOut βIn : Fin nf → Fin 4}
    {μ : Fin nA → Fin 4} :
    onePIPart P Φ D nf nA (K + 1) pOut pIn kIn αOut βIn μ =
      Lepton.onePIFunction₂ P Φ nf nA (K + 1) pOut pIn kIn αOut βIn μ -
        Lepton.onePIFunction₂ P Φ nf nA K pOut pIn kIn αOut βIn μ :=
  QED.GradedProof.onePIPart_eq_onePIFunction₂_sub' P Φ D hmass h₁ h₂ hm h₃ hD hD₃ nf nA K hnf hK
    pOut pIn kIn αOut βIn μ

end QED.Provider.Graded

end
