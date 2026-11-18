/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.OnePIFunction
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable
import QED.TwoLoop.IntegrableOrderFive

/-!
# Provider for `QED.TwoLoop.jointEnergyFirstIntegrable_vertexOrderFive`

Proves the frozen theorem goal (HV₀) (decision D-45) as
`QED.Provider.TwoLoop.jointEnergyFirstIntegrable_vertexOrderFive`, with the binder convention of
decision D-13. The proof is
`QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_of_order_five`: by cases on the number of vertices, every 1PI contraction of total order `5` is a relabelling of
a counterterm representative (δ₁, δ₂, δ_m, δ₃ classes, integrable at `ε > 0`) or of a class
representative of five gauge vertices (the open-line classes, VP, F₊, F₋; the last three use the
Pauli–Villars conditions), and (T₉′) transfers along relabellings. This module must never import
the frozen anchor.
-/

public section

namespace QED.Provider.TwoLoop

open QED.WickModel in
/-- (HV₀), with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem jointEnergyFirstIntegrable_vertexOrderFive {P : Params} (hε : 0 < P.ε := by assumption)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0 := by assumption)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0 := by assumption)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} (hκ : ∑ t, (κ t).order = 5 := by assumption)
    {C : Contraction 1 1 κ} (hC : IsOnePI C := by assumption) {pOut pIn : Fin 1 → Fin 4 → ℝ}
    {kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0 := by assumption)
    {αOut βIn μ : Fin 1 → Fin 4} :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ :=
  QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_of_order_five P hε hc₁ hc₂ hκ C hC
    hmom αOut βIn μ

end QED.Provider.TwoLoop

end
