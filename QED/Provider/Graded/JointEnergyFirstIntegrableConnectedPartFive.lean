/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.GradedOrder
public import QED.Frozen.Graded.RegulatedAmplitude
public import QED.Frozen.TwoLoop.LineMomentum
public import QED.Frozen.TwoLoop.LoopCount
public import QED.Frozen.WickModel.ExternalsAttached
public import QED.Frozen.WickModel.VerticesConnected
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable
public import QED.GradedProof.X0Final

/-!
# Provider for `QED.Graded.jointEnergyFirstIntegrable_connectedPart_five`

Proves the frozen theorem goal `QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (Phase 5
Stage 2 packet, decision D-57) as
`QED.Provider.Graded.jointEnergyFirstIntegrable_connectedPart_five`, with the binder convention of
decision D-13, from
`QED.GradedProof.X0.jointEnergyFirstIntegrable_connectedPart_five'`. This module must never import
the frozen anchor.
-/

@[expose] public section

open QED.WickModel (Params Contraction ExternalsAttached VerticesConnected loopCount lineMomentum₂)
open QED.Graded

namespace QED.Provider.Graded

/-- (X₀), with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem jointEnergyFirstIntegrable_connectedPart_five {P : Params} {F : Type} [Fintype F]
    [DecidableEq F] {Φ : Lepton.Flavors F} {D : Counterterms F} {rep : F → F}
    (hε : 0 < P.ε := by assumption)
    (hrep : ∀ f, rep (rep f) = rep f := by assumption)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0 := by
      assumption)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0 := by
      assumption)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0 := by assumption)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} {g : Grading κ}
    (hg : gradedOrder κ g = 5 := by assumption)
    {C : Contraction 1 1 κ} (hC : ExternalsAttached C ∧ VerticesConnected C := by assumption)
    {pOut pIn : Fin 1 → Fin 4 → ℝ} {kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0 := by assumption)
    {αOut βIn μ : Fin 1 → Fin 4} :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ :=
  QED.GradedProof.X0.jointEnergyFirstIntegrable_connectedPart_five' P Φ D rep hε hrep hPV₁ hPV₂
    hD g hg C hC pOut pIn kIn hmom αOut βIn μ

end QED.Provider.Graded

end
