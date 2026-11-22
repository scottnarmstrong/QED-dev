/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetA
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable
public import QED.Frozen.TwoLoop.LineMomentum
public import QED.Frozen.TwoLoop.LoopCount
public import QED.Frozen.Graded.RegulatedAmplitude
public import QED.Frozen.Graded.GradedOrder
public import QED.ChainProof.SetALinkIntFinal

/-!
# Provider for `QED.ThreeLoop.jointEnergyFirstIntegrable_setA`

Proves the frozen theorem goal (HA₀) (Phase 5 Stage 3a/3b packet, decision D-58) as
`QED.Provider.ThreeLoop.jointEnergyFirstIntegrable_setA`, with the binder convention of decision
D-13. The proof is `QED.ChainProof.SetALink.jointEnergyFirstIntegrable_setA_final`, which
discharges the nine class obligations of the set (a) family. This module must never import the
frozen anchor.
-/

@[expose] public section

open QED.WickModel (Params Contraction loopCount lineMomentum₂)

namespace QED.Provider.ThreeLoop

/-- (HA₀), with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem jointEnergyFirstIntegrable_setA {P : Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : Lepton.Flavors F} {D : Graded.Counterterms F} {rep : F → F}
    (hε : 0 < P.ε := by assumption)
    (hrep : ∀ f, rep (rep f) = rep f := by assumption)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0 := by
      assumption)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0 := by
      assumption)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0 := by assumption)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} {g : Graded.Grading κ}
    (hg : Graded.gradedOrder κ g = 7 := by assumption) {C : Contraction 1 1 κ}
    (hC : QED.ThreeLoop.IsSetA C := by assumption)
    {pOut pIn : Fin 1 → Fin 4 → ℝ} {kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0 := by assumption)
    {αOut βIn μ : Fin 1 → Fin 4} :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        Graded.regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn
          μ :=
  QED.ChainProof.SetALink.jointEnergyFirstIntegrable_setA_final P Φ D rep hε hrep hPV₁ hPV₂ hD
    g hg C hC pOut pIn kIn hmom αOut βIn μ

end QED.Provider.ThreeLoop

end
