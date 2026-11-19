/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.VPChain.IsVPChain
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable
public import QED.Frozen.TwoLoop.RegulatedAmplitude
public import QED.Frozen.TwoLoop.LineMomentum
public import QED.Frozen.TwoLoop.LoopCount
import QED.ChainProof.RepsIntBBFinal

/-!
# Provider for `QED.VPChain.jointEnergyFirstIntegrable_vertexChain_two`

Proves the frozen theorem goal (HC₀) (Phase 5 Stage 1a packet, decision D-53) as
`QED.Provider.VPChain.jointEnergyFirstIntegrable_vertexChain_two`, with the binder convention of
decision D-13. The proof is `QED.ChainProof.jointEnergyFirstIntegrable_vertexChain_two'`: the
nine set (b) representatives are integrable at `ε > 0` (`QED.ChainProof.RepsInt*`); the
bubble–bubble representative, the only three-loop one, by a common complex rotation of the three
loop energies (`QED.Integration.ThreeLoopRotation`), after which every denominator is elliptic
and each Pauli–Villars-summed bubble decays fast enough for joint integrability. This module must
never import the frozen anchor.
-/

public section

namespace QED.Provider.VPChain

open QED.WickModel in
/-- (HC₀), with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem jointEnergyFirstIntegrable_vertexChain_two {P : Params} (hε : 0 < P.ε := by assumption)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0 := by assumption)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0 := by assumption)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 1 1 κ}
    (hC : QED.VPChain.IsVPChain 2 C := by assumption) {pOut pIn : Fin 1 → Fin 4 → ℝ}
    {kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0 := by assumption)
    {αOut βIn μ : Fin 1 → Fin 4} :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ :=
  QED.ChainProof.jointEnergyFirstIntegrable_vertexChain_two' P hε hc₁ hc₂ C hC hmom αOut βIn μ

end QED.Provider.VPChain

end
