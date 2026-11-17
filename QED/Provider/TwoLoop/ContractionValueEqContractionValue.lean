/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.ContractionValue
public import QED.Frozen.TwoLoop.LoopCount
public import QED.Frozen.WickModel.ContractionValue
import QED.TwoLoop.OneLoopEmbedding

/-!
# Provider for `QED.WickModel.contractionValue₂_eq_contractionValue`

Proves packet T1's theorem goal (T₁₃) (decision D-38) as
`QED.Provider.TwoLoop.contractionValue₂_eq_contractionValue`, with the binder convention of
decision D-13. The content is
`QED.TwoLoop.contractionValue₂_eq_contractionValue_of_loopCount_le_one`: with at most one
chord the chords are the loop lines, the routing (T₄) is (X₂₂), and the joint prescription is
(D) or the evaluation at the empty family. This module must never import the frozen anchor.
-/

public section

open Complex

namespace QED.Provider.TwoLoop

open QED.WickModel in
/-- Packet T1's (T₁₃), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem contractionValue₂_eq_contractionValue {P : Params} {nf nA N : ℕ}
    {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}
    (hC : loopCount C ≤ 1 := by assumption) {pOut pIn : Fin nf → Fin 4 → ℝ}
    {kIn : Fin nA → Fin 4 → ℝ} {αOut βIn : Fin nf → Fin 4} {μ : Fin nA → Fin 4} :
    contractionValue₂ P C pOut pIn kIn αOut βIn μ =
      contractionValue P C pOut pIn kIn αOut βIn μ :=
  QED.TwoLoop.contractionValue₂_eq_contractionValue_of_loopCount_le_one P C hC pOut pIn kIn
    αOut βIn μ

end QED.Provider.TwoLoop

end
