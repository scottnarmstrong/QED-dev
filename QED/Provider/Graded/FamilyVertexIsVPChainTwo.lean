/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.FamilyVertex
public import QED.Frozen.VPChain.VertexChain
import QED.ChainProof.EG4Bridge

/-!
# Provider for `QED.Graded.familyVertex_isVPChain_two`

Proves the frozen theorem goal (E-G₄) (Phase 5 Stage 3a/3b packet, decision D-58) as
`QED.Provider.Graded.familyVertex_isVPChain_two`, with the binder convention of decision D-13.
A two-insertion chain has total order `7` with every vertex at level `0`, so only the zero
grading contributes and the two sums agree term by term
(`QED.ChainProof.EG4.familyVertex_isVPChain_two'`). This module must never import the frozen
anchor.
-/

@[expose] public section

open QED.WickModel (Params IsOnePI)
open QED.Graded

namespace QED.Provider.Graded

/-- (E-G₄), with implicit data binders and a `by assumption` hypothesis (decision D-13). -/
theorem familyVertex_isVPChain_two {P : Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : Lepton.Flavors F} {D : Counterterms F}
    (h₃ : P.δ₃ = P.e ^ 2 * D.d₃ 0 := by assumption) {p' p : Fin 4 → ℝ} {μ : Fin 4} :
    familyVertex P Φ D (fun C _ => IsOnePI C ∧ VPChain.IsVPChain 2 C) 7 p' p μ =
      VPChain.vertexChain 2 P Φ p' p μ :=
  QED.ChainProof.EG4.familyVertex_isVPChain_two' P Φ D h₃ p' p μ

end QED.Provider.Graded

end
