-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.ContractionValue
public import QED.Frozen.TwoLoop.ContractionValue
public import QED.Provider.VPChain.ContractionValueParams

@[expose] public section

open QED.WickModel (Params Contraction)
open QED.Lepton (contractionValue₂)

namespace QED.VPChain

/-- (M₃) **At T1's flavours the value is T1's** (definitional; obligation O3-16): with `F = Fin 3`,
`mass = P.mass` (X₀′), `coeff = P.loopCoeff` (X₀″) and open line `0`, the value (F₇), from which
(C₂) and (C₃) are built, is the frozen (T₁₀) of packet T1, for every contraction and so at any
number of loops. -/
theorem contractionValue₂_params (P : Params) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) :
    contractionValue₂ P ⟨P.mass, P.loopCoeff, 0⟩ C = QED.WickModel.contractionValue₂ P C :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.VPChain

end
-- FROZEN_ANCHOR_SUFFIX_END
