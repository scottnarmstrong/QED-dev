-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.VertexOrderFive
public import QED.Frozen.TwoLoop.VertexOrderFive
public import QED.Provider.Lepton.VertexOrderFiveParams

@[expose] public section

open QED.WickModel (Params)

namespace QED.Lepton

/-- (E₁′) The same for the order-`e⁵` vertex: (F₉) at T1's flavours is (HV₁). -/
theorem vertexOrderFive_params (P : Params) :
    vertexOrderFive P ⟨P.mass, P.loopCoeff, 0⟩ = QED.TwoLoop.vertexOrderFive P :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Lepton

end
-- FROZEN_ANCHOR_SUFFIX_END
