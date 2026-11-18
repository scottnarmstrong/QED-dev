-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.VertexOrderFive
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Frozen.TwoLoop.VertexOrderFive
public import QED.Provider.Lepton.VertexOrderFiveLeptonFlavorsZero

@[expose] public section

open QED.WickModel (Params)

namespace QED.Lepton

/-- (E₃) **The electron alone: the vertex.** With no heavy lepton, the order-`e⁵` vertex (F₉) of
the multi-lepton model is T1's (HV₁). From (E₁′) and (E₂) with
`Fin 3 ⊕ Fin 0 × Fin 3 ≃ Fin 3`. -/
theorem vertexOrderFive_leptonFlavors_zero (P : Params) (H : Fin 0 → HeavyLepton) :
    vertexOrderFive P (leptonFlavors P H) = QED.TwoLoop.vertexOrderFive P :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Lepton

end
-- FROZEN_ANCHOR_SUFFIX_END
