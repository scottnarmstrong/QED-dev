-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.OnePIFunction
public import QED.Frozen.TwoLoop.OnePIFunction
public import QED.Provider.Lepton.OnePIFunctionParams

@[expose] public section

open QED.WickModel (Params)

namespace QED.Lepton

/-- (E₁) **The successor at T1's flavours is T1** (definitional): with `F = Fin 3`,
`mass = P.mass` (X₀′), `coeff = P.loopCoeff` (X₀″) and open line `0`, the 1PI function (F₈) is
(T₁₁). -/
theorem onePIFunction₂_params (P : Params) :
    onePIFunction₂ P ⟨P.mass, P.loopCoeff, 0⟩ = QED.WickModel.onePIFunction₂ P :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Lepton

end
-- FROZEN_ANCHOR_SUFFIX_END
