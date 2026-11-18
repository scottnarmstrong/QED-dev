/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.OnePIFunction
public import QED.Frozen.Lepton.VertexOrderFive
public import QED.Frozen.TwoLoop.OnePIFunction
public import QED.Frozen.TwoLoop.VertexOrderFive

/-!
# The flavour successor at T1's flavours is T1 (definitional)

Helper-level proofs for the Phase 5 Stage 0 packet (decision D-50), goals (E₁) and (E₁′): with
`F = Fin 3`, `mass = P.mass`, `coeff = P.loopCoeff` and open line `0`, the flavour-successor 1PI
function and order-`e⁵` vertex are T1's, by `rfl`.

## Main statements

* `onePIFunction₂_params'`: the frozen goal `QED.Lepton.onePIFunction₂_params`.
* `vertexOrderFive_params'`: the frozen goal `QED.Lepton.vertexOrderFive_params`.
-/

@[expose] public section

open QED.WickModel (Params)

namespace QED.Lepton.Proof

/-- (E₁) The 1PI function of the successor at T1's flavours is (T₁₁). -/
theorem onePIFunction₂_params' (P : Params) :
    onePIFunction₂ P ⟨P.mass, P.loopCoeff, 0⟩ = QED.WickModel.onePIFunction₂ P :=
  rfl

/-- (E₁′) The order-`e⁵` vertex of the successor at T1's flavours is (HV₁). -/
theorem vertexOrderFive_params' (P : Params) :
    vertexOrderFive P ⟨P.mass, P.loopCoeff, 0⟩ = QED.TwoLoop.vertexOrderFive P :=
  rfl

end QED.Lepton.Proof

end
