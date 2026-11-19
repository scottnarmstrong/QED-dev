-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.OnePIFamilyFunction
public import QED.Frozen.Lepton.OnePIFunction
public import QED.Provider.VPChain.OnePIFamilyFunctionTrue

@[expose] public section

open QED.WickModel (Params)
open QED.Lepton (Flavors onePIFunction₂ onePIFamilyFunction₂)

namespace QED.VPChain

/-- (M₁) **The trivial family is the whole 1PI function** (obligation O3-16): with the family
predicate `True`, the family 1PI function (C₂) is the flavoured 1PI function (F₈), for every
order `K`. So (C₂) differs from (F₈) only by its filter. -/
theorem onePIFamilyFunction₂_true (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Flavors F) (nf nA : ℕ) :
    onePIFamilyFunction₂ P Φ nf nA (fun _ => True) = onePIFunction₂ P Φ nf nA :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.VPChain

end
-- FROZEN_ANCHOR_SUFFIX_END
