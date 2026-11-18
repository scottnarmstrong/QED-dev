-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.OnePIFunction
public import QED.Provider.Lepton.OnePIFunctionRelabel

@[expose] public section

open QED.WickModel (Params)

namespace QED.Lepton

/-- (E₂) **Relabelling the flavours** does not change the 1PI function: if `e : F ≃ G` carries
the masses, the loop coefficients and the open-line flavour of `Φ` to those of `Ψ`, then (F₈)
is the same for `Φ` and `Ψ`. (Composition with `e` is a bijection of the flavourings (F₁) that
preserves (F₃), the weight (F₄) and the amplitude (F₅).) -/
theorem onePIFunction₂_relabel (P : Params) {F G : Type} [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] (e : F ≃ G)
    (Φ : Flavors F) (Ψ : Flavors G) (hmass : ∀ f, Ψ.mass (e f) = Φ.mass f)
    (hcoeff : ∀ f, Ψ.coeff (e f) = Φ.coeff f) (hopen : e Φ.openLine = Ψ.openLine) :
    onePIFunction₂ P Φ = onePIFunction₂ P Ψ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Lepton.onePIFunction₂_relabel
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Lepton

end
-- FROZEN_ANCHOR_SUFFIX_END
