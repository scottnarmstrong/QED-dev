/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.OnePIFamilyFunction
public import QED.Frozen.Lepton.OnePIFunction
import QED.ChainProof.QuickMeaning

/-!
# Provider for `QED.VPChain.onePIFamilyFunction₂_true`

Proves the frozen theorem goal `QED.VPChain.onePIFamilyFunction₂_true` (Phase 5 Stage 1a packet,
decision D-53) as `QED.Provider.VPChain.onePIFamilyFunction₂_true`, with the binder convention of
decision D-13, from the helper in `QED.ChainProof.QuickMeaning`. This module must never import the
frozen anchor.
-/

public section

open QED.WickModel (Params)
open QED.Lepton (Flavors onePIFunction₂ onePIFamilyFunction₂)

namespace QED.Provider.VPChain

open QED.VPChain

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem onePIFamilyFunction₂_true {P : Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : Flavors F} {nf nA : ℕ} :
    onePIFamilyFunction₂ P Φ nf nA (fun _ => True) = onePIFunction₂ P Φ nf nA :=
  QED.ChainProof.onePIFamilyFunction₂_true' P Φ nf nA

end QED.Provider.VPChain

end
