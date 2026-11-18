-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.OnePIFunction
public import QED.Frozen.WickModel.OnePIFunction
public import QED.Provider.Lepton.OnePIFunctionOneZero

@[expose] public section

open QED.WickModel (Params)

namespace QED.Lepton

/-- (E₅) **The electron conditions do not see the flavours.** For any flavour data whose open
line has the mass `P.m`, the one-electron 1PI function (F₈) through order `3` is packet 6a's
(X₂₈): a 1PI contraction of the one-electron function of order at most `3` has no closed fermion
loop, so its only flavouring is the constant open-line one, with weight `1`. Hence the electron
condition (Z₅), defined through (X₂₈) at order `2`, is the right condition for every flavour set,
and the multi-lepton headline reuses it unchanged; the charge condition (K₀) does not involve the
Wick model at all. -/
theorem onePIFunction₂_one_zero (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Flavors F)
    (hΦ : Φ.mass Φ.openLine = P.m) {K : ℕ} (hK : K ≤ 3) :
    onePIFunction₂ P Φ 1 0 K = QED.WickModel.onePIFunction P 1 0 K :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Lepton

end
-- FROZEN_ANCHOR_SUFFIX_END
