-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.IsPhotonOnShellAt
public import QED.Frozen.Lepton.IsPhotonOnShell
public import QED.Provider.Graded.IsPhotonOnShellAtOneIff

@[expose] public section

open QED.WickModel (Params)

namespace QED.Graded

/-- (E-G₂ₚ) **The order-`e²` photon condition is (F₁₁)** (memo (E-G₂)): (G₁₁) at `n = 1` holds if
and only if the flavour-summed photon condition (F₁₁) holds with `δ₃ = e² d₃ 0`. The order-`2`
two-photon 1PI terms are the one-loop flavour-summed bubbles and the `photonCt` vertex, which
carry no fermion counterterm, so the theorem has no hypothesis. -/
theorem isPhotonOnShellAt_one_iff (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) :
    IsPhotonOnShellAt P Φ D 1 ↔ Lepton.IsPhotonOnShell { P with δ₃ := P.e ^ 2 * D.d₃ 0 } Φ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
