-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.IsOnShellAt
public import QED.Frozen.Graded.IsChargeNormalizedAt
public import QED.Provider.Graded.WardIdentityOne

@[expose] public section

open QED.WickModel (Params)

namespace QED.Graded

/-- (WI₂) **The two-loop Ward identity `Z₁ = Z₂` at order `e⁴`** (Srednicki (68.13) at order
`e⁴`; memo (WI₂); ruling S4 and decision D-37.2: proved, not imposed). For `e ≠ 0`, all flavour
masses and `m_γ, Λ` positive and the two Pauli–Villars conditions: if flavour `f` is on shell (G₉)
and charge normalized (G₁₀) at orders `e²` and `e⁴`, then `d₁ f 1 = d₂ f 1`. The order-`e⁴`
self-energy and order-`e⁵` vertex of flavour `f` carry no counterterm on a closed loop, so neither
the other flavours' counterterms nor the photon conditions enter (the one-loop bubbles they contain
are transverse for every `δ₃`). -/
theorem d₁_eq_d₂_one (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (he : P.e ≠ 0)
    (hmass : ∀ g, 0 < Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hPV₁ : ∑ g, Φ.coeff g = 0) (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0)
    (hon₁ : IsOnShellAt P Φ D f 1) (hK₁ : IsChargeNormalizedAt P Φ D f 1)
    (hon₂ : IsOnShellAt P Φ D f 2) (hK₂ : IsChargeNormalizedAt P Φ D f 2) :
    D.d₁ f 1 = D.d₂ f 1 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Graded.d₁_eq_d₂_one
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
