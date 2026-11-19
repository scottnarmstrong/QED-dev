-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.IsOnShellAt
public import QED.Frozen.Graded.IsChargeNormalizedAt
public import QED.Provider.Graded.WardIdentityZero

@[expose] public section

open QED.WickModel (Params)

namespace QED.Graded

/-- (WI₁′) **The one-loop Ward identity for every flavour** (Srednicki (68.13); memo (WI₁′);
decision D-37.2: proved, not imposed): for `e ≠ 0` and `M_f, m_γ, Λ > 0`, if flavour `f` is on
shell (G₉) and charge normalized (G₁₀) at order `e²`, then `d₁ f 0 = d₂ f 0`. This is (WI₁) at
mass `M_f`, through (E-G₂ₛ) and (E-G₂ₖ); no other flavour enters. -/
theorem d₁_eq_d₂_zero (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (he : P.e ≠ 0) (hf : 0 < Φ.mass f)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hon : IsOnShellAt P Φ D f 1)
    (hK : IsChargeNormalizedAt P Φ D f 1) :
    D.d₁ f 0 = D.d₂ f 0 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Graded.d₁_eq_d₂_zero
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
