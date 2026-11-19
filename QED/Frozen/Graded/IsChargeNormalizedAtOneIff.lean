-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.IsChargeNormalizedAt
public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.Provider.Graded.IsChargeNormalizedAtOneIff

@[expose] public section

open QED.WickModel (Params)

namespace QED.Graded

/-- (E-G₂ₖ) **The order-`e³` charge condition of flavour `f` is (K₀) at mass `M_f`** (memo
(E-G₂)): for `M_f, m_γ, Λ > 0`, (G₁₀) at `n = 1` holds if and only if the frozen charge condition
(K₀) holds at mass `M_f` with `Z₁ = 1 + e² d₁ f 0`. -/
theorem isChargeNormalizedAt_one_iff (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (hf : 0 < Φ.mass f)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    IsChargeNormalizedAt P Φ D f 1 ↔
      QED.OneLoop.IsChargeNormalized P.e (1 + P.e ^ 2 * D.d₁ f 0) (Φ.mass f) P.mγ P.Λ hf hmγ
        hΛ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Graded.isChargeNormalizedAt_one_iff
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
