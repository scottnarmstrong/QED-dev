-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.IsOnShellAt
public import QED.Frozen.WickModel.IsElectronOnShell
public import QED.Provider.Graded.IsOnShellAtOneIff

@[expose] public section

open QED.WickModel (Params)

namespace QED.Graded

/-- (E-G₂ₛ) **The order-`e²` on-shell conditions of flavour `f` are (Z₅) at mass `M_f`** (memo
(E-G₂)): for `M_f, m_γ, Λ > 0`, the flavour-`f` conditions (G₉) at `n = 1` hold if and only if the
frozen electron is on shell (Z₅) in T1's model with mass `M_f` and counterterms
`δ₂ = e² d₂ f 0`, `δ_m = e² d_m f 0`. The order-`e²` self-energy has no closed loop, so the
other flavours do not enter. -/
theorem isOnShellAt_one_iff (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (hf : 0 < Φ.mass f)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    IsOnShellAt P Φ D f 1 ↔
      WickModel.IsElectronOnShell
        { P with m := Φ.mass f, δ₂ := P.e ^ 2 * D.d₂ f 0, δm := P.e ^ 2 * D.dm f 0 }
        hf hmγ hΛ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Graded.isOnShellAt_one_iff
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
