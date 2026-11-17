-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.IsElectronOnShell
public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.Provider.TwoLoop.WardIdentity

@[expose] public section

namespace QED.WickModel

/-- (WI₁) **The one-loop Ward identity `Z₁ = Z₂` at fixed regulators** (Srednicki (68.13) and
the on-shell paragraph after it, p. 405; obligation O2-15; decision D-37.2: proved, not
imposed). Let `e ≠ 0` and `m, m_γ, Λ > 0`. If the electron counterterms `δ₂, δ_m` put the
electron on shell (Z₅) and the vertex counterterm `δ₁` satisfies the charge condition (K₀) with
`Z₁ = 1 + δ₁`, then `δ₁ = δ₂`. The regulator-fermion data, `ε` and `δ₃` of `P` play no role, and
no relation between `m_γ` and `Λ` is assumed. The premise `e ≠ 0` is needed: at `e = 0` the
charge condition holds for every `Z₁`, while (Z₅) forces `δ₂ = 0`. This identity is the infrared
cancellation's input at order `e⁵` (section 5.5 of `docs/TWO-LOOP-DERIVATION.md`). -/
theorem δ₁_eq_δ₂ (P : Params) (he : P.e ≠ 0) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hon : IsElectronOnShell P hm hmγ hΛ)
    (hK : QED.OneLoop.IsChargeNormalized P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ) :
    P.δ₁ = P.δ₂ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.TwoLoop.δ₁_eq_δ₂
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.WickModel

end
-- FROZEN_ANCHOR_SUFFIX_END
