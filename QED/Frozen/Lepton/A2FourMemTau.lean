-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.A2Four
public import QED.Provider.Lepton.A2FourMemTau

@[expose] public section

namespace QED.Lepton

/-- (U₅) **Enclosure at the tau mass ratio** (decision D-49.3; obligation O3-M5): for every `y`
in the one-standard-uncertainty interval of `m_e/m_τ = 0.287 585(19) × 10⁻³` (AKN Table 1
caption, p. 4; an input interval), `A₂⁽⁴⁾(y) ∈ [1.8376 × 10⁻⁹, 1.8382 × 10⁻⁹]`. The image of the
interval is about `[1.837 648, 1.838 134] × 10⁻⁹` (numerics), against AKN Table 1
`0.183 790(25) × 10⁻⁸`. -/
theorem a2Four_mem_tau (y : ℝ) (hy : y ∈ Set.Icc (0.000287566 : ℝ) 0.000287604) :
    a2Four y ∈ Set.Icc (1.8376e-9 : ℝ) 1.8382e-9 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Lepton

end
-- FROZEN_ANCHOR_SUFFIX_END
