-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.A2Four
public import QED.Provider.Lepton.A2FourMemMuon

@[expose] public section

namespace QED.Lepton

/-- (U₄) **Enclosure at the muon mass ratio** (decision D-49.3; obligation O3-M5): for every
`y` in the one-standard-uncertainty interval of `m_e/m_μ = 0.483 633 170(11) × 10⁻²` (AKN
Table 1 caption, p. 4; an input interval, so the conclusion holds for the true ratio only if it
lies in that interval), `A₂⁽⁴⁾(y) ∈ [5.197 386 × 10⁻⁷, 5.197 388 × 10⁻⁷]`. The image of the
interval is about `[5.197 386 53, 5.197 387 00] × 10⁻⁷` (numerics), against AKN Table 1
`0.519 738 676(24) × 10⁻⁶`. -/
theorem a2Four_mem_muon (y : ℝ) (hy : y ∈ Set.Icc (0.00483633159 : ℝ) 0.00483633181) :
    a2Four y ∈ Set.Icc (5.197386e-7 : ℝ) 5.197388e-7 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Lepton

end
-- FROZEN_ANCHOR_SUFFIX_END
