-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.IsVertexOrderFiveLimit
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Frozen.TwoLoop.IsVertexOrderFiveLimit
public import QED.Provider.Lepton.IsVertexOrderFiveLimitLeptonFlavorsZeroIff

@[expose] public section

open QED.WickModel (Params)

namespace QED.Lepton

/-- (E₃′) **The electron alone: the limit predicate.** With no heavy lepton, (F₁₀) is (HV₂). -/
theorem isVertexOrderFiveLimit_leptonFlavors_zero_iff (P : Params) (H : Fin 0 → HeavyLepton)
    (p' p : Fin 4 → ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    IsVertexOrderFiveLimit P (leptonFlavors P H) p' p V ↔
      QED.TwoLoop.IsVertexOrderFiveLimit P p' p V :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Lepton.isVertexOrderFiveLimit_leptonFlavors_zero_iff
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Lepton

end
-- FROZEN_ANCHOR_SUFFIX_END
