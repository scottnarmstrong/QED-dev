-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.IsPhotonOnShell
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Frozen.WickModel.IsPhotonOnShell
public import QED.Provider.Lepton.IsPhotonOnShellLeptonFlavorsZeroIff

@[expose] public section

open QED.WickModel (Params)

namespace QED.Lepton

/-- (E₄) **The electron alone: the photon condition.** With no heavy lepton and T1's hypotheses
(`m > 0`, regulator fermions heavier than the electron, the Pauli–Villars conditions), the
successor photon condition (F₁₁) is T1's (Z₈). From (E₁), (E₂), (T₁₄) and the characterization
(Z₇′), at a nonzero lightlike `k`. -/
theorem isPhotonOnShell_leptonFlavors_zero_iff (P : Params) (H : Fin 0 → HeavyLepton)
    (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) :
    IsPhotonOnShell P (leptonFlavors P H) ↔
      QED.WickModel.IsPhotonOnShell P hm hM₁ hM₂ hPV₁ hPV₂ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Lepton

end
-- FROZEN_ANCHOR_SUFFIX_END
