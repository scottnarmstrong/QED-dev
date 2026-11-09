-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.IsPhotonOnShell
public import QED.Frozen.WickModel.VacuumPolarizationExistsUnique
public import QED.Provider.WickModel.PhotonCountertermExistsUnique

@[expose] public section

open Complex Filter Topology MeasureTheory

namespace QED.WickModel

/-- (Z₉) **The on-shell condition fixes the photon counterterm** (packet 6b-2 theorem goal;
(62.11); decisions D-23, D-25). For `m > 0` and regulator fermions satisfying the conditions of
(Z₂), and all other parameters, there is a unique real counterterm coefficient `δ₃` for which
the photon is on shell (Z₈); the `δ₃` stored in `P` is replaced. It is the regulated analogue
of the source's (62.24). -/
theorem photonCounterterm_existsUnique (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) :
    ∃! d : ℝ, IsPhotonOnShell { P with δ₃ := d } hm hM₁ hM₂ hPV₁ hPV₂ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.WickModel.photonCounterterm_existsUnique
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.WickModel

end
-- FROZEN_ANCHOR_SUFFIX_END
