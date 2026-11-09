/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.VacuumPolarization
public import QED.Frozen.WickModel.VacuumPolarizationExistsUnique

@[expose] public section

open Complex Filter Topology MeasureTheory

namespace QED.WickModel

/-- (Z₈) **The on-shell condition for the photon** (62.11): `Π(0) = 0`, for the vacuum
polarization function (Z₇). By (62.10), the transverse part of the exact photon propagator then
has residue `P^{μν}(k)` at `k² = 0`, i.e. the factor `1/(1 - Π(0))` is `1`; this is the field
normalization needed for the LSZ formula. -/
def IsPhotonOnShell (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) :
    Prop :=
  vacuumPolarization P hm hM₁ hM₂ hPV₁ hPV₂
    ⟨0, neg_lt_zero.mpr (mul_pos four_pos (pow_pos hm 2))⟩ = 0

end QED.WickModel

end
