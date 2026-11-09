/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.VacuumPolarizationExistsUnique

@[expose] public section

open Complex Filter Topology MeasureTheory

namespace QED.WickModel

/-- (Z₇) **The vacuum polarization function** (decision D-25): the unique function `Π` of
`s = k²`, on the region `s > -4m²` below the pair threshold, with
`Π^{μν}(k) = Π(k²) (k² g^{μν} - k^μ k^ν)` for the `ε → 0⁺` limit of the regulated one-loop
vacuum polarization (62.4)–(62.7), (62.12), counterterm `-δ₃` included. It is chosen from the
sealed existence-and-uniqueness theorem (Z₂); its characterization is (Z₇′). -/
noncomputable def vacuumPolarization (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) :
    {s : ℝ // -(4 * P.m ^ 2) < s} → ℂ :=
  (vacuumPolarization_existsUnique P hm hM₁ hM₂ hPV₁ hPV₂).2.exists.choose

end QED.WickModel

end
