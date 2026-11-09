/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.IsPhotonOnShell
public import QED.Frozen.WickModel.VacuumPolarizationExistsUnique
import QED.Frozen.WickModel.VacuumPolarizationSpec
import QED.WickModel.PhotonOnShell

/-!
# Provider for `QED.WickModel.photonCounterterm_existsUnique`

Proves packet 6b-2's theorem goal (Z₉) (decision D-28) as
`QED.Provider.WickModel.photonCounterterm_existsUnique`, with the binder convention of decision
D-13. This module must never import the frozen anchor.

By the characterization (Z₇′) and `QED.WickModel.eq_vacuumPolarizationLoop_of_tendsto`, the
vacuum polarization function with counterterm `δ₃` is `-δ₃ + Π_loop`, so `Π(0) = 0` holds
exactly for `δ₃ = Π_loop(0)` (`QED.WickModel.vacuumPolarizationLoop_onShell_iff`).
-/

@[expose] public section

open Complex Filter Topology MeasureTheory

namespace QED.Provider.WickModel

open QED.WickModel in
/-- Packet 6b-2's (Z₉), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem photonCounterterm_existsUnique {P : Params} (hm : 0 < P.m := by assumption)
    (hM₁ : P.m < P.M₁ := by assumption) (hM₂ : P.m < P.M₂ := by assumption)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0 := by assumption)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0 := by assumption) :
    ∃! d : ℝ, IsPhotonOnShell { P with δ₃ := d } hm hM₁ hM₂ hPV₁ hPV₂ := by
  have key : ∀ d : ℝ, IsPhotonOnShell { P with δ₃ := d } hm hM₁ hM₂ hPV₁ hPV₂ ↔
      d = vacuumPolarizationLoop P 0 := by
    intro d
    have hPol : vacuumPolarization { P with δ₃ := d } hm hM₁ hM₂ hPV₁ hPV₂ =
        fun s => -(d : ℂ) + (vacuumPolarizationLoop P s.1 : ℂ) :=
      eq_vacuumPolarizationLoop_of_tendsto { P with δ₃ := d } hm hM₁ hM₂ hPV₁ hPV₂
        (QED.WickModel.vacuumPolarization_spec { P with δ₃ := d } hm hM₁ hM₂ hPV₁ hPV₂).1
    unfold IsPhotonOnShell
    rw [hPol]
    exact vacuumPolarizationLoop_onShell_iff P d
  exact ⟨_, (key _).2 rfl, fun d hd => (key d).1 hd⟩

end QED.Provider.WickModel

end
