/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.VacuumPolarization
public import QED.Frozen.WickModel.VacuumPolarizationExistsUnique

/-!
# Provider for `QED.WickModel.vacuumPolarization_spec`

Proves packet 6b-2's characterization (Z₇′) (decision D-28) as
`QED.Provider.WickModel.vacuumPolarization_spec`, with the binder convention of decision D-13.
It follows directly from the existence and uniqueness of the sealed theorem (Z₂). This module
must never import the frozen anchor.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory

namespace QED.Provider.WickModel

open QED.WickModel in
/-- Packet 6b-2's (Z₇′), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem vacuumPolarization_spec {P : Params} (hm : 0 < P.m := by assumption)
    (hM₁ : P.m < P.M₁ := by assumption) (hM₂ : P.m < P.M₂ := by assumption)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0 := by assumption)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0 := by assumption) :
    (∀ (k : Fin 4 → ℝ) (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4),
      Tendsto (fun ε : ℝ => (1 / I) *
          onePIFunction { P with ε := ε } 0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν])
        (𝓝[>] 0)
        (𝓝 (vacuumPolarization P hm hM₁ hM₂ hPV₁ hPV₂ ⟨_, hk⟩ *
          ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ))))
    ∧ ∀ Pol : {s : ℝ // -(4 * P.m ^ 2) < s} → ℂ,
      (∀ (k : Fin 4 → ℝ) (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4),
        Tendsto (fun ε : ℝ => (1 / I) *
            onePIFunction { P with ε := ε } 0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν])
          (𝓝[>] 0)
          (𝓝 (Pol ⟨_, hk⟩ *
            ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ)))) →
      Pol = vacuumPolarization P hm hM₁ hM₂ hPV₁ hPV₂ := by
  have h := (QED.WickModel.vacuumPolarization_existsUnique P hm hM₁ hM₂ hPV₁ hPV₂).2
  exact ⟨h.exists.choose_spec, fun Pol hPol => h.unique hPol h.exists.choose_spec⟩

end QED.Provider.WickModel

end
