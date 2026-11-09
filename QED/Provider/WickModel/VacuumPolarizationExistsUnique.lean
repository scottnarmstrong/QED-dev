/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.OnePIFunction
public import QED.Frozen.WickModel.RegulatedAmplitude
public import QED.Frozen.WickModel.IsOnePI
public import QED.Frozen.WickModel.IsLoopLine
public import QED.Frozen.Wick.VertexKindOrder
public import QED.Frozen.Algebra.Dot
public import QED.Frozen.Algebra.Metric
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.Basic
import QED.WickModel.VacuumPolarizationExistsUnique

/-!
# Provider for `QED.WickModel.vacuumPolarization_existsUnique`

Proves packet 6b-1's theorem goal (Z₂) (decision D-26) as
`QED.Provider.WickModel.vacuumPolarization_existsUnique`, with the binder convention of decision
D-13. This module must never import the frozen anchor. The proof is
`QED.WickModel.vacuumPolarization_existsUnique_of_twoPoint`. It combines:

* the reduction of the two-photon function to its counterterm tree and regulated loop
  (`QED.WickModel.onePIFunction_vacuumPolarization`);
* Pauli–Villars bounds of second order, which give integrability for every `k`;
* dominated convergence;
* the closed form `Π(k²) = -δ₃ + (e²/2π²) ∫ x(1-x) ∑_f c_f log(M_f² + x(1-x)k²)` at `ε = 0`,
  whose non-transverse terms cancel by both Pauli–Villars conditions;
* uniqueness of limits.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory

namespace QED.Provider.WickModel

open QED.WickModel in
/-- Packet 6b-1's (Z₂), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem vacuumPolarization_existsUnique {P : Params} (hm : 0 < P.m := by assumption)
    (hM₁ : P.m < P.M₁ := by assumption) (hM₂ : P.m < P.M₂ := by assumption)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0 := by assumption)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0 := by assumption) :
    (∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind), ∑ t, (κ t).order ≤ 2 →
      ∀ C : Contraction 0 2 κ, IsOnePI C → (∃ f : Line C, IsLoopLine f) →
      ∀ (k : Fin 4 → ℝ) (μ ν : Fin 4),
        (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
          regulatedAmplitude { P with ε := ε } C ![] ![] ![k, -k] (Fin.cons t v) ![] ![] ![μ, ν]) ∧
        Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
          regulatedAmplitude { P with ε := ε } C ![] ![] ![k, -k] (Fin.cons t v) ![] ![] ![μ, ν]) ∧
    ∃! Pol : {s : ℝ // -(4 * P.m ^ 2) < s} → ℂ,
      ∀ (k : Fin 4 → ℝ) (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4),
        Tendsto (fun ε : ℝ => (1 / I) *
            onePIFunction { P with ε := ε } 0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν])
          (𝓝[>] 0)
          (𝓝 (Pol ⟨_, hk⟩ *
            ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ))) :=
  QED.WickModel.vacuumPolarization_existsUnique_of_twoPoint P hm hM₁ hM₂ hPV₁ hPV₂

end QED.Provider.WickModel

end
