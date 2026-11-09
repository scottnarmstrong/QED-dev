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
public import QED.Frozen.Algebra.Slash
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.Basic
import QED.WickModel.SelfEnergyExistsUnique

/-!
# Provider for `QED.WickModel.selfEnergy_existsUnique`

Proves packet 6b-1's theorem goal (Z₁) (decision D-26) as
`QED.Provider.WickModel.selfEnergy_existsUnique`, with the binder convention of decision D-13.
This module must never import the frozen anchor. The proof is
`QED.WickModel.selfEnergy_existsUnique_of_twoPoint`. It combines the reduction of the self-energy function
to its counterterm tree and loop (`QED.WickModel.onePIFunction_selfEnergy`) with the limit of
the loop (`QED.WickModel.tendsto_energyFirstIntegral_selfEnergyIntegrand`), a two-stage
integrability bound at fixed `ε`, and the independence of `p̸` and `1`.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory

namespace QED.Provider.WickModel

open QED.WickModel in
/-- Packet 6b-1's (Z₁), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem selfEnergy_existsUnique {P : Params} (hm : 0 < P.m := by assumption)
    (hmγ : 0 < P.mγ := by assumption) (hΛ : 0 < P.Λ := by assumption) :
    (∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind), ∑ t, (κ t).order ≤ 2 →
      ∀ C : Contraction 1 0 κ, IsOnePI C → (∃ f : Line C, IsLoopLine f) →
      ∀ (p : Fin 4 → ℝ) (α β : Fin 4),
        (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
          regulatedAmplitude { P with ε := ε } C ![p] ![p] ![] (Fin.cons t v) ![α] ![β] ![]) ∧
        Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
          regulatedAmplitude { P with ε := ε } C ![p] ![p] ![] (Fin.cons t v) ![α] ![β] ![]) ∧
    ∃! AB : {s : ℝ // -(P.m + min P.mγ P.Λ) ^ 2 < s} → ℂ × ℂ,
      ∀ (p : Fin 4 → ℝ) (hp : -(P.m + min P.mγ P.Λ) ^ 2 < Minkowski.dot p p) (α β : Fin 4),
        Tendsto (fun ε : ℝ => (1 / I) *
            onePIFunction { P with ε := ε } 1 0 2 ![p] ![p] ![] ![α] ![β] ![])
          (𝓝[>] 0)
          (𝓝 (((AB ⟨_, hp⟩).1 • Dirac.slash p
            + ((AB ⟨_, hp⟩).2 * P.m) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β)) :=
  QED.WickModel.selfEnergy_existsUnique_of_twoPoint P hm hmγ hΛ

end QED.Provider.WickModel

end
