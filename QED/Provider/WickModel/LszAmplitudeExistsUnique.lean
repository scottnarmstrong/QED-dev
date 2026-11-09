/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.ConnectedFunction
public import QED.Frozen.WickModel.RegulatedAmplitude
public import QED.Frozen.WickModel.ExternalsAttached
public import QED.Frozen.WickModel.VerticesConnected
public import QED.Frozen.WickModel.IsLoopLine
public import QED.Frozen.WickModel.IsElectronOnShell
public import QED.Frozen.Wick.VertexKindOrder
public import QED.Frozen.Algebra.Bar
public import QED.Frozen.Algebra.Spinor
public import QED.Frozen.Algebra.Dot
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Complex.Basic
import QED.WickModel.ThreePointIntegrable
import QED.WickModel.LszLimit

/-!
# Provider for `QED.WickModel.lszAmplitude_existsUnique`

Proves packet 6c-1's theorem goal (L₁) (decision D-30) as
`QED.Provider.WickModel.lszAmplitude_existsUnique`, with the binder convention of decision D-13.
This module must never import the frozen anchor.

The first conjunct, the integrability of every one-loop connected contraction, is
`QED.WickModel.integrable_connected_threePoint`. The second, the existence and uniqueness of the
iterated LSZ limit, is `QED.WickModel.existsUnique_lszLimit`: the limit is
`ū′ V^μ u + e q² D(q²) Π(q²) ū′ γ^μ u` (`QED.WickModel.lszLimit_closedForm`), from the
decomposition of the connected function into its 1PI part and the leg insertions
(`QED.WickModel.connectedFunction_threePoint_of_pos`), the off-shell vertex limit, the vanishing
of the electron-leg insertions on shell, and the continuity of the photon-leg insertion.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory

namespace QED.Provider.WickModel

open QED.WickModel in
/-- Packet 6c-1's (L₁), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem lszAmplitude_existsUnique {P : Params} (hm : 0 < P.m := by assumption)
    (hmγ : 0 < P.mγ := by assumption) (hΛ : 0 < P.Λ := by assumption)
    (hM₁ : P.m < P.M₁ := by assumption) (hM₂ : P.m < P.M₂ := by assumption)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0 := by assumption)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0 := by assumption)
    (hon : IsElectronOnShell P hm hmγ hΛ := by assumption) :
    (∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind), ∑ t, (κ t).order ≤ 3 →
      ∀ C : Contraction 1 1 κ, ExternalsAttached C → VerticesConnected C →
      (∃ f : Line C, IsLoopLine f) →
      ∀ (r' r : Fin 4 → ℝ) (α β μ : Fin 4),
        (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
          regulatedAmplitude { P with ε := ε } C ![r'] ![r] ![r' - r] (Fin.cons t v) ![α] ![β]
            ![μ]) ∧
        Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
          regulatedAmplitude { P with ε := ε } C ![r'] ![r] ![r' - r] (Fin.cons t v) ![α] ![β]
            ![μ]) ∧
    ∀ (p' p : Fin 4 → ℝ), Minkowski.dot p' p' = -P.m ^ 2 → Minkowski.dot p p = -P.m ^ 2 →
      0 < p' 0 → 0 < p 0 → ∀ (s' s : Fin 2) (μ : Fin 4),
      ∃! M : ℂ, ∀ η > 0, ∃ δ > 0, ∀ r' r : Fin 4 → ℝ,
        Minkowski.dot r' r' ≠ -P.m ^ 2 → Minkowski.dot r r ≠ -P.m ^ 2 →
        dist r' p' < δ → dist r p < δ →
        ∃ G : ℂ, Tendsto (fun ε : ℝ => (1 / I) *
            (Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ
              (Matrix.of (fun α β => connectedFunction { P with ε := ε } 1 1 3 ![r'] ![r]
                ![r' - r] ![α] ![β] ![μ]) *ᵥ Dirac.spinor P.m p s)))
          (𝓝[>] 0) (𝓝 G) ∧ ‖G - M‖ < η :=
  ⟨integrable_connected_threePoint P hm hM₁ hM₂ hPV₁ hPV₂,
    existsUnique_lszLimit P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon⟩

end QED.Provider.WickModel

end
