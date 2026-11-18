/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.IsVertexOrderFiveLimit
public import QED.Frozen.TwoLoop.A1Four
public import QED.Frozen.WickModel.IsElectronOnShell
public import QED.Frozen.WickModel.IsPhotonOnShell
public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.Frozen.OneLoop.IsFormFactorPair
import QED.TwoLoop.HeadlineAssembly
import QED.TwoLoop.UnitXXiKernel
import QED.TwoLoop.UnitSCCornerMain
import QED.TwoLoop.UnitSCCornerErr

/-!
# Provider for `QED.TwoLoop.isFormFactorPair_vertexOrderFive_pauli_limit`

Proves packet T3's theorem goal (HV₃) (decisions D-41, D-43) as
`QED.Provider.TwoLoop.isFormFactorPair_vertexOrderFive_pauli_limit`, with the binder convention of
decision D-13. The proof is the headline assembly
`QED.TwoLoop.HeadlineAssembly.pauliLimit_of_unitLimits` (VP, L, the Furry pair, the Ward identity,
the counterterms and the unit sum) applied to the two unit links proved separately: X
(`QED.TwoLoop.UnitXXi.xUnitLimit`) and S + C (`SCUnitLimit.of_one` of
`QED.TwoLoop.UnitSCCorner.scUnitLimitOne_of_corner` with `cornerMainLimit` and `cornerErrLimit`).
This module must never import the frozen anchor.
-/

@[expose] public section

open Matrix Complex Filter Topology
open QED.WickModel (Params onePIFunction₂ IsElectronOnShell IsPhotonOnShell)

namespace QED.Provider.TwoLoop

open QED.TwoLoop

/-- Packet T3's (HV₃), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem isFormFactorPair_vertexOrderFive_pauli_limit {P₀ : Params}
    (he : P₀.e ≠ 0 := by assumption) (hm : 0 < P₀.m := by assumption) {η : ℝ}
    (hη : 0 < η := by assumption) :
    ∃ RM : ℝ, ∀ (M₁ M₂ c₁ c₂ : ℝ) (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂), RM < M₁ → RM < M₂ →
      ∀ (hPV₁ : 1 + c₁ + c₂ = 0) (hPV₂ : P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0),
      ∃ δ > 0, ∃ R : ℝ, ∀ (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ), mγ < δ → R < Λ →
        (∃ d₁ d₂ dm d₃ : ℝ,
          IsElectronOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hmγ hΛ ∧
          QED.OneLoop.IsChargeNormalized P₀.e (1 + d₁) P₀.m mγ Λ hm hmγ hΛ ∧
          IsPhotonOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hM₁ hM₂ hPV₁ hPV₂) ∧
        ∀ d₁ d₂ dm d₃ : ℝ,
          IsElectronOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hmγ hΛ →
          QED.OneLoop.IsChargeNormalized P₀.e (1 + d₁) P₀.m mγ Λ hm hmγ hΛ →
          IsPhotonOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hM₁ hM₂ hPV₁ hPV₂ →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, IsVertexOrderFiveLimit
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ } p' p V) ∧
            ∀ V, IsVertexOrderFiveLimit
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ } p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖16 * (Real.pi : ℂ) ^ 4 * F.2 / (P₀.e : ℂ) ^ 4 - (a1Four : ℂ)‖ < η :=
  QED.TwoLoop.HeadlineAssembly.pauliLimit_of_unitLimits
    (QED.TwoLoop.HeadlineAssembly.SCUnitLimit.of_one
      (QED.TwoLoop.UnitSCCorner.scUnitLimitOne_of_corner QED.TwoLoop.UnitSCCorner.cornerMainLimit
        QED.TwoLoop.UnitSCCorner.cornerErrLimit))
    QED.TwoLoop.UnitXXi.xUnitLimit P₀ he hm η hη

end QED.Provider.TwoLoop

end
