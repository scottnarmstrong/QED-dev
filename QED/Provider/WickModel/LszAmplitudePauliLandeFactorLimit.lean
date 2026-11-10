/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.IsLSZFormFactorPair
public import QED.Frozen.WickModel.LszAmplitude
public import QED.Frozen.WickModel.IsLSZChargeNormalized
public import QED.Frozen.WickModel.IsLSZResponseMagneticMoment
public import QED.Frozen.WickModel.LszSourceMagneticMoment
public import QED.Frozen.Algebra.LorentzGen
public import QED.Frozen.Algebra.Lower
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Support
import QED.WickModel.Headline

/-!
# Provider for `QED.WickModel.lszAmplitude_pauli_landeFactor_limit`

Proves the headline theorem (H) (decision D-33) as
`QED.Provider.WickModel.lszAmplitude_pauli_landeFactor_limit`, with the binder convention of
decision D-13, by combining sealed theorems (`QED.WickModel.Headline.landeFactor_limit_of_lsz`): the
counterterms exist by (K), (Z₆), (L₄′), (R) and (L₅′); the Pauli bound follows from (I), (N), (L₃)
and the spanning of the solution spaces; the response Landé factor from (R′), (L₄′) and (L₅′); and
the source Landé factor from (W₅) and the equality of the LSZ and packet-4b source moments. This
module must never import the frozen anchor.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open scoped ContDiff

namespace QED.Provider.WickModel

open QED.WickModel in
/-- The headline packet's (H), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem lszAmplitude_pauli_landeFactor_limit {P₀ : Params} (he : P₀.e ≠ 0 := by assumption)
    (hm : 0 < P₀.m := by assumption) (hM₁ : P₀.m < P₀.M₁ := by assumption)
    (hM₂ : P₀.m < P₀.M₂ := by assumption) (hPV₁ : 1 + P₀.c₁ + P₀.c₂ = 0 := by assumption)
    (hPV₂ : P₀.m ^ 2 + P₀.c₁ * P₀.M₁ ^ 2 + P₀.c₂ * P₀.M₂ ^ 2 = 0 := by assumption) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ := by assumption) (hφc : HasCompactSupport φ := by assumption)
    (hφ0 : ∃ t, 0 ≤ t ∧ φ t ≠ 0 := by assumption) {η : ℝ} (hη : 0 < η := by assumption) :
    ∃ δ > 0, ∃ R : ℝ, ∀ (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ), mγ < δ → R < Λ →
      (∃ (d₁ d₂ dm : ℝ) (hon : IsElectronOnShell
          { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm } hm hmγ hΛ),
        IsLSZChargeNormalized { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
          hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon ∧
        ∃ μ : ℝ, IsLSZResponseMagneticMoment
          { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
          hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon μ) ∧
      ∀ (d₁ d₂ dm : ℝ) (hon : IsElectronOnShell
          { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm } hm hmγ hΛ),
        IsLSZChargeNormalized { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
          hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon →
        (∀ (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P₀.m ^ 2)
            (hp : Minkowski.dot p p = -P₀.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0),
          0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < δ →
          (∃ F : ℂ × ℂ, IsLSZFormFactorPair
            { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
            hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 F) ∧
          ∀ F : ℂ × ℂ, IsLSZFormFactorPair
            { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
            hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 F →
            ‖F.2 - ((P₀.e ^ 2 / (8 * Real.pi ^ 2) : ℝ) : ℂ)‖ < η) ∧
        (∀ μ : ℝ, IsLSZResponseMagneticMoment
            { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
            hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon μ →
          |4 * P₀.m * μ / P₀.e - 2 * (1 + P₀.e ^ 2 / (8 * Real.pi ^ 2))| < η) ∧
        ∃ lam₀ > 0, ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          ‖4 * (P₀.m : ℂ) * lszSourceMagneticMoment
              { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
              hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon φ lam / P₀.e
            - 2 * (1 + P₀.e ^ 2 / (8 * Real.pi ^ 2))‖ < η := by
  exact Headline.landeFactor_limit_of_lsz P₀ he hm hM₁ hM₂ hPV₁ hPV₂ φ hφ hφc hφ0 η hη

end QED.Provider.WickModel

end
