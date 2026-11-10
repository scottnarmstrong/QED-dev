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
import QED.WickModel.HeadlinePair

/-!
# Provider for `QED.WickModel.existsUnique_isLSZFormFactorPair`

Proves the headline packet's theorem goal (H₀′) (decision D-33) as
`QED.Provider.WickModel.existsUnique_isLSZFormFactorPair`, with the binder convention of decision
D-13. By (L₃) an LSZ form-factor pair is a form-factor pair of the vertex function with its first
component shifted by the photon-leg coefficient, and the spinors `u_s(p)` span the on-shell solution
spaces; uniqueness then follows from (G) and (N) (`QED.WickModel.Headline.existsUnique_lszPair`).
This module must never import the frozen anchor.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open scoped ContDiff

namespace QED.Provider.WickModel

open QED.WickModel in
/-- The headline packet's (H₀′), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem existsUnique_isLSZFormFactorPair {P : Params} (he : P.e ≠ 0 := by assumption)
    (hm : 0 < P.m := by assumption) (hmγ : 0 < P.mγ := by assumption)
    (hΛ : 0 < P.Λ := by assumption) (hM₁ : P.m < P.M₁ := by assumption)
    (hM₂ : P.m < P.M₂ := by assumption) (hPV₁ : 1 + P.c₁ + P.c₂ = 0 := by assumption)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0 := by assumption)
    (hon : IsElectronOnShell P hm hmγ hΛ := by assumption) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -P.m ^ 2 := by assumption)
    (hp : Minkowski.dot p p = -P.m ^ 2 := by assumption) (hp0' : 0 < p' 0 := by assumption)
    (hp0 : 0 < p 0 := by assumption) (hq : 0 < Minkowski.dot (p' - p) (p' - p) := by assumption) :
    ∃! F : ℂ × ℂ, IsLSZFormFactorPair P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 F := by
  exact Headline.existsUnique_lszPair P he hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 hq

end QED.Provider.WickModel

end
