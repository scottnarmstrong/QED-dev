-- FROZEN_ANCHOR_PREFIX_BEGIN
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
public import QED.Provider.WickModel.LszFormFactorExistsUnique

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open scoped ContDiff

namespace QED.WickModel

/-- (H₀′) **The LSZ form factors are well defined (headline packet theorem goal).** For `e ≠ 0`
and on-shell positive-energy momenta with `q² > 0`, the LSZ amplitude has exactly one form-factor
pair (H₀). -/
theorem existsUnique_isLSZFormFactorPair (P : Params) (he : P.e ≠ 0) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ)
    (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) :
    ∃! F : ℂ × ℂ, IsLSZFormFactorPair P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 F :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.WickModel.existsUnique_isLSZFormFactorPair
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.WickModel

end
-- FROZEN_ANCHOR_SUFFIX_END
